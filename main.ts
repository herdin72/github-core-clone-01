// Entrypoint for the forge: boot the app, tell the harness where it lives,
// then wait until the harness says the run is over.
//
// The harness owns port 8080, so the forge always picks its own free port
// and reports that port back. Everything here is plain Node 22 stdlib.
import { createApp } from './app.ts';

// How long one registration attempt may hang before we give up on it.
const REGISTER_ATTEMPT_MS = 30_000;
// How long one wait-for-done request may hang before we retry it. The env
// answers /done at once, so this is only a safety net, not a long poll.
const DONE_ATTEMPT_MS = 30_000;
// Backoff between registration retries: starts small, doubles, stops growing.
const FIRST_RETRY_MS = 250;
const MAX_RETRY_MS = 2_000;

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// The harness URL comes from the environment. A trailing slash would double
// up when we append a path, so trim every trailing slash up front.
function harnessBase(): string {
  const raw = (process.env.MAKEFUN_ENV_URL ?? '').trim().replace(/\/+$/, '');
  if (raw === '') {
    console.error('error: MAKEFUN_ENV_URL is not set; nothing to register with');
    process.exit(1);
  }
  return raw;
}

// Start the forge on whatever port the OS hands us and report that port.
function startForge(): Promise<number> {
  const server = createApp();
  return new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => {
      const addr = server.address();
      if (addr === null || typeof addr === 'string') {
        server.close();
        reject(new Error('could not learn the port the forge bound to'));
        return;
      }
      console.log(`forge listening on port ${addr.port}`);
      resolve(addr.port);
    });
  });
}

// Tell the harness which port we bound. Keep trying while the harness is
// still coming up: 200 means registered, 409 means an earlier attempt
// already won, so both end the loop. 400/405 mean our request itself is
// wrong, so there is no point retrying; anything else, or a dropped
// connection, just means "try again a little later".
async function announce(base: string, port: number): Promise<void> {
  let pause = FIRST_RETRY_MS;
  for (;;) {
    let reply: Response;
    try {
      reply = await fetch(`${base}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(REGISTER_ATTEMPT_MS),
      });
    } catch (err) {
      console.error(`register attempt failed (${err instanceof Error ? err.message : String(err)}); retrying in ${pause}ms`);
      await sleep(pause);
      pause = Math.min(pause * 2, MAX_RETRY_MS);
      continue;
    }
    if (reply.status === 200 || reply.status === 409) {
      console.log(`registered with harness (HTTP ${reply.status})`);
      return;
    }
    if (reply.status === 400 || reply.status === 405) {
      throw new Error(`harness refused registration with HTTP ${reply.status}`);
    }
    console.error(`register returned HTTP ${reply.status}; retrying in ${pause}ms`);
    await sleep(pause);
    pause = Math.min(pause * 2, MAX_RETRY_MS);
  }
}

// Poll GET /done until its body says {"done": true}. The env answers at
// once with {"done": false} while the suite is still running, so a 200 on
// its own means nothing — only the body decides. A failed or malformed
// reply is not a verdict either; just wait a beat and ask again.
async function waitUntilDone(base: string): Promise<void> {
  for (;;) {
    try {
      const reply = await fetch(`${base}/done`, {
        signal: AbortSignal.timeout(DONE_ATTEMPT_MS),
      });
      if (reply.ok) {
        let body: unknown = null;
        try {
          body = await reply.json();
        } catch {
          body = null;
        }
        if (body !== null && typeof body === 'object' && (body as { done?: unknown }).done === true) {
          console.log('harness signalled done; shutting down');
          return;
        }
      } else {
        console.error(`GET /done returned HTTP ${reply.status}; polling again`);
      }
    } catch (err) {
      console.error(`GET /done failed (${err instanceof Error ? err.message : String(err)}); polling again`);
    }
    await sleep(1000);
  }
}

const base = harnessBase();
const port = await startForge();
await announce(base, port);
await waitUntilDone(base);
process.exit(0);
