// A standalone GitHub-compatible git forge: one process, stdlib only.
// Serves git smart HTTP v2/v0, REST v3, GraphQL v4 and MCP from one in-memory store.
// Original code written for the make.fun github-core-clone-01 bounty.
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

export const VIEWER_LOGIN = 'adaiversen';
export const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const FIXED_TS = '2025-01-01T00:00:00Z';
const FIXED_EPOCH = 1700000000;
const ZERO_OID = '0'.repeat(40);
const AGENT = 'forge/1.0.0';

const sha1 = (b: Buffer): string => createHash('sha1').update(b).digest('hex');
function hashObject(type: string, data: Buffer): string {
  return sha1(Buffer.concat([Buffer.from(`${type} ${data.length}\0`, 'utf8'), data]));
}
const b64 = (b: Buffer): string => b.toString('base64');
const unb64 = (s: string): Buffer => Buffer.from(s.replace(/\s+/g, ''), 'base64');
const isOid = (s: string): boolean => /^[0-9a-f]{40}$/.test(s);

// --------------------------------------------------------------- pkt-line
function pktLine(payload: Buffer | string): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const len = data.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
function pktLines(items: readonly (Buffer | string | 'flush' | 'delim')[]): Buffer {
  const parts: Buffer[] = [];
  for (const it of items) {
    if (it === 'flush') parts.push(PKT_FLUSH);
    else if (it === 'delim') parts.push(PKT_DELIM);
    else parts.push(pktLine(it));
  }
  return Buffer.concat(parts);
}
interface Pkt { kind: 'data' | 'flush' | 'delim'; payload: Buffer }
function parsePktLines(buf: Buffer): { packets: Pkt[]; rest: Buffer } {
  const packets: Pkt[] = [];
  let off = 0;
  while (off + 4 <= buf.length) {
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
    const len = parseInt(hex, 16);
    if (len === 0) { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len === 1) { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (len < 4 || off + len > buf.length) break;
    packets.push({ kind: 'data', payload: Buffer.from(buf.subarray(off + 4, off + len)) });
    off += len;
  }
  return { packets, rest: Buffer.from(buf.subarray(off)) };
}

// --------------------------------------------------------------- git objects
interface TreeEntry { mode: string; name: string; oid: string }
function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp + 1);
    out.push({ mode: data.subarray(off, sp).toString('ascii'), name: data.subarray(sp + 1, nul).toString('utf8'), oid: data.subarray(nul + 1, nul + 21).toString('hex') });
    off = nul + 21;
  }
  return out;
}
function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => Buffer.compare(Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8'), Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8')));
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string }
function parseCommit(data: Buffer): CommitView {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = ''; const parents: string[] = []; let author = ''; let committer = '';
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    const k = sp < 0 ? line : line.slice(0, sp);
    const v = sp < 0 ? '' : line.slice(sp + 1);
    if (k === 'tree') tree = v; else if (k === 'parent') parents.push(v);
    else if (k === 'author') author = v; else if (k === 'committer') committer = v;
  }
  return { tree, parents, author, committer, message };
}
function buildCommit(tree: string, parents: readonly string[], message: string, ts: number): Buffer {
  const who = `${VIEWER_NAME} <${VIEWER_EMAIL}> ${ts} +0000`;
  const lines = [`tree ${tree}`, ...parents.map((p) => `parent ${p}`), `author ${who}`, `committer ${who}`, ''];
  return Buffer.from(`${lines.join('\n')}\n${message.endsWith('\n') ? message : `${message}\n`}`, 'utf8');
}
function parseTag(data: Buffer): { object: string; type: string; tag: string } {
  const blank = data.indexOf('\n\n');
  const head = blank < 0 ? data.toString('utf8') : data.subarray(0, blank).toString('utf8');
  const m = new Map<string, string>();
  for (const line of head.split('\n')) { const sp = line.indexOf(' '); if (sp > 0) m.set(line.slice(0, sp), line.slice(sp + 1)); }
  return { object: m.get('object') ?? '', type: m.get('type') ?? '', tag: m.get('tag') ?? '' };
}

// Delta application
function readVarint(buf: Buffer, off: number): { value: number; next: number } {
  let value = buf[off] & 0x7f; let shift = 7; let i = off + 1;
  while (buf[off] & 0x80 || false) { break; }
  // git varint: first byte low 7 bits, continuation bit 0x80 on all but last
  value = buf[off] & 0x7f; shift = 7; i = off + 1;
  while (buf[i - 1] & 0x80) { value |= (buf[i] & 0x7f) << shift; shift += 7; i += 1; }
  return { value, next: i };
}
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const src = readVarint(delta, off); off = src.next;
  const tgt = readVarint(delta, off); off = tgt.next;
  if (src.value !== base.length) throw new Error('delta source size mismatch');
  const parts: Buffer[] = [];
  while (off < delta.length) {
    const op = delta[off]; off += 1;
    if (op & 0x80) {
      let cpOff = 0; let cpSize = 0;
      for (let b = 0; b < 4; b += 1) if (op & (1 << b)) { cpOff |= delta[off] << (8 * b); off += 1; }
      for (let b = 0; b < 3; b += 1) if (op & (0x10 << b)) { cpSize |= delta[off] << (8 * b); off += 1; }
      if (cpSize === 0) cpSize = 0x10000;
      parts.push(Buffer.from(base.subarray(cpOff, cpOff + cpSize)));
    } else if (op > 0) {
      parts.push(Buffer.from(delta.subarray(off, off + op))); off += op;
    } else throw new Error('delta op 0');
  }
  const out = Buffer.concat(parts);
  if (out.length !== tgt.value) throw new Error('delta target size mismatch');
  return out;
}

// Pack writing (full objects only, deterministic order)
function writePackObjectHeader(typeNum: number, size: number): Buffer {
  const out: number[] = [];
  let s = size;
  out.push(((typeNum << 4) | (s & 0x0f)) | (s > 0x0f ? 0x80 : 0));
  s >>= 4;
  while (s > 0) { out.push((s & 0x7f) | (s > 0x7f ? 0x80 : 0)); s >>= 7; }
  return Buffer.from(out);
}
const TYPE_NUM: Record<string, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const NUM_TYPE: Record<number, string> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
function writePack(objects: readonly { type: string; data: Buffer }[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 4, 'ascii'); header.writeUInt32BE(2, 4); header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const o of objects) {
    parts.push(writePackObjectHeader(TYPE_NUM[o.type] ?? 3, o.data.length));
    parts.push(deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}
// Pack parsing
interface PackObject { type: string; data: Buffer }
function parsePack(buf: Buffer, store: Map<string, PackObject>): Map<string, PackObject> {
  if (buf.length < 12 || buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const count = buf.readUInt32BE(8);
  const out = new Map<string, PackObject>();
  const byOffset = new Map<number, { oid: string; type: string; data: Buffer }>();
  let off = 12;
  for (let i = 0; i < count; i += 1) {
    const entryStart = off;
    let b = buf[off]; off += 1;
    const typeNum = (b >> 4) & 0x07;
    let size = b & 0x0f; let shift = 4;
    while (b & 0x80) { b = buf[off]; off += 1; size |= (b & 0x7f) << shift; shift += 7; }
    let baseOid = ''; let baseOff = -1;
    if (typeNum === 6) { baseOid = buf.subarray(off, off + 20).toString('hex'); off += 20; }
    else if (typeNum === 7) {
      b = buf[off]; off += 1; let o = b & 0x7f;
      while (b & 0x80) { b = buf[off]; off += 1; o = ((o + 1) << 7) | (b & 0x7f); }
      baseOff = entryStart - o;
    }
    const res = inflateSync(buf.subarray(off), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    const data = Buffer.from(res.buffer);
    off += res.engine.bytesWritten;
    let type = NUM_TYPE[typeNum] ?? '';
    let finalData = data;
    if (typeNum === 6 || typeNum === 7) {
      let base: PackObject | undefined;
      if (typeNum === 6) base = out.get(baseOid) ?? store.get(baseOid);
      else { const be = byOffset.get(baseOff); base = be ? { type: be.type, data: be.data } : undefined; }
      if (!base) throw new Error('delta base missing');
      finalData = applyDelta(base.data, data);
      type = base.type;
    }
    if (finalData.length !== size && typeNum !== 6 && typeNum !== 7) {
      // size is the inflated size; for non-delta it must match
      if (finalData.length !== size) throw new Error('object size mismatch');
    }
    const oid = hashObject(type, finalData);
    const obj = { type, data: finalData };
    out.set(oid, obj);
    byOffset.set(entryStart, { oid, type, data: finalData });
  }
  return out;
}

// --------------------------------------------------------------- store
interface IssueRec { id: number; number: number; title: string; body: string; state: 'open' | 'closed'; labels: string[]; comments: { id: number; body: string }[]; seq: number }
interface PullRec { id: number; number: number; title: string; body: string; state: 'open' | 'closed'; merged: boolean; merged_at: string | null; merge_commit_sha: string | null; head: string; base: string; headSha: string; baseSha: string; seq: number }
interface Repo {
  id: number; name: string; description: string; private: boolean; defaultBranch: string;
  objects: Map<string, PackObject>; refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  issues: Map<number, IssueRec>; pulls: Map<number, PullRec>;
  nextNum: number; commentSeq: number; commitSeq: number; objVersion: number;
  packCache: Map<string, Buffer>; commitMeta: Map<string, { message: string; ts: number }>;
}
const repos = new Map<string, Repo>();
let repoIdSeq = 0;
let reqSeq = 0;
let sessionSeq = 0;
function repoKey(owner: string, name: string): string { return `${owner}/${name}`; }
function getRepo(owner: string, name: string): Repo | null {
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}
function createRepoRecord(name: string, description: string, priv: boolean): Repo {
  const r: Repo = {
    id: ++repoIdSeq, name, description, private: priv, defaultBranch: 'main',
    objects: new Map(), refs: new Map(), labels: new Map(), issues: new Map(), pulls: new Map(),
    nextNum: 1, commentSeq: 0, commitSeq: 0, objVersion: 0, packCache: new Map(), commitMeta: new Map(),
  };
  repos.set(repoKey(VIEWER_LOGIN, name), r);
  return r;
}
function bumpRepo(r: Repo): void { r.objVersion += 1; r.packCache.clear(); }
function refTip(r: Repo, ref: string): string | null { return r.refs.get(ref) ?? null; }
function branchTip(r: Repo, branch: string): string | null { return r.refs.get(`refs/heads/${branch}`) ?? null; }
function defaultTip(r: Repo): string | null { return branchTip(r, r.defaultBranch); }

function sortedRefs(r: Repo): { name: string; oid: string }[] {
  return [...r.refs.entries()].map(([name, oid]) => ({ name, oid })).sort((a, b) => (a.name < b.name ? -1 : 1));
}
// Reachable closure. depth: max commit generations from a want (undefined = all).
// Returns included objects (oid -> object), shallow boundary oids, unshallow oids.
function collectObjects(r: Repo, wants: readonly string[], opts: { depth?: number; haves?: readonly string[]; oldShallow?: readonly string[] } = {}): { objects: Map<string, PackObject>; shallow: string[]; unshallow: string[] } {
  const depth = opts.depth;
  const included = new Map<string, PackObject>();
  const commitGen = new Map<string, number>();
  const queue: { oid: string; gen: number }[] = [];
  const addObj = (oid: string): PackObject | undefined => {
    const o = r.objects.get(oid);
    if (o && !included.has(oid)) included.set(oid, o);
    return o;
  };
  const includeTree = (treeOid: string): void => {
    const t = addObj(treeOid); if (!t) return;
    for (const e of parseTree(t.data)) {
      if (e.mode === '40000') includeTree(e.oid);
      else addObj(e.oid);
    }
  };
  const includeCommit = (oid: string, gen: number): void => {
    const c = addObj(oid); if (!c || c.type !== 'commit') return;
    const cv = parseCommit(c.data);
    includeTree(cv.tree);
    for (const p of cv.parents) {
      if (depth === undefined || gen + 1 < depth) queue.push({ oid: p, gen: gen + 1 });
    }
  };
  for (const w of wants) {
    const o = r.objects.get(w);
    if (!o) continue;
    if (o.type === 'commit') { commitGen.set(w, 0); queue.push({ oid: w, gen: 0 }); }
    else if (o.type === 'tag') {
      addObj(w);
      const tv = parseTag(o.data);
      const target = r.objects.get(tv.object);
      if (target) {
        if (target.type === 'commit') { commitGen.set(tv.object, 0); queue.push({ oid: tv.object, gen: 0 }); }
        else if (target.type === 'tag') { /* nested tag: include and follow once */ addObj(tv.object); }
        else addObj(tv.object);
      }
    } else addObj(w);
  }
  const seenCommit = new Set<string>();
  while (queue.length) {
    const item = queue.shift()!;
    if (seenCommit.has(item.oid)) continue;
    seenCommit.add(item.oid);
    includeCommit(item.oid, item.gen);
    commitGen.set(item.oid, item.gen);
  }
  // Exclusion set from haves
  const excluded = new Set<string>();
  if (opts.haves && opts.haves.length) {
    if (depth !== undefined) {
      // shallow-aware: a have contributes only itself + its tree/blobs (no parents)
      for (const h of opts.haves) {
        const o = r.objects.get(h); if (!o) continue;
        excluded.add(h);
        if (o.type === 'commit') { const cv = parseCommit(o.data); const walk = (treeOid: string): void => { excluded.add(treeOid); const t = r.objects.get(treeOid); if (!t) return; for (const e of parseTree(t.data)) { if (e.mode === '40000') walk(e.oid); else excluded.add(e.oid); } }; walk(cv.tree); }
      }
    } else {
      const full = collectObjects(r, opts.haves);
      for (const oid of full.objects.keys()) excluded.add(oid);
    }
  }
  for (const oid of excluded) included.delete(oid);
  // Shallow boundary: included commits at max depth with parents in the store not included
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== undefined) {
    for (const [oid, gen] of commitGen) {
      if (!included.has(oid)) continue;
      if (gen !== depth - 1) continue;
      const o = r.objects.get(oid); if (!o) continue;
      const cv = parseCommit(o.data);
      if (cv.parents.length && cv.parents.some((p) => r.objects.has(p) && !included.has(p))) shallow.push(oid);
      else if (cv.parents.length === 0) shallow.push(oid);
    }
    for (const old of opts.oldShallow ?? []) {
      // The old boundary commit itself is usually excluded from the pack
      // (the client already has it); what matters is whether any of its
      // parents is now included, i.e. the boundary moved past it.
      const o = r.objects.get(old); if (!o || o.type !== 'commit') continue;
      const cv = parseCommit(o.data);
      if (cv.parents.some((p) => included.has(p))) unshallow.push(old);
    }
  }
  return { objects: included, shallow, unshallow };
}
function packFor(r: Repo, objects: Map<string, PackObject>): Buffer {
  const key = [...objects.keys()].sort().join(',');
  const cached = r.packCache.get(key);
  if (cached) return cached;
  const list = [...objects.keys()].sort().map((oid) => objects.get(oid)!);
  const pack = writePack(list);
  if (r.packCache.size > 24) r.packCache.clear();
  r.packCache.set(key, pack);
  return pack;
}
// Flatten a tree to path -> {oid, mode}
function flattenTree(r: Repo, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  const t = r.objects.get(treeOid); if (!t) return;
  for (const e of parseTree(t.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flattenTree(r, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
}
function treeFromFlat(r: Repo, flat: Map<string, { oid: string; mode: string }>): string {
  // group by directory
  const build = (dir: string): string => {
    const entries: TreeEntry[] = [];
    const subdirs = new Set<string>();
    for (const [path, v] of flat) {
      const rel = dir ? (path.startsWith(`${dir}/`) ? path.slice(dir.length + 1) : null) : path;
      if (rel === null) continue;
      const slash = rel.indexOf('/');
      if (slash < 0) entries.push({ mode: v.mode, name: rel, oid: v.oid });
      else subdirs.add(rel.slice(0, slash));
    }
    for (const d of [...subdirs].sort()) entries.push({ mode: '40000', name: d, oid: build(dir ? `${dir}/${d}` : d) });
    const data = buildTree(entries);
    const oid = hashObject('tree', data);
    if (!r.objects.has(oid)) r.objects.set(oid, { type: 'tree', data });
    return oid;
  };
  return build('');
}
function storeObject(r: Repo, type: string, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!r.objects.has(oid)) r.objects.set(oid, { type, data });
  return oid;
}
function commitMetaOf(r: Repo, oid: string): { message: string; ts: number } {
  const m = r.commitMeta.get(oid);
  if (m) return m;
  const o = r.objects.get(oid);
  if (o && o.type === 'commit') {
    const cv = parseCommit(o.data);
    return { message: cv.message.replace(/\n$/, ''), ts: FIXED_EPOCH };
  }
  return { message: '', ts: FIXED_EPOCH };
}
// Create a commit on a branch from a flat-file change. Returns commit oid.
function makeCommit(r: Repo, branch: string, message: string, apply: (flat: Map<string, { oid: string; mode: string }>) => void): string {
  const tip = branchTip(r, branch);
  const flat = new Map<string, { oid: string; mode: string }>();
  if (tip) {
    const o = r.objects.get(tip);
    if (o) flattenTree(r, parseCommit(o.data).tree, '', flat);
  }
  apply(flat);
  const treeOid = treeFromFlat(r, flat);
  const ts = FIXED_EPOCH + (++r.commitSeq);
  const data = buildCommit(treeOid, tip ? [tip] : [], message, ts);
  const oid = storeObject(r, 'commit', data);
  r.commitMeta.set(oid, { message, ts });
  r.refs.set(`refs/heads/${branch}`, oid);
  bumpRepo(r);
  return oid;
}
function isAncestor(r: Repo, ancestor: string, oid: string): boolean {
  // is `ancestor` reachable from `oid` following parents?
  const seen = new Set<string>(); const stack = [oid];
  while (stack.length) {
    const cur = stack.pop()!;
    if (cur === ancestor) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const o = r.objects.get(cur);
    if (o && o.type === 'commit') stack.push(...parseCommit(o.data).parents);
  }
  return false;
}
function globalId(kind: string, ...parts: (string | number)[]): string {
  return `gid_${Buffer.from(`${kind}:${parts.join(':')}`).toString('base64')}`;
}
function decodeGlobalId(id: string): { kind: string; parts: string[] } | null {
  if (typeof id !== 'string' || !id.startsWith('gid_')) return null;
  try {
    const text = Buffer.from(id.slice(4), 'base64').toString('utf8');
    const [kind, ...parts] = text.split(':');
    if (!kind) return null;
    return { kind, parts };
  } catch { return null; }
}
function viewerUser(): Record<string, unknown> {
  return { login: VIEWER_LOGIN, id: VIEWER_ID, node_id: globalId('User', VIEWER_ID), avatar_url: `https://avatars.githubusercontent.com/u/${VIEWER_ID}?v=4`, gravatar_id: '', url: '/api/v3/users/adaiversen', html_url: 'https://github.com/adaiversen', type: 'User', site_admin: false, name: VIEWER_NAME, email: VIEWER_EMAIL };
}
function repoJson(r: Repo): Record<string, unknown> {
  return {
    id: r.id, node_id: globalId('Repository', r.id), name: r.name, full_name: `${VIEWER_LOGIN}/${r.name}`,
    owner: viewerUser(), private: r.private, html_url: `https://github.com/${VIEWER_LOGIN}/${r.name}`,
    description: r.description, fork: false, url: `/api/v3/repos/${VIEWER_LOGIN}/${r.name}`,
    created_at: FIXED_TS, updated_at: FIXED_TS, pushed_at: FIXED_TS,
    git_url: `git://github.com/${VIEWER_LOGIN}/${r.name}.git`, ssh_url: `git@github.com:${VIEWER_LOGIN}/${r.name}.git`,
    clone_url: `https://github.com/${VIEWER_LOGIN}/${r.name}.git`,
    homepage: null, size: 0, stargazers_count: 0, watchers_count: 0, language: null, has_issues: true,
    has_projects: true, has_downloads: true, has_wiki: true, has_pages: false, has_discussions: false,
    forks_count: 0, archived: false, disabled: false, open_issues_count: [...r.issues.values()].filter((i) => i.state === 'open').length,
    license: null, allow_forking: true, is_template: false, topics: [], visibility: r.private ? 'private' : 'public',
    forks: 0, open_issues: 0, watchers: 0, default_branch: r.defaultBranch,
  };
}
function issueJson(r: Repo, iss: IssueRec): Record<string, unknown> {
  return {
    id: r.id * 1000000 + iss.number, node_id: globalId('Issue', r.id, iss.number), number: iss.number,
    title: iss.title, body: iss.body, state: iss.state, user: viewerUser(),
    labels: iss.labels.map((name) => { const l = r.labels.get(name); return { id: 0, node_id: globalId('Label', r.id, name), name, color: l?.color ?? 'ededed', description: '', default: false, url: '' }; }),
    assignee: null, assignees: [], milestone: null, locked: false, comments: iss.comments.length,
    created_at: FIXED_TS, updated_at: FIXED_TS, closed_at: iss.state === 'closed' ? FIXED_TS : null,
    author_association: 'OWNER', url: `/api/v3/repos/${VIEWER_LOGIN}/${r.name}/issues/${iss.number}`,
    repository_url: `/api/v3/repos/${VIEWER_LOGIN}/${r.name}`, html_url: `https://github.com/${VIEWER_LOGIN}/${r.name}/issues/${iss.number}`,
  };
}
function pullJson(r: Repo, pr: PullRec): Record<string, unknown> {
  const headSha = pr.headSha; const baseSha = pr.baseSha;
  return {
    id: r.id * 1000000 + pr.number, node_id: globalId('PullRequest', r.id, pr.number), number: pr.number,
    title: pr.title, body: pr.body, state: pr.state, merged: pr.merged, merged_at: pr.merged_at,
    merge_commit_sha: pr.merge_commit_sha, user: viewerUser(), labels: [], assignee: null, assignees: [],
    draft: false, locked: false, comments: 0, review_comments: 0, commits: 1, additions: 1, deletions: 0, changed_files: 1,
    created_at: FIXED_TS, updated_at: FIXED_TS, closed_at: pr.state === 'closed' ? FIXED_TS : null,
    head: { label: `${VIEWER_LOGIN}:${pr.head}`, ref: pr.head, sha: headSha, user: viewerUser(), repo: repoJson(r) },
    base: { label: `${VIEWER_LOGIN}:${pr.base}`, ref: pr.base, sha: baseSha, user: viewerUser(), repo: repoJson(r) },
    url: `/api/v3/repos/${VIEWER_LOGIN}/${r.name}/pulls/${pr.number}`,
    html_url: `https://github.com/${VIEWER_LOGIN}/${r.name}/pull/${pr.number}`,
  };
}
function createIssueRec(r: Repo, title: string, body: string, labels: string[]): IssueRec {
  const number = r.nextNum; r.nextNum += 1;
  const iss: IssueRec = { id: r.id * 1000000 + number, number, title, body: body ?? '', state: 'open', labels: [...labels], comments: [], seq: number };
  r.issues.set(number, iss);
  return iss;
}
function createPullRec(r: Repo, title: string, body: string, head: string, base: string): PullRec | null {
  const headSha = branchTip(r, head); const baseSha = branchTip(r, base);
  if (!headSha || !baseSha) return null;
  const number = r.nextNum; r.nextNum += 1;
  const pr: PullRec = { id: r.id * 1000000 + number, number, title, body: body ?? '', state: 'open', merged: false, merged_at: null, merge_commit_sha: null, head, base, headSha, baseSha, seq: number };
  r.pulls.set(number, pr);
  return pr;
}
function pullFiles(r: Repo, pr: PullRec): { filename: string; status: string; additions: number; deletions: number; changes: number; path: string }[] {
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  const headFlat = new Map<string, { oid: string; mode: string }>();
  const bo = r.objects.get(pr.baseSha); const ho = r.objects.get(pr.headSha);
  if (bo) flattenTree(r, parseCommit(bo.data).tree, '', baseFlat);
  if (ho) flattenTree(r, parseCommit(ho.data).tree, '', headFlat);
  const out: { filename: string; status: string; additions: number; deletions: number; changes: number; path: string }[] = [];
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of [...paths].sort()) {
    const b = baseFlat.get(path); const h = headFlat.get(path);
    if (b && h && b.oid === h.oid) continue;
    const countLines = (oid: string | undefined): Map<string, number> => {
      const m = new Map<string, number>();
      if (!oid) return m;
      const o = r.objects.get(oid); if (!o) return m;
      for (const line of o.data.toString('utf8').split('\n')) m.set(line, (m.get(line) ?? 0) + 1);
      return m;
    };
    const bl = countLines(b?.oid); const hl = countLines(h?.oid);
    let additions = 0; let deletions = 0;
    for (const [line, n] of hl) additions += Math.max(0, n - (bl.get(line) ?? 0));
    for (const [line, n] of bl) deletions += Math.max(0, n - (hl.get(line) ?? 0));
    const status = !b ? 'added' : !h ? 'removed' : 'modified';
    out.push({ filename: path, path, status, additions, deletions, changes: additions + deletions });
  }
  return out;
}
// Returns 'ok' | 'conflict'; on ok applies the squash commit to the default branch.
function mergePull(r: Repo, pr: PullRec): 'ok' | 'conflict' {
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  const headFlat = new Map<string, { oid: string; mode: string }>();
  const curFlat = new Map<string, { oid: string; mode: string }>();
  const bo = r.objects.get(pr.baseSha); const ho = r.objects.get(pr.headSha);
  const curTip = defaultTip(r);
  if (bo) flattenTree(r, parseCommit(bo.data).tree, '', baseFlat);
  if (ho) flattenTree(r, parseCommit(ho.data).tree, '', headFlat);
  if (curTip) { const co = r.objects.get(curTip); if (co) flattenTree(r, parseCommit(co.data).tree, '', curFlat); }
  const changed = new Set<string>();
  for (const p of new Set([...baseFlat.keys(), ...headFlat.keys()])) {
    const b = baseFlat.get(p); const h = headFlat.get(p);
    if ((b?.oid ?? null) !== (h?.oid ?? null)) changed.add(p);
  }
  for (const p of changed) {
    const b = baseFlat.get(p); const h = headFlat.get(p); const c = curFlat.get(p);
    const curChanged = (c?.oid ?? null) !== (b?.oid ?? null);
    const headVal = h?.oid ?? null; const curVal = c?.oid ?? null;
    if (curChanged && curVal !== headVal) return 'conflict';
  }
  const newFlat = new Map(curFlat);
  for (const p of changed) {
    const h = headFlat.get(p);
    if (h) newFlat.set(p, h); else newFlat.delete(p);
  }
  const treeOid = treeFromFlat(r, newFlat);
  const ts = FIXED_EPOCH + (++r.commitSeq);
  const msg = `Merge pull request #${pr.number} from ${VIEWER_LOGIN}/${pr.head}\n\n${pr.title}`;
  const data = buildCommit(treeOid, curTip ? [curTip] : [], msg, ts);
  const oid = storeObject(r, 'commit', data);
  r.commitMeta.set(oid, { message: msg, ts });
  r.refs.set(`refs/heads/${r.defaultBranch}`, oid);
  bumpRepo(r);
  pr.state = 'closed'; pr.merged = true; pr.merged_at = FIXED_TS; pr.merge_commit_sha = oid;
  return 'ok';
}
function prMergeable(r: Repo, pr: PullRec): 'MERGEABLE' | 'CONFLICTING' | 'UNKNOWN' {
  if (pr.state !== 'open') return 'UNKNOWN';
  // simulate conflict check without applying
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  const headFlat = new Map<string, { oid: string; mode: string }>();
  const curFlat = new Map<string, { oid: string; mode: string }>();
  const bo = r.objects.get(pr.baseSha); const ho = r.objects.get(pr.headSha);
  const curTip = defaultTip(r);
  if (bo) flattenTree(r, parseCommit(bo.data).tree, '', baseFlat);
  if (ho) flattenTree(r, parseCommit(ho.data).tree, '', headFlat);
  if (curTip) { const co = r.objects.get(curTip); if (co) flattenTree(r, parseCommit(co.data).tree, '', curFlat); }
  for (const p of new Set([...baseFlat.keys(), ...headFlat.keys()])) {
    const b = baseFlat.get(p); const h = headFlat.get(p); const c = curFlat.get(p);
    if ((b?.oid ?? null) !== (h?.oid ?? null) && (c?.oid ?? null) !== (b?.oid ?? null) && (c?.oid ?? null) !== (h?.oid ?? null)) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

// --------------------------------------------------------------- HTTP plumbing
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (c: Buffer) => { total += c.length; if (total > 64 * 1024 * 1024) { req.destroy(); reject(new Error('body too large')); } else chunks.push(c); });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = status === 204 ? '' : `${JSON.stringify(body)}\n`;
  const headers: Record<string, string> = { 'content-type': 'application/json; charset=utf-8', 'x-github-request-id': `req-${++reqSeq}`, ...extra };
  if (status !== 204) headers['content-length'] = String(Buffer.byteLength(text));
  res.writeHead(status, headers);
  res.end(text);
}
function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': String(body.length), 'x-github-request-id': `req-${++reqSeq}` });
  res.end(body);
}
function pathOf(req: IncomingMessage): string {
  try { return new URL(req.url ?? '/', 'http://entry').pathname; } catch { return '/'; }
}
function queryOf(req: IncomingMessage): URLSearchParams {
  try { return new URL(req.url ?? '/', 'http://entry').searchParams; } catch { return new URLSearchParams(); }
}
function authOk(req: IncomingMessage): boolean {
  const expected = process.env.MAKEFUN_SHOP_TOKEN ?? '';
  const got = req.headers.authorization ?? '';
  if (!got.startsWith('Bearer ') || got.slice(7).trim() === '') return false;
  if (expected === '') return true;
  return got.slice(7) === expected;
}
function parseJsonBody(buf: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (buf.length === 0) return { ok: true, value: {} };
  try { return { ok: true, value: JSON.parse(buf.toString('utf8')) }; } catch { return { ok: false }; }
}

// --------------------------------------------------------------- git smart HTTP
const UPLOAD_CAPS_V0 = 'side-band-64k multi_ack thin-pack ofs-delta shallow symref=HEAD:refs/heads/main agent=forge/1.0.0';
const RECEIVE_CAPS_V0 = 'report-status report-status-v2 side-band-64k delete-refs ofs-delta agent=forge/1.0.0';
function v0Advertisement(r: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = service === 'git-upload-pack' ? UPLOAD_CAPS_V0 : RECEIVE_CAPS_V0;
  const refs = sortedRefs(r);
  const items: (string | 'flush')[] = [];
  const tip = defaultTip(r);
  if (refs.length === 0) {
    items.push(`# service=${service}\n`, 'flush');
    items.push(`${ZERO_OID} capabilities^{}\0${caps}\n`, 'flush');
    return pktLines(items);
  }
  items.push(`# service=${service}\n`, 'flush');
  const headOid = tip ?? ZERO_OID;
  items.push(`${headOid} HEAD\0${caps}\n`);
  for (const ref of refs) {
    items.push(`${ref.oid} ${ref.name}\n`);
    if (ref.name.startsWith('refs/tags/')) {
      const o = r.objects.get(ref.oid);
      if (o && o.type === 'tag') {
        const tv = parseTag(o.data);
        items.push(`${tv.object} ${ref.name}^{}\n`);
      }
    }
  }
  items.push('flush');
  return pktLines(items);
}
function v2Advertisement(): Buffer {
  return pktLines(['version 2\n', 'ls-refs=unborn\n', 'fetch=shallow filter\n', 'object-format=sha1\n', `agent=${AGENT}\n`, 'flush']);
}
function sidebandWrap(data: Buffer): Buffer {
  // Split pack data into sideband band-1 pkt-lines (max payload 65515 per pkt-line incl band byte)
  const parts: Buffer[] = [];
  const CHUNK = 65515;
  for (let off = 0; off < data.length; off += CHUNK) {
    const chunk = data.subarray(off, Math.min(data.length, off + CHUNK));
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (data.length === 0) parts.push(pktLine(Buffer.from([1])));
  return Buffer.concat(parts);
}
function handleGitInfoRefs(req: IncomingMessage, res: ServerResponse, owner: string, name: string, service: string): void {
  const r = getRepo(owner, name);
  if (!r || (service !== 'git-upload-pack' && service !== 'git-receive-pack')) {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  const wantV2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '') === 'version=2';
  const body = wantV2 ? v2Advertisement() : v0Advertisement(r, service as 'git-upload-pack' | 'git-receive-pack');
  const ct = service === 'git-upload-pack' ? 'application/x-git-upload-pack-advertisement' : 'application/x-git-receive-pack-advertisement';
  sendRaw(res, 200, body, ct);
}
function handleGitUploadPack(req: IncomingMessage, res: ServerResponse, r: Repo, body: Buffer): void {
  const wantV2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  const { packets } = parsePktLines(body);
  if (wantV2) {
    // command=ls-refs or command=fetch
    let command = '';
    const args: string[] = [];
    let inArgs = false;
    for (const p of packets) {
      if (p.kind === 'delim') { inArgs = true; continue; }
      if (p.kind !== 'data') continue;
      const text = p.payload.toString('utf8');
      if (!inArgs && text.startsWith('command=')) command = text.slice(8).trim();
      else if (inArgs) args.push(text);
    }
    if (command === 'ls-refs') {
      const prefixes: string[] = [];
      let peel = false; let symrefs = false;
      for (const a of args) {
        const t = a.trim();
        if (t.startsWith('ref-prefix ')) prefixes.push(t.slice(11));
        else if (t === 'peel') peel = true;
        else if (t === 'symrefs') symrefs = true;
      }
      const lines: string[] = [];
      const refs = sortedRefs(r);
      const keep = (n: string): boolean => prefixes.length === 0 || prefixes.some((p) => n.startsWith(p));
      // HEAD is a pseudo-ref: include its symref line when the client asked
      // for it (ref-prefix HEAD) or for the full listing (no prefixes).
      if (prefixes.length === 0 || prefixes.some((p) => 'HEAD'.startsWith(p) || p.startsWith('HEAD'))) {
        const tip = defaultTip(r);
        if (tip) lines.push(`${tip} HEAD symref-target:refs/heads/${r.defaultBranch}\n`);
        else lines.push(`unborn HEAD symref-target:refs/heads/${r.defaultBranch}\n`);
      }
      for (const ref of refs) {
        if (!keep(ref.name)) continue;
        let line = `${ref.oid} ${ref.name}`;
        if (peel && ref.name.startsWith('refs/tags/')) {
          const o = r.objects.get(ref.oid);
          if (o && o.type === 'tag') line += ` peeled:${parseTag(o.data).object}`;
        }
        lines.push(`${line}\n`);
      }
      sendRaw(res, 200, pktLines([...lines, 'flush']), 'application/x-git-upload-pack-result');
      return;
    }
    if (command === 'fetch') {
      const wants: string[] = []; const haves: string[] = []; const shallowIn: string[] = [];
      let depth: number | undefined;
      for (const a of args) {
        const t = a.trim();
        if (t.startsWith('want ')) wants.push(t.slice(5).trim());
        else if (t.startsWith('have ')) haves.push(t.slice(5).trim());
        else if (t.startsWith('shallow ')) shallowIn.push(t.slice(8).trim());
        else if (t.startsWith('deepen ')) depth = parseInt(t.slice(7), 10);
      }
      const { objects, shallow, unshallow } = collectObjects(r, wants, { depth, haves, oldShallow: shallowIn });
      const headParts: (string | 'delim')[] = [];
      // Protocol v2: the acknowledgments section is only present when the
      // client sent "have" lines. Real git omits it entirely for a fresh
      // clone (no haves); sending it makes git's fetch-pack expect the
      // packfile section at the wrong offset.
      if (haves.length) {
        headParts.push('acknowledgments\n');
        for (const h of haves) if (r.objects.has(h)) headParts.push(`ACK ${h}\n`);
        if (!headParts.some((p) => typeof p === 'string' && p.startsWith('ACK '))) headParts.push('NAK\n');
        // Stateless RPC: the client already finished sending haves, so the
        // server must declare itself ready or git aborts the fetch.
        headParts.push('ready\n');
        headParts.push('delim');
      }
      if (depth !== undefined) {
        headParts.push('shallow-info\n');
        for (const s of shallow) headParts.push(`shallow ${s}\n`);
        for (const s of unshallow) headParts.push(`unshallow ${s}\n`);
        headParts.push('delim');
      }
      let resp: Buffer;
      if (objects.size > 0) {
        resp = Buffer.concat([pktLines([...headParts, 'packfile\n']), sidebandWrap(packFor(r, objects)), PKT_FLUSH]);
      } else {
        resp = pktLines([...headParts, 'flush']);
      }
      sendRaw(res, 200, resp, 'application/x-git-upload-pack-result');
      return;
    }
    sendJson(res, 400, { message: 'unknown command' });
    return;
  }
  // v0 fetch
  const wants: string[] = []; const haves: string[] = []; const shallowIn: string[] = [];
  let depth: number | undefined;
  let section = 0;
  for (const p of packets) {
    if (p.kind === 'flush') { section += 1; continue; }
    if (p.kind !== 'data') continue;
    const text = p.payload.toString('utf8').trim();
    if (text.startsWith('want ')) wants.push(text.slice(5).split(' ')[0]);
    else if (text.startsWith('have ')) haves.push(text.slice(5).trim());
    else if (text.startsWith('shallow ')) shallowIn.push(text.slice(8).trim());
    else if (text.startsWith('deepen ')) depth = parseInt(text.slice(7), 10);
  }
  const { objects, shallow, unshallow } = collectObjects(r, wants, { depth, haves, oldShallow: shallowIn });
  const headParts: string[] = [];
  if (haves.length) { for (const h of haves) if (r.objects.has(h)) headParts.push(`ACK ${h}\n`); }
  else headParts.push('NAK\n');
  if (depth !== undefined) {
    for (const s of shallow) headParts.push(`shallow ${s}\n`);
    for (const s of unshallow) headParts.push(`unshallow ${s}\n`);
  }
  let resp: Buffer;
  if (objects.size > 0) resp = Buffer.concat([pktLines(headParts), sidebandWrap(packFor(r, objects)), PKT_FLUSH]);
  else resp = pktLines([...headParts, 'flush']);
  sendRaw(res, 200, resp, 'application/x-git-upload-pack-result');
}
function handleGitReceivePack(req: IncomingMessage, res: ServerResponse, r: Repo, body: Buffer): void {
  const { packets, rest } = parsePktLines(body);
  const commands: { oldOid: string; newOid: string; ref: string }[] = [];
  for (const p of packets) {
    if (p.kind !== 'data') continue;
    let text = p.payload.toString('utf8');
    const nul = text.indexOf('\0');
    if (nul >= 0) text = text.slice(0, nul);
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)\s*$/.exec(text.trim());
    if (m) commands.push({ oldOid: m[1], newOid: m[2], ref: m[3] });
  }
  let unpackOk = true; let unpackDetail = 'ok';
  let newObjects = new Map<string, PackObject>();
  if (rest.length > 0) {
    try { newObjects = parsePack(rest, r.objects); }
    catch (e) { unpackOk = false; unpackDetail = e instanceof Error ? e.message : 'unpack error'; }
  }
  const reportLines: string[] = [];
  if (unpackOk) {
    for (const [oid, obj] of newObjects) if (!r.objects.has(oid)) r.objects.set(oid, obj);
    for (const cmd of commands) {
      const cur = r.refs.get(cmd.ref) ?? null;
      let ok = true; let reason = '';
      if (cmd.newOid === ZERO_OID) {
        // delete
        if (cur === null) { ok = false; reason = 'ref does not exist'; }
        else if (cmd.oldOid !== ZERO_OID && cmd.oldOid !== cur) { ok = false; reason = 'non-fast-forward'; }
        else r.refs.delete(cmd.ref);
      } else if (cmd.oldOid === ZERO_OID) {
        if (cur !== null) { ok = false; reason = 'already exists'; }
        else if (!r.objects.has(cmd.newOid)) { ok = false; reason = 'object not found'; }
        else r.refs.set(cmd.ref, cmd.newOid);
      } else {
        if (cur !== cmd.oldOid) { ok = false; reason = 'non-fast-forward'; }
        else if (!r.objects.has(cmd.newOid)) { ok = false; reason = 'object not found'; }
        else if (!isAncestor(r, cmd.oldOid, cmd.newOid)) { ok = false; reason = 'non-fast-forward'; }
        else r.refs.set(cmd.ref, cmd.newOid);
      }
      reportLines.push(ok ? `ok ${cmd.ref}` : `ng ${cmd.ref} ${reason}`);
    }
    bumpRepo(r);
  } else {
    for (const cmd of commands) reportLines.push(`ng ${cmd.ref} unpack error`);
  }
  const inner = pktLines([`unpack ${unpackDetail}\n`, ...reportLines.map((l) => `${l}\n`), 'flush']);
  // Wrap inner pkt stream in sideband band 1. The inner flush must itself be
  // sent as band-1 data ("0000" inside a band-1 pkt-line) so the client's
  // report reader sees the terminating flush; the outer flush ends the body.
  const outer: Buffer[] = [];
  const { packets: innerPkts } = parsePktLines(inner);
  for (const p of innerPkts) {
    if (p.kind === 'flush') { outer.push(pktLine(Buffer.concat([Buffer.from([1]), Buffer.from('0000')]))); continue; }
    outer.push(pktLine(Buffer.concat([Buffer.from([1]), pktLine(p.payload)])));
  }
  outer.push(PKT_FLUSH);
  sendRaw(res, 200, Buffer.concat(outer), 'application/x-git-receive-pack-result');
}

// --------------------------------------------------------------- REST v3
function restNotFound(res: ServerResponse, what = 'Not Found'): void { sendJson(res, 404, { message: what }); }
function decodePathSeg(s: string): string { try { return decodeURIComponent(s); } catch { return s; } }

async function handleRest(req: IncomingMessage, res: ServerResponse, path: string): Promise<void> {
  const method = req.method ?? 'GET';
  const q = queryOf(req);
  const segs = path.split('/').filter((s) => s !== '').map(decodePathSeg);
  // segs[0]='api', segs[1]='v3', rest follows
  const rest = segs.slice(2);
  const scopes = { 'x-oauth-scopes': 'repo, read:org' };
  if (rest.length === 0) {
    if (method === 'GET') { sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit', repository_url: '/api/v3/repos/{owner}/{repo}' }, scopes); return; }
    restNotFound(res); return;
  }
  if (rest[0] === 'meta' && rest.length === 1) {
    if (method === 'GET') { sendJson(res, 200, { installed_version: '1.0.0', verifiable_password_authentication: false }, scopes); return; }
    restNotFound(res); return;
  }
  if (rest[0] === 'rate_limit' && rest.length === 1) {
    sendJson(res, 200, { resources: { core: { limit: 5000, remaining: 4999, reset: 1700000000 } }, rate: { limit: 5000, remaining: 4999, reset: 1700000000 } }, scopes); return;
  }
  if (!authOk(req)) { sendJson(res, 401, { message: 'Requires authentication' }, scopes); return; }
  const bodyBuf = (method === 'POST' || method === 'PATCH' || method === 'PUT' || method === 'DELETE') ? await readBody(req) : Buffer.alloc(0);
  const parsed = parseJsonBody(bodyBuf);
  if (!parsed.ok) { sendJson(res, 400, { message: 'Problems parsing JSON' }, scopes); return; }
  const body = (parsed.value ?? {}) as Record<string, unknown>;
  const bodyObj = typeof parsed.value === 'object' && parsed.value !== null && !Array.isArray(parsed.value) ? body as Record<string, unknown> : {};

  // GET /user
  if (rest[0] === 'user' && rest.length === 1) {
    if (method === 'GET') { sendJson(res, 200, viewerUser(), scopes); return; }
    restNotFound(res); return;
  }
  // /user/repos
  if (rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'GET') {
      const all = [...repos.values()].sort((a, b) => a.id - b.id);
      const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
      const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
      const slice = all.slice((page - 1) * perPage, page * perPage);
      const extra: Record<string, string> = { ...scopes };
      if (page * perPage < all.length) {
        const host = req.headers.host ?? 'localhost';
        const base = `http://${host}/api/v3/user/repos?per_page=${perPage}&page=${page + 1}`;
        extra.link = `<${base}>; rel="next"`;
      }
      sendJson(res, 200, slice.map(repoJson), extra); return;
    }
    if (method === 'POST') {
      const name = typeof bodyObj.name === 'string' ? bodyObj.name.trim() : '';
      if (!name || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$/.test(name)) { sendJson(res, 422, { message: 'Validation Failed: name is invalid' }, scopes); return; }
      if (repos.has(repoKey(VIEWER_LOGIN, name))) { sendJson(res, 422, { message: `Repository ${VIEWER_LOGIN}/${name} already exists` }, scopes); return; }
      const r = createRepoRecord(name, typeof bodyObj.description === 'string' ? bodyObj.description : '', bodyObj.private === true);
      sendJson(res, 201, repoJson(r), scopes); return;
    }
    restNotFound(res); return;
  }
  // /repos/{owner}/{repo}[...]
  if (rest[0] === 'repos' && rest.length >= 3) {
    const owner = rest[1]; const name = rest[2];
    const r = getRepo(owner, name);
    const tail = rest.slice(3);
    if (!r) { restNotFound(res); return; }
    // repo itself
    if (tail.length === 0) {
      if (method === 'GET') { sendJson(res, 200, repoJson(r), scopes); return; }
      if (method === 'PATCH') {
        if (typeof bodyObj.description === 'string') r.description = bodyObj.description;
        if (typeof bodyObj.name === 'string' && bodyObj.name !== name) {
          // rename: keep it simple, update key
          repos.delete(repoKey(owner, name));
          r.name = bodyObj.name;
          repos.set(repoKey(owner, r.name), r);
        }
        sendJson(res, 200, repoJson(r), scopes); return;
      }
      if (method === 'DELETE') { repos.delete(repoKey(owner, name)); sendJson(res, 204, null, scopes); return; }
      restNotFound(res); return;
    }
    // branches
    if (tail[0] === 'branches') {
      if (tail.length === 1 && method === 'GET') {
        const list = sortedRefs(r).filter((x) => x.name.startsWith('refs/heads/')).map((x) => ({ name: x.name.slice(11), commit: { sha: x.oid, url: '' }, protected: false }));
        sendJson(res, 200, list, scopes); return;
      }
      if (tail.length === 2 && method === 'GET') {
        const tip = branchTip(r, tail[1]);
        if (!tip) { restNotFound(res); return; }
        sendJson(res, 200, { name: tail[1], commit: { sha: tip, url: '' }, protected: false }, scopes); return;
      }
      restNotFound(res); return;
    }
    // commits
    if (tail[0] === 'commits') {
      if (method === 'GET') {
        if (tail.length === 2) {
          const o = r.objects.get(tail[1]);
          if (!o || o.type !== 'commit') { restNotFound(res); return; }
          const meta = commitMetaOf(r, tail[1]);
          sendJson(res, 200, { sha: tail[1], commit: { message: meta.message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_TS }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_TS }, tree: { sha: parseCommit(o.data).tree } }, parents: parseCommit(o.data).parents.map((p) => ({ sha: p })) }, scopes); return;
        }
        const shaParam = q.get('sha');
        let tip: string | null = null;
        if (shaParam) {
          if (r.objects.has(shaParam)) tip = shaParam;
          else tip = branchTip(r, shaParam);
        } else tip = defaultTip(r);
        const list: Record<string, unknown>[] = [];
        if (tip) {
          const seen = new Set<string>(); const stack = [tip];
          while (stack.length && list.length < 100) {
            const cur = stack.shift()!;
            if (seen.has(cur)) continue;
            seen.add(cur);
            const o = r.objects.get(cur); if (!o || o.type !== 'commit') continue;
            const cv = parseCommit(o.data); const meta = commitMetaOf(r, cur);
            list.push({ sha: cur, commit: { message: meta.message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_TS }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_TS }, tree: { sha: cv.tree } }, parents: cv.parents.map((p) => ({ sha: p })) });
            stack.push(...cv.parents);
          }
        }
        sendJson(res, 200, list, scopes); return;
      }
      restNotFound(res); return;
    }
    // git/refs
    if (tail[0] === 'git' && tail[1] === 'refs') {
      if (method === 'POST' && tail.length === 2) {
        const ref = typeof bodyObj.ref === 'string' ? bodyObj.ref : '';
        const sha = typeof bodyObj.sha === 'string' ? bodyObj.sha : '';
        if (!ref.startsWith('refs/') || !isOid(sha) || !r.objects.has(sha)) { sendJson(res, 422, { message: 'Validation Failed' }, scopes); return; }
        r.refs.set(ref, sha); bumpRepo(r);
        sendJson(res, 201, { ref, node_id: globalId('Ref', r.id, ref), url: '', object: { sha, type: 'commit', url: '' } }, scopes); return;
      }
      if (method === 'GET') {
        const refPath = tail.slice(2).join('/');
        if (refPath === '') {
          sendJson(res, 200, sortedRefs(r).map((x) => ({ ref: x.name, node_id: globalId('Ref', r.id, x.name), object: { sha: x.oid, type: 'commit' } })), scopes); return;
        }
        const full = `refs/${refPath}`;
        const oid = r.refs.get(full);
        if (!oid) { restNotFound(res); return; }
        sendJson(res, 200, { ref: full, node_id: globalId('Ref', r.id, full), object: { sha: oid, type: 'commit', url: '' } }, scopes); return;
      }
      if (method === 'DELETE' && tail.length > 2) {
        const full = `refs/${tail.slice(2).join('/')}`;
        if (!r.refs.has(full)) { restNotFound(res); return; }
        r.refs.delete(full); bumpRepo(r);
        sendJson(res, 204, null, scopes); return;
      }
      restNotFound(res); return;
    }
    // labels
    if (tail[0] === 'labels') {
      if (method === 'GET' && tail.length === 1) { sendJson(res, 200, [...r.labels.values()].map((l) => ({ name: l.name, color: l.color, description: '', default: false })), scopes); return; }
      if (method === 'POST' && tail.length === 1) {
        const lname = typeof bodyObj.name === 'string' ? bodyObj.name : '';
        if (!lname) { sendJson(res, 422, { message: 'Validation Failed' }, scopes); return; }
        const color = typeof bodyObj.color === 'string' ? bodyObj.color.replace(/^#/, '') : 'ededed';
        r.labels.set(lname, { name: lname, color });
        sendJson(res, 201, { name: lname, color, description: '', default: false }, scopes); return;
      }
      restNotFound(res); return;
    }
    // contents
    if (tail[0] === 'contents') {
      const filePath = tail.slice(1).join('/');
      if (method === 'GET') {
        const refParam = q.get('ref');
        let tip: string | null = null;
        if (refParam) tip = r.objects.has(refParam) ? refParam : branchTip(r, refParam);
        else tip = defaultTip(r);
        if (!tip) { restNotFound(res); return; }
        const flat = new Map<string, { oid: string; mode: string }>();
        const to = r.objects.get(tip); if (to) flattenTree(r, parseCommit(to.data).tree, '', flat);
        if (filePath === '') {
          const entries = dirEntries(r, flat, '');
          sendJson(res, 200, entries, scopes); return;
        }
        const entry = flat.get(filePath);
        if (entry) {
          const blob = r.objects.get(entry.oid);
          const content = blob ? blob.data : Buffer.alloc(0);
          sendJson(res, 200, { type: 'file', encoding: 'base64', size: content.length, name: filePath.split('/').pop(), path: filePath, content: b64(content), sha: entry.oid, url: '', html_url: '', download_url: null, _links: {} }, scopes); return;
        }
        // directory?
        const prefix = `${filePath}/`;
        const hasChild = [...flat.keys()].some((p) => p.startsWith(prefix));
        if (hasChild) { sendJson(res, 200, dirEntries(r, flat, filePath), scopes); return; }
        restNotFound(res); return;
      }
      if (method === 'PUT') {
        const branch = typeof bodyObj.branch === 'string' ? bodyObj.branch : r.defaultBranch;
        const contentB64 = typeof bodyObj.content === 'string' ? bodyObj.content : '';
        if (contentB64 === '') { sendJson(res, 422, { message: 'Validation Failed: content is required' }, scopes); return; }
        const contentBuf = unb64(contentB64);
        const message = typeof bodyObj.message === 'string' ? bodyObj.message : 'Update file';
        let branchTipOid = branchTip(r, branch);
        if (!branchTipOid && branch !== r.defaultBranch) {
          const dt = defaultTip(r);
          if (dt) { r.refs.set(`refs/heads/${branch}`, dt); branchTipOid = dt; }
        }
        const flat = new Map<string, { oid: string; mode: string }>();
        if (branchTipOid) { const to = r.objects.get(branchTipOid); if (to) flattenTree(r, parseCommit(to.data).tree, '', flat); }
        const existing = flat.get(filePath);
        const shaParam = typeof bodyObj.sha === 'string' ? bodyObj.sha : undefined;
        if (existing && shaParam && shaParam !== existing.oid) { sendJson(res, 409, { message: 'Conflict: sha does not match' }, scopes); return; }
        if (existing && !shaParam) { sendJson(res, 409, { message: 'Conflict: sha is required to update a file' }, scopes); return; }
        const blobOid = storeObject(r, 'blob', contentBuf);
        const commitOid = makeCommit(r, branch, message, (f) => { f.set(filePath, { oid: blobOid, mode: '100644' }); });
        sendJson(res, existing ? 200 : 201, { content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: contentBuf.length, encoding: 'base64', content: b64(contentBuf), type: 'file' }, commit: { sha: commitOid, message } }, scopes); return;
      }
      if (method === 'DELETE') {
        const branch = typeof bodyObj.branch === 'string' ? bodyObj.branch : r.defaultBranch;
        const tip = branchTip(r, branch);
        if (!tip) { restNotFound(res); return; }
        const flat = new Map<string, { oid: string; mode: string }>();
        const to = r.objects.get(tip); if (to) flattenTree(r, parseCommit(to.data).tree, '', flat);
        const existing = flat.get(filePath);
        if (!existing) { restNotFound(res); return; }
        const shaParam = typeof bodyObj.sha === 'string' ? bodyObj.sha : undefined;
        if (shaParam && shaParam !== existing.oid) { sendJson(res, 409, { message: 'Conflict: sha does not match' }, scopes); return; }
        const message = typeof bodyObj.message === 'string' ? bodyObj.message : 'Delete file';
        const commitOid = makeCommit(r, branch, message, (f) => { f.delete(filePath); });
        sendJson(res, 200, { commit: { sha: commitOid, message } }, scopes); return;
      }
      restNotFound(res); return;
    }
    // issues
    if (tail[0] === 'issues') {
      if (tail.length === 1) {
        if (method === 'GET') {
          let list = [...r.issues.values()];
          const state = q.get('state') ?? 'open';
          if (state !== 'all') list = list.filter((i) => i.state === state);
          const sort = q.get('sort') ?? 'created';
          const dir = q.get('direction') ?? (sort === 'created' ? 'desc' : 'desc');
          if (sort === 'created') list.sort((a, b) => dir === 'asc' ? a.seq - b.seq : b.seq - a.seq);
          const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
          const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
          list = list.slice((page - 1) * perPage, page * perPage);
          sendJson(res, 200, list.map((i) => issueJson(r, i)), scopes); return;
        }
        if (method === 'POST') {
          const title = typeof bodyObj.title === 'string' ? bodyObj.title : '';
          if (!title) { sendJson(res, 422, { message: 'Validation Failed: title is required' }, scopes); return; }
          const labelsRaw = bodyObj.labels;
          const labels: string[] = Array.isArray(labelsRaw) ? labelsRaw.map((x) => typeof x === 'string' ? x : (x as Record<string, unknown>).name as string).filter(Boolean) : [];
          for (const l of labels) if (!r.labels.has(l)) { sendJson(res, 422, { message: `Validation Failed: label ${l} does not exist` }, scopes); return; }
          const iss = createIssueRec(r, title, typeof bodyObj.body === 'string' ? bodyObj.body : '', labels);
          sendJson(res, 201, issueJson(r, iss), scopes); return;
        }
        restNotFound(res); return;
      }
      const num = parseInt(tail[1], 10);
      const iss = r.issues.get(num);
      if (tail.length === 2) {
        if (!iss) { restNotFound(res); return; }
        if (method === 'GET') { sendJson(res, 200, issueJson(r, iss), scopes); return; }
        if (method === 'PATCH') {
          if (typeof bodyObj.state === 'string' && (bodyObj.state === 'open' || bodyObj.state === 'closed')) iss.state = bodyObj.state;
          if (typeof bodyObj.title === 'string') iss.title = bodyObj.title;
          if (typeof bodyObj.body === 'string') iss.body = bodyObj.body;
          sendJson(res, 200, issueJson(r, iss), scopes); return;
        }
        restNotFound(res); return;
      }
      if (tail[2] === 'comments') {
        if (!iss) { restNotFound(res); return; }
        if (method === 'GET') {
          sendJson(res, 200, iss.comments.map((c) => ({ id: c.id, node_id: globalId('Comment', r.id, iss.number, c.id), body: c.body, user: viewerUser(), created_at: FIXED_TS, updated_at: FIXED_TS, url: '' })), scopes); return;
        }
        if (method === 'POST') {
          const cbody = typeof bodyObj.body === 'string' ? bodyObj.body : '';
          const id = ++r.commentSeq;
          iss.comments.push({ id, body: cbody });
          sendJson(res, 201, { id, node_id: globalId('Comment', r.id, iss.number, id), body: cbody, user: viewerUser(), created_at: FIXED_TS, updated_at: FIXED_TS, url: '' }, scopes); return;
        }
        restNotFound(res); return;
      }
      restNotFound(res); return;
    }
    // pulls
    if (tail[0] === 'pulls') {
      if (tail.length === 1) {
        if (method === 'GET') {
          let list = [...r.pulls.values()];
          const state = q.get('state') ?? 'open';
          if (state !== 'all') list = list.filter((p) => p.state === state);
          list.sort((a, b) => b.seq - a.seq);
          const perPage = Math.max(1, Math.min(100, parseInt(q.get('per_page') ?? '30', 10) || 30));
          const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
          list = list.slice((page - 1) * perPage, page * perPage);
          sendJson(res, 200, list.map((p) => pullJson(r, p)), scopes); return;
        }
        if (method === 'POST') {
          const title = typeof bodyObj.title === 'string' ? bodyObj.title : '';
          const head = typeof bodyObj.head === 'string' ? bodyObj.head : '';
          const base = typeof bodyObj.base === 'string' ? bodyObj.base : r.defaultBranch;
          if (!title || !head) { sendJson(res, 422, { message: 'Validation Failed' }, scopes); return; }
          if (!branchTip(r, head)) { sendJson(res, 422, { message: `Validation Failed: head branch ${head} does not exist` }, scopes); return; }
          if (!branchTip(r, base)) { sendJson(res, 422, { message: `Validation Failed: base branch ${base} does not exist` }, scopes); return; }
          const existing = [...r.pulls.values()].find((p) => p.state === 'open' && p.head === head && p.base === base);
          if (existing) { sendJson(res, 422, { message: 'Validation Failed: a pull request already exists for this head branch' }, scopes); return; }
          const pr = createPullRec(r, title, typeof bodyObj.body === 'string' ? bodyObj.body : '', head, base);
          if (!pr) { sendJson(res, 422, { message: 'Validation Failed' }, scopes); return; }
          sendJson(res, 201, pullJson(r, pr), scopes); return;
        }
        restNotFound(res); return;
      }
      const num = parseInt(tail[1], 10);
      const pr = r.pulls.get(num);
      if (tail.length === 2) {
        if (!pr) { restNotFound(res); return; }
        if (method === 'GET') { sendJson(res, 200, pullJson(r, pr), scopes); return; }
        if (method === 'PATCH') {
          if (typeof bodyObj.title === 'string') pr.title = bodyObj.title;
          if (typeof bodyObj.body === 'string') pr.body = bodyObj.body;
          if (typeof bodyObj.state === 'string' && bodyObj.state === 'closed') pr.state = 'closed';
          sendJson(res, 200, pullJson(r, pr), scopes); return;
        }
        restNotFound(res); return;
      }
      if (tail[2] === 'files' && method === 'GET') {
        if (!pr) { restNotFound(res); return; }
        sendJson(res, 200, pullFiles(r, pr).map((f) => ({ sha: pr.headSha, filename: f.filename, status: f.status, additions: f.additions, deletions: f.deletions, changes: f.changes, blob_url: '', raw_url: '', contents_url: '' })), scopes); return;
      }
      if (tail[2] === 'merge' && method === 'PUT') {
        if (!pr) { restNotFound(res); return; }
        if (pr.state !== 'open') { sendJson(res, 405, { message: 'Pull request is not open' }, scopes); return; }
        const result = mergePull(r, pr);
        if (result === 'conflict') { sendJson(res, 405, { message: 'Merge conflict' }, scopes); return; }
        sendJson(res, 200, { sha: pr.merge_commit_sha, merged: true, message: `Pull request #${pr.number} successfully merged` }, scopes); return;
      }
      restNotFound(res); return;
    }
    restNotFound(res); return;
  }
  restNotFound(res);
}
function dirEntries(r: Repo, flat: Map<string, { oid: string; mode: string }>, dir: string): Record<string, unknown>[] {
  const prefix = dir ? `${dir}/` : '';
  const seen = new Map<string, { type: string; oid: string; path: string }>();
  for (const [p, v] of flat) {
    if (!p.startsWith(prefix)) continue;
    const rel = p.slice(prefix.length);
    const slash = rel.indexOf('/');
    if (slash < 0) seen.set(rel, { type: 'file', oid: v.oid, path: p });
    else {
      const d = rel.slice(0, slash);
      if (!seen.has(d)) {
        // compute dir tree oid by rebuilding? use hash of name as placeholder sha must be 40 hex: use tree oid from flat via treeFromFlat on subdir
        const sub = new Map<string, { oid: string; mode: string }>();
        for (const [p2, v2] of flat) if (p2.startsWith(`${prefix}${d}/`)) sub.set(p2.slice(prefix.length + d.length + 1), v2);
        const treeOid = treeFromFlat(r, sub);
        seen.set(d, { type: 'dir', oid: treeOid, path: `${prefix}${d}` });
      }
    }
  }
  return [...seen.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([name, v]) => ({
    type: v.type, size: v.type === 'file' ? (r.objects.get(v.oid)?.data.length ?? 0) : 0,
    name, path: v.path, sha: v.oid, url: '', html_url: '', download_url: null, _links: {},
  }));
}

// --------------------------------------------------------------- GraphQL
type GqlValue = string | number | boolean | null | GqlValue[] | { [k: string]: GqlValue };
interface GqlField { alias: string | null; name: string; args: Record<string, unknown>; selections: GqlField[] | null; inlineType: string | null }
interface GqlOp { kind: 'query' | 'mutation'; name: string | null; vars: Record<string, unknown>; fields: GqlField[] }
function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (/\s/.test(c) || c === ',') { i += 1; continue; }
    if ('{}()[]:!=$@'.includes(c)) { if (c === '.' && src.slice(i, i + 3) === '...') { tokens.push('...'); i += 3; } else { tokens.push(c); i += 1; } continue; }
    if (c === '"') {
      let j = i + 1; let out = '';
      while (j < src.length && src[j] !== '"') { if (src[j] === '\\' && j + 1 < src.length) { const e = src[j + 1]; out += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e; j += 2; } else { out += src[j]; j += 1; } }
      tokens.push(JSON.stringify(out)); i = j + 1; continue;
    }
    let j = i;
    while (j < src.length && /[A-Za-z0-9_\-.]/.test(src[j])) j += 1;
    tokens.push(src.slice(i, j)); i = j;
  }
  return tokens;
}
class GqlParser {
  toks: string[]; pos = 0;
  constructor(src: string) { this.toks = gqlTokenize(src); }
  peek(): string { return this.toks[this.pos] ?? ''; }
  next(): string { return this.toks[this.pos++] ?? ''; }
  expect(t: string): void { if (this.next() !== t) throw new Error(`expected ${t}`); }
  parseValue(vars: Record<string, unknown>): unknown {
    const t = this.next();
    if (t === '$') { const name = this.next(); return { __var: name }; }
    if (t === '{') {
      const obj: Record<string, unknown> = {};
      while (this.peek() !== '}') { const k = this.next(); this.expect(':'); obj[k] = this.parseValue(vars); }
      this.expect('}'); return obj;
    }
    if (t === '[') {
      const arr: unknown[] = [];
      while (this.peek() !== ']') arr.push(this.parseValue(vars));
      this.expect(']'); return arr;
    }
    if (t.startsWith('"')) return JSON.parse(t) as string;
    if (t === 'true') return true;
    if (t === 'false') return false;
    if (t === 'null') return null;
    if (/^-?\d+$/.test(t)) return parseInt(t, 10);
    if (/^-?\d+\.\d+$/.test(t)) return parseFloat(t);
    return { __enum: t };
  }
  resolve(v: unknown, vars: Record<string, unknown>): unknown {
    if (v && typeof v === 'object') {
      if ('__var' in (v as Record<string, unknown>)) return vars[(v as Record<string, unknown>).__var as string];
      if ('__enum' in (v as Record<string, unknown>)) return (v as Record<string, unknown>).__enum;
      if (Array.isArray(v)) return v.map((x) => this.resolve(x, vars));
      const out: Record<string, unknown> = {};
      for (const [k, val] of Object.entries(v as Record<string, unknown>)) out[k] = this.resolve(val, vars);
      return out;
    }
    return v;
  }
  parseSelectionSet(vars: Record<string, unknown>): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      if (this.peek() === '...') {
        this.next();
        let inlineType: string | null = null;
        if (this.peek() === 'on') { this.next(); inlineType = this.next(); }
        else { this.next(); /* fragment name, unsupported spread: skip its selections if present */ if (this.peek() === '{') { const sub = this.parseSelectionSet(vars); fields.push(...sub); } continue; }
        const sels = this.parseSelectionSet(vars);
        for (const s of sels) fields.push({ ...s, inlineType });
        continue;
      }
      let name = this.next();
      let alias: string | null = null;
      if (this.peek() === ':') { this.next(); alias = name; name = this.next(); }
      const args: Record<string, unknown> = {};
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')') { const k = this.next(); this.expect(':'); args[k] = this.resolve(this.parseValue(vars), vars); }
        this.next();
      }
      let sels: GqlField[] | null = null;
      if (this.peek() === '{') sels = this.parseSelectionSet(vars);
      fields.push({ alias, name, args, selections: sels, inlineType: null });
    }
    this.expect('}');
    return fields;
  }
  parseDocument(vars: Record<string, unknown>): GqlOp[] {
    const ops: GqlOp[] = [];
    while (this.pos < this.toks.length) {
      let kind: 'query' | 'mutation' = 'query';
      let name: string | null = null;
      const t = this.peek();
      if (t === 'query' || t === 'mutation') { kind = this.next() as 'query' | 'mutation'; if (this.peek() !== '{' && this.peek() !== '(') name = this.next(); }
      else if (t === 'fragment') { this.next(); this.next(); if (this.peek() === 'on') { this.next(); this.next(); } this.parseSelectionSet(vars); continue; }
      // variable definitions
      if (this.peek() === '(') {
        let depth = 0;
        while (this.pos < this.toks.length) { const tk = this.next(); if (tk === '(') depth += 1; else if (tk === ')') { depth -= 1; if (depth === 0) break; } }
      }
      const fields = this.parseSelectionSet(vars);
      ops.push({ kind, name, vars, fields });
    }
    return ops;
  }
}
const SCHEMA_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest'],
  Issue: ['id', 'number', 'title', 'state', 'body'],
  PullRequest: ['id', 'number', 'title', 'state', 'merged', 'headRefName', 'baseRefName', 'mergeable', 'files'],
  User: ['login', 'id', 'name', 'email', 'avatarUrl'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo'],
  PullRequestChangedFile: ['path', 'filename', 'additions', 'deletions', 'changes', 'status'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'endCursor', 'startCursor'],
  __Type: ['kind', 'name', 'description', 'fields', 'enumValues', 'inputFields', 'interfaces', 'possibleTypes'],
  __Field: ['name', 'description', 'args', 'type'],
  __EnumValue: ['name', 'description'],
  __Schema: ['types', 'queryType', 'mutationType'],
  Branch: ['name'],
};
const SCHEMA_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'CODE', 'DISCUSSION', 'COMMIT'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
};
function validateFields(fields: GqlField[], typeName: string, errors: string[]): void {
  const known = SCHEMA_FIELDS[typeName] ?? [];
  for (const f of fields) {
    if (f.name === '__typename') continue;
    if (f.inlineType) { validateFields([{ ...f, inlineType: null }], f.inlineType, errors); continue; }
    if (!known.includes(f.name)) { errors.push(`Cannot query field "${f.name}" on type "${typeName}".`); continue; }
    const childType = childTypeOf(typeName, f.name);
    if (childType && f.selections) validateFields(f.selections, childType, errors);
  }
}
function childTypeOf(parent: string, field: string): string | null {
  const map: Record<string, Record<string, string>> = {
    Query: { viewer: 'User', repository: 'Repository', node: 'Repository', __type: '__Type', __schema: '__Schema' },
    Repository: { owner: 'User', defaultBranchRef: 'Branch', issue: 'Issue', issues: 'IssueConnection', pullRequests: 'PullRequestConnection', pullRequest: 'PullRequest' },
    IssueConnection: { nodes: 'Issue', pageInfo: 'PageInfo' },
    PullRequestConnection: { nodes: 'PullRequest', pageInfo: 'PageInfo' },
    PullRequestChangedFileConnection: { nodes: 'PullRequestChangedFile', pageInfo: 'PageInfo' },
    PullRequest: { files: 'PullRequestChangedFileConnection' },
    __Type: { fields: '__Field', enumValues: '__EnumValue' },
  };
  return map[parent]?.[field] ?? null;
}
function issueGqlState(s: string): string { return s === 'closed' ? 'CLOSED' : 'OPEN'; }
function prGqlState(p: PullRec): string { return p.merged ? 'MERGED' : p.state === 'closed' ? 'CLOSED' : 'OPEN'; }
function issueNode(r: Repo, iss: IssueRec): Record<string, unknown> {
  return { id: globalId('Issue', r.id, iss.number), number: iss.number, title: iss.title, state: issueGqlState(iss.state), body: iss.body };
}
function prNode(r: Repo, pr: PullRec): Record<string, unknown> {
  return { id: globalId('PullRequest', r.id, pr.number), number: pr.number, title: pr.title, state: prGqlState(pr), merged: pr.merged, headRefName: pr.head, baseRefName: pr.base, mergeable: prMergeable(r, pr), __repo: r, __pr: pr };
}
function repoNode(r: Repo): Record<string, unknown> {
  const tip = defaultTip(r);
  return {
    id: globalId('Repository', r.id), databaseId: r.id, name: r.name, nameWithOwner: `${VIEWER_LOGIN}/${r.name}`,
    owner: { login: VIEWER_LOGIN, id: globalId('User', VIEWER_ID), name: VIEWER_NAME, email: VIEWER_EMAIL },
    defaultBranchRef: tip ? { name: r.defaultBranch } : null, viewerPermission: 'ADMIN', hasIssuesEnabled: true,
    __repo: r,
  };
}
function cursorFor(n: number): string { return Buffer.from(`cursor:${n}`).toString('base64'); }
function cursorNum(c: unknown): number | null {
  if (typeof c !== 'string') return null;
  try { const t = Buffer.from(c, 'base64').toString('utf8'); const m = /^cursor:(\d+)$/.exec(t); return m ? parseInt(m[1], 10) : null; } catch { return null; }
}
function selectFields(obj: Record<string, unknown> | null, fields: GqlField[], typeName: string, ctx: { repo?: Repo }): Record<string, unknown> | null {
  if (obj === null || obj === undefined) return null;
  const out: Record<string, unknown> = {};
  for (const f of fields) {
    const key = f.alias ?? f.name;
    if (f.name === '__typename') { out[key] = typeName; continue; }
    if (f.inlineType && f.inlineType !== typeName && !(typeName === 'Repository' && f.inlineType === 'Repository')) {
      // inline fragment on a different type: skip unless it matches the node's type
      if (f.inlineType === 'Node') { /* fallthrough */ } else continue;
    }
    out[key] = resolveGqlField(obj, f, typeName, ctx);
  }
  return out;
}
function resolveGqlField(obj: Record<string, unknown>, f: GqlField, typeName: string, ctx: { repo?: Repo }): unknown {
  const r = (obj.__repo as Repo | undefined) ?? ctx.repo;
  if (typeName === 'Query') {
    if (f.name === 'viewer') {
      const v = { login: VIEWER_LOGIN, id: globalId('User', VIEWER_ID), name: VIEWER_NAME, email: VIEWER_EMAIL };
      return f.selections ? selectFields(v, f.selections, 'User', ctx) : v;
    }
    if (f.name === 'repository') {
      const owner = String(f.args.owner ?? ''); const name = String(f.args.name ?? '');
      const repo = getRepo(owner, name);
      if (!repo) return null;
      const node = repoNode(repo);
      return f.selections ? selectFields(node, f.selections, 'Repository', { repo }) : node;
    }
    if (f.name === 'node') {
      const dec = decodeGlobalId(String(f.args.id ?? ''));
      if (!dec) return null;
      if (dec.kind === 'Repository') {
        const repo = [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10));
        if (!repo) return null;
        const node = repoNode(repo);
        return f.selections ? selectFields(node, f.selections, 'Repository', { repo }) : node;
      }
      if (dec.kind === 'Issue') {
        const repo = [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10));
        const iss = repo?.issues.get(parseInt(dec.parts[1], 10));
        if (!repo || !iss) return null;
        const node = issueNode(repo, iss);
        return f.selections ? selectFields(node, f.selections, 'Issue', { repo }) : node;
      }
      if (dec.kind === 'PullRequest') {
        const repo = [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10));
        const pr = repo?.pulls.get(parseInt(dec.parts[1], 10));
        if (!repo || !pr) return null;
        const node = prNode(repo, pr);
        return f.selections ? selectFields(node, f.selections, 'PullRequest', { repo }) : node;
      }
      return null;
    }
    if (f.name === '__type') {
      const tname = String(f.args.name ?? '');
      const fields = SCHEMA_FIELDS[tname];
      const enums = SCHEMA_ENUMS[tname];
      if (!fields && !enums) return null;
      const node: Record<string, unknown> = { kind: enums ? 'ENUM' : 'OBJECT', name: tname, description: null, fields: fields ? fields.map((n) => ({ name: n })) : null, enumValues: enums ? enums.map((n) => ({ name: n })) : null };
      return f.selections ? selectFields(node, f.selections, '__Type', ctx) : node;
    }
    if (f.name === '__schema') {
      const node: Record<string, unknown> = { types: [], queryType: { name: 'Query' }, mutationType: { name: 'Mutation' } };
      return f.selections ? selectFields(node, f.selections, '__Schema', ctx) : node;
    }
    return null;
  }
  if (typeName === 'Repository' && r) {
    if (f.name === 'issue') {
      const iss = r.issues.get(Number(f.args.number));
      if (!iss) return null;
      const node = issueNode(r, iss);
      return f.selections ? selectFields(node, f.selections, 'Issue', { repo: r }) : node;
    }
    if (f.name === 'issues') {
      let list = [...r.issues.values()];
      const states = f.args.states as string[] | undefined;
      if (states && states.length) list = list.filter((i) => states.includes(issueGqlState(i.state)));
      const orderBy = f.args.orderBy as Record<string, unknown> | undefined;
      if (orderBy) {
        const dir = String(orderBy.direction ?? 'ASC');
        list.sort((a, b) => dir === 'DESC' ? b.seq - a.seq : a.seq - b.seq);
      } else list.sort((a, b) => a.seq - b.seq);
      const after = cursorNum(f.args.after);
      if (after !== null) list = list.filter((i) => i.number > after);
      const first = typeof f.args.first === 'number' ? f.args.first : list.length;
      const page = list.slice(0, first);
      const conn: Record<string, unknown> = {
        nodes: page.map((i) => issueNode(r, i)),
        pageInfo: { hasNextPage: list.length > first, hasPreviousPage: false, endCursor: page.length ? cursorFor(page[page.length - 1].number) : null, startCursor: page.length ? cursorFor(page[0].number) : null },
        totalCount: list.length,
      };
      if (!f.selections) return conn;
      const out: Record<string, unknown> = {};
      for (const sf of f.selections) {
        if (sf.name === 'nodes') out[sf.alias ?? 'nodes'] = (conn.nodes as Record<string, unknown>[]).map((n) => sf.selections ? selectFields(n, sf.selections, 'Issue', { repo: r }) : n);
        else if (sf.name === 'pageInfo') out[sf.alias ?? 'pageInfo'] = sf.selections ? selectFields(conn.pageInfo as Record<string, unknown>, sf.selections, 'PageInfo', ctx) : conn.pageInfo;
        else out[sf.alias ?? sf.name] = conn[sf.name];
      }
      return out;
    }
    if (f.name === 'pullRequests') {
      let list = [...r.pulls.values()];
      const states = f.args.states as string[] | undefined;
      if (states && states.length) list = list.filter((p) => states.includes(prGqlState(p)));
      list.sort((a, b) => b.seq - a.seq);
      const first = typeof f.args.first === 'number' ? f.args.first : list.length;
      const page = list.slice(0, first);
      const conn: Record<string, unknown> = { nodes: page.map((p) => prNode(r, p)), pageInfo: { hasNextPage: list.length > first, hasPreviousPage: false, endCursor: null, startCursor: null }, totalCount: list.length };
      if (!f.selections) return conn;
      const out: Record<string, unknown> = {};
      for (const sf of f.selections) {
        if (sf.name === 'nodes') out[sf.alias ?? 'nodes'] = (conn.nodes as Record<string, unknown>[]).map((n) => sf.selections ? selectFields(n, sf.selections, 'PullRequest', { repo: r }) : n);
        else if (sf.name === 'pageInfo') out[sf.alias ?? 'pageInfo'] = sf.selections ? selectFields(conn.pageInfo as Record<string, unknown>, sf.selections, 'PageInfo', ctx) : conn.pageInfo;
        else out[sf.alias ?? sf.name] = conn[sf.name];
      }
      return out;
    }
    if (f.name === 'pullRequest') {
      const pr = r.pulls.get(Number(f.args.number));
      if (!pr) return null;
      const node = prNode(r, pr);
      return f.selections ? selectFields(node, f.selections, 'PullRequest', { repo: r }) : node;
    }
  }
  if (typeName === 'PullRequest' && r) {
    if (f.name === 'files') {
      const pr = obj.__pr as PullRec;
      const files = pullFiles(r, pr);
      const first = typeof f.args.first === 'number' ? f.args.first : files.length;
      const page = files.slice(0, first);
      const conn: Record<string, unknown> = { nodes: page.map((x) => ({ path: x.filename, filename: x.filename, additions: x.additions, deletions: x.deletions, changes: x.changes, status: x.status })), pageInfo: { hasNextPage: files.length > first, hasPreviousPage: false, endCursor: null, startCursor: null } };
      if (!f.selections) return conn;
      const out: Record<string, unknown> = {};
      for (const sf of f.selections) {
        if (sf.name === 'nodes') out[sf.alias ?? 'nodes'] = (conn.nodes as Record<string, unknown>[]).map((n) => sf.selections ? selectFields(n, sf.selections, 'PullRequestChangedFile', ctx) : n);
        else if (sf.name === 'pageInfo') out[sf.alias ?? 'pageInfo'] = sf.selections ? selectFields(conn.pageInfo as Record<string, unknown>, sf.selections, 'PageInfo', ctx) : conn.pageInfo;
        else out[sf.alias ?? sf.name] = conn[sf.name];
      }
      return out;
    }
  }
  if (typeName === '__Type') {
    if (f.name === 'fields') {
      const arr = (obj.fields as { name: string }[] | null) ?? [];
      if (!f.selections) return arr;
      return arr.map((x) => selectFields(x, f.selections, '__Field', ctx));
    }
    if (f.name === 'enumValues') {
      const arr = (obj.enumValues as { name: string }[] | null) ?? [];
      if (!f.selections) return arr;
      return arr.map((x) => selectFields(x, f.selections, '__EnumValue', ctx));
    }
  }
  // plain property
  const val = obj[f.name];
  if (val !== undefined && f.selections && val && typeof val === 'object' && !Array.isArray(val)) {
    const child = childTypeOf(typeName, f.name);
    return selectFields(val as Record<string, unknown>, f.selections, child ?? typeName, ctx);
  }
  return val ?? null;
}
function executeGql(op: GqlOp, vars: Record<string, unknown>): { data: Record<string, unknown> | null; errors?: { message: string }[] } {
  const errors: string[] = [];
  if (op.kind === 'query') validateFields(op.fields, 'Query', errors);
  else validateFields(op.fields, 'Mutation', errors);
  if (errors.length) return { data: { viewer: null }, errors: errors.map((m) => ({ message: m })) };
  const data: Record<string, unknown> = {};
  const rootObj: Record<string, unknown> = {};
  if (op.kind === 'mutation') {
    for (const f of op.fields) {
      const key = f.alias ?? f.name;
      try { data[key] = executeMutation(f); } catch (e) { return { data, errors: [{ message: e instanceof Error ? e.message : String(e) }] }; }
    }
    return { data };
  }
  for (const f of op.fields) {
    const key = f.alias ?? f.name;
    data[key] = resolveGqlField(rootObj, f, 'Query', {});
  }
  return { data };
}
function executeMutation(f: GqlField): unknown {
  const input = (f.args.input ?? {}) as Record<string, unknown>;
  if (f.name === 'createIssue') {
    const dec = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = dec && dec.kind === 'Repository' ? [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10)) : undefined;
    if (!repo) throw new Error('repository not found');
    const iss = createIssueRec(repo, String(input.title ?? ''), typeof input.body === 'string' ? input.body : '', []);
    const node = issueNode(repo, iss);
    const out = f.selections ? selectFields({ issue: node }, f.selections, 'Mutation', { repo }) : { issue: node };
    // selectFields on wrapper: handle 'issue' sub-selection manually
    if (f.selections) {
      const res: Record<string, unknown> = {};
      for (const sf of f.selections) {
        if (sf.name === 'issue') res[sf.alias ?? 'issue'] = sf.selections ? selectFields(node, sf.selections, 'Issue', { repo }) : node;
        else res[sf.alias ?? sf.name] = null;
      }
      return res;
    }
    return out;
  }
  if (f.name === 'closeIssue') {
    const dec = decodeGlobalId(String(input.issueId ?? ''));
    const repo = dec && dec.kind === 'Issue' ? [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10)) : undefined;
    const iss = repo?.issues.get(parseInt(dec?.parts[1] ?? '0', 10));
    if (!repo || !iss) throw new Error('issue not found');
    iss.state = 'closed';
    const node = issueNode(repo, iss);
    if (f.selections) {
      const res: Record<string, unknown> = {};
      for (const sf of f.selections) if (sf.name === 'issue') res[sf.alias ?? 'issue'] = sf.selections ? selectFields(node, sf.selections, 'Issue', { repo }) : node;
      return res;
    }
    return { issue: node };
  }
  if (f.name === 'createPullRequest') {
    const dec = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = dec && dec.kind === 'Repository' ? [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10)) : undefined;
    if (!repo) throw new Error('repository not found');
    const head = String(input.headRefName ?? ''); const base = String(input.baseRefName ?? repo.defaultBranch);
    let pr = [...repo.pulls.values()].find((p) => p.state === 'open' && p.head === head && p.base === base);
    if (!pr) {
      pr = createPullRec(repo, String(input.title ?? ''), typeof input.body === 'string' ? input.body : '', head, base);
      if (!pr) throw new Error('head or base branch not found');
    }
    const node = prNode(repo, pr);
    if (f.selections) {
      const res: Record<string, unknown> = {};
      for (const sf of f.selections) if (sf.name === 'pullRequest') res[sf.alias ?? 'pullRequest'] = sf.selections ? selectFields(node, sf.selections, 'PullRequest', { repo }) : node;
      return res;
    }
    return { pullRequest: node };
  }
  if (f.name === 'mergePullRequest') {
    const dec = decodeGlobalId(String(input.pullRequestId ?? ''));
    const repo = dec && dec.kind === 'PullRequest' ? [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10)) : undefined;
    const pr = repo?.pulls.get(parseInt(dec?.parts[1] ?? '0', 10));
    if (!repo || !pr) throw new Error('pull request not found');
    if (pr.state === 'open') mergePull(repo, pr);
    const node = prNode(repo, pr);
    if (f.selections) {
      const res: Record<string, unknown> = {};
      for (const sf of f.selections) if (sf.name === 'pullRequest') res[sf.alias ?? 'pullRequest'] = sf.selections ? selectFields(node, sf.selections, 'PullRequest', { repo }) : node;
      return res;
    }
    return { pullRequest: node };
  }
  if (f.name === 'addComment') {
    const dec = decodeGlobalId(String(input.subjectId ?? ''));
    const repo = dec && dec.kind === 'Issue' ? [...repos.values()].find((x) => x.id === parseInt(dec.parts[0], 10)) : undefined;
    const iss = repo?.issues.get(parseInt(dec?.parts[1] ?? '0', 10));
    if (!repo || !iss) throw new Error('issue not found');
    const id = ++repo.commentSeq;
    const body = String(input.body ?? '');
    iss.comments.push({ id, body });
    const node = { id: globalId('Comment', repo.id, iss.number, id), body };
    if (f.selections) {
      const res: Record<string, unknown> = {};
      for (const sf of f.selections) {
        if (sf.name === 'commentEdge') {
          const edge: Record<string, unknown> = {};
          if (sf.selections) for (const s2 of sf.selections) if (s2.name === 'node') edge[s2.alias ?? 'node'] = s2.selections ? selectFields(node, s2.selections, 'Comment', { repo }) : node;
          res[sf.alias ?? 'commentEdge'] = edge;
        }
      }
      return res;
    }
    return { commentEdge: { node } };
  }
  throw new Error(`unknown mutation ${f.name}`);
}
async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authOk(req)) { sendJson(res, 401, { message: 'Requires authentication' }); return; }
  const buf = await readBody(req);
  const parsed = parseJsonBody(buf);
  if (!parsed.ok) { sendJson(res, 400, { message: 'Problems parsing JSON' }); return; }
  const runOne = (doc: unknown): Record<string, unknown> => {
    if (!doc || typeof doc !== 'object') return { data: null, errors: [{ message: 'invalid request' }] };
    const d = doc as Record<string, unknown>;
    const query = typeof d.query === 'string' ? d.query : '';
    const vars = (d.variables ?? {}) as Record<string, unknown>;
    try {
      const parser = new GqlParser(query);
      const ops = parser.parseDocument(vars);
      if (ops.length === 0) return { data: null, errors: [{ message: 'no operation' }] };
      const op = ops[0];
      return executeGql(op, vars);
    } catch (e) {
      return { data: null, errors: [{ message: e instanceof Error ? e.message : String(e) }] };
    }
  };
  if (Array.isArray(parsed.value)) {
    sendJson(res, 200, parsed.value.map(runOne));
  } else {
    sendJson(res, 200, runOne(parsed.value));
  }
}

// --------------------------------------------------------------- MCP
const MCP_PROTOCOL = '2026-07-28';
const MCP_TOOLS: { name: string; description: string; inputSchema: { type: string; properties: Record<string, unknown>; required: string[] } }[] = [
  { name: 'create_repo', description: 'Create a repository for the viewer', inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' } }, required: ['name'] } },
  { name: 'get_repo', description: 'Get a repository by owner and name', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' } }, required: ['owner', 'repo'] } },
  { name: 'create_issue', description: 'Create an issue in a repository', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title'] } },
  { name: 'list_issues', description: 'List issues in a repository', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, state: { type: 'string', description: 'open, closed, or all' } }, required: ['owner', 'repo'] } },
  { name: 'create_pull_request', description: 'Create a pull request', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title', 'head', 'base'] } },
  { name: 'merge_pull_request', description: 'Merge a pull request with squash', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, pull_number: { type: 'number', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] } },
];
function mcpResult(id: unknown, result: unknown): Record<string, unknown> { return { jsonrpc: '2.0', id: id ?? null, result }; }
function mcpError(id: unknown, code: number, message: string): Record<string, unknown> { return { jsonrpc: '2.0', id: id ?? null, error: { code, message } }; }
function pickArg(args: Record<string, unknown>, names: string[]): unknown {
  for (const n of names) if (args[n] !== undefined && args[n] !== null) return args[n];
  return undefined;
}
function callMcpTool(name: string, args: Record<string, unknown>): { content: { type: string; text: string }[]; isError?: boolean } {
  const err = (msg: string): { content: { type: string; text: string }[]; isError: boolean } => ({ content: [{ type: 'text', text: msg }], isError: true });
  const ok = (v: unknown): { content: { type: string; text: string }[] } => ({ content: [{ type: 'text', text: JSON.stringify(v) }] });
  const lname = name.toLowerCase();
  const base = lname.includes('create_repo') ? 'create_repo' : lname.includes('get_repo') ? 'get_repo' : lname.includes('create_issue') ? 'create_issue' : lname.includes('list_issues') ? 'list_issues' : lname.includes('create_pull_request') ? 'create_pull_request' : lname.includes('merge_pull_request') ? 'merge_pull_request' : null;
  if (!base) return err(`unknown tool: ${name}`);
  if (base === 'create_repo') {
    const rname = pickArg(args, ['name', 'repo_name']);
    if (typeof rname !== 'string' || !rname) return err('missing required argument: name');
    if (repos.has(repoKey(VIEWER_LOGIN, rname))) return err(`Repository ${VIEWER_LOGIN}/${rname} already exists`);
    const r = createRepoRecord(rname, typeof args.description === 'string' ? args.description : '', args.private === true);
    return ok(repoJson(r));
  }
  if (base === 'get_repo') {
    const owner = String(pickArg(args, ['owner', 'owner_login']) ?? '');
    const repoName = String(pickArg(args, ['repo', 'repo_name', 'name']) ?? '');
    const full = String(pickArg(args, ['full_name']) ?? '');
    let r: Repo | null = null;
    if (full) { const [o, n] = full.split('/'); r = getRepo(o ?? '', n ?? ''); }
    else r = getRepo(owner, repoName);
    if (!r) return err(`repository not found: ${owner}/${repoName}`);
    return ok(repoJson(r));
  }
  if (base === 'create_issue') {
    const owner = String(pickArg(args, ['owner', 'owner_login']) ?? '');
    const repoName = String(pickArg(args, ['repo', 'repo_name']) ?? '');
    const full = String(pickArg(args, ['full_name']) ?? '');
    let r: Repo | null = null;
    if (full) { const [o, n] = full.split('/'); r = getRepo(o ?? '', n ?? ''); }
    else r = getRepo(owner, repoName);
    if (!r) return err('repository not found');
    const title = pickArg(args, ['title']);
    if (typeof title !== 'string' || !title) return err('missing required argument: title');
    const iss = createIssueRec(r, title, typeof args.body === 'string' ? args.body : '', []);
    return ok(issueJson(r, iss));
  }
  if (base === 'list_issues') {
    const owner = String(pickArg(args, ['owner', 'owner_login']) ?? '');
    const repoName = String(pickArg(args, ['repo', 'repo_name']) ?? '');
    const full = String(pickArg(args, ['full_name']) ?? '');
    let r: Repo | null = null;
    if (full) { const [o, n] = full.split('/'); r = getRepo(o ?? '', n ?? ''); }
    else r = getRepo(owner, repoName);
    if (!r) return err('repository not found');
    const state = typeof args.state === 'string' ? args.state : 'open';
    let list = [...r.issues.values()];
    if (state !== 'all') list = list.filter((i) => i.state === state);
    list.sort((a, b) => b.seq - a.seq);
    return ok(list.map((i) => issueJson(r, i)));
  }
  if (base === 'create_pull_request') {
    const owner = String(pickArg(args, ['owner', 'owner_login']) ?? '');
    const repoName = String(pickArg(args, ['repo', 'repo_name']) ?? '');
    const full = String(pickArg(args, ['full_name']) ?? '');
    let r: Repo | null = null;
    if (full) { const [o, n] = full.split('/'); r = getRepo(o ?? '', n ?? ''); }
    else r = getRepo(owner, repoName);
    if (!r) return err('repository not found');
    const title = pickArg(args, ['title']);
    const head = String(pickArg(args, ['head', 'head_ref', 'headRefName']) ?? '');
    const baseRef = String(pickArg(args, ['base', 'base_ref', 'baseRefName']) ?? r.defaultBranch);
    if (typeof title !== 'string' || !title) return err('missing required argument: title');
    if (!head) return err('missing required argument: head');
    const pr = createPullRec(r, title, typeof args.body === 'string' ? args.body : '', head, baseRef);
    if (!pr) return err('head or base branch not found');
    return ok(pullJson(r, pr));
  }
  if (base === 'merge_pull_request') {
    const owner = String(pickArg(args, ['owner', 'owner_login']) ?? '');
    const repoName = String(pickArg(args, ['repo', 'repo_name']) ?? '');
    const full = String(pickArg(args, ['full_name']) ?? '');
    let r: Repo | null = null;
    if (full) { const [o, n] = full.split('/'); r = getRepo(o ?? '', n ?? ''); }
    else r = getRepo(owner, repoName);
    if (!r) return err('repository not found');
    const num = Number(pickArg(args, ['pull_number', 'number', 'pullRequestNumber']));
    if (!Number.isFinite(num)) return err('missing required argument: pull_number');
    const pr = r.pulls.get(num);
    if (!pr) return err('pull request not found');
    if (pr.state !== 'open') return err('pull request is not open');
    const result = mergePull(r, pr);
    if (result === 'conflict') return err('Merge conflict');
    return ok({ sha: pr.merge_commit_sha, merged: true, message: `Pull request #${num} successfully merged` });
  }
  return err(`unknown tool: ${name}`);
}
async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authOk(req)) { sendJson(res, 401, { message: 'Requires authentication' }); return; }
  const buf = await readBody(req);
  let doc: unknown;
  try { doc = JSON.parse(buf.toString('utf8')); } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  if (!doc || typeof doc !== 'object' || Array.isArray(doc)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32600, message: 'Invalid Request' } });
    return;
  }
  const d = doc as Record<string, unknown>;
  const id = d.id ?? null;
  const method = String(d.method ?? '');
  if (method === 'server/discover') {
    sendJson(res, 200, mcpResult(id, {
      protocolVersion: MCP_PROTOCOL,
      supportedVersions: [MCP_PROTOCOL, '2025-11-25', '2025-06-18'],
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
    }));
    return;
  }
  if (method === 'initialize') {
    sendJson(res, 200, mcpResult(id, {
      protocolVersion: MCP_PROTOCOL,
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
    }));
    return;
  }
  if (method === 'notifications/initialized' || method.startsWith('notifications/')) {
    res.writeHead(202, { 'mcp-session-id': `sess-${++sessionSeq}` });
    res.end();
    return;
  }
  if (method === 'ping') { sendJson(res, 200, mcpResult(id, {})); return; }
  if (method === 'tools/list') {
    sendJson(res, 200, mcpResult(id, { tools: MCP_TOOLS }));
    return;
  }
  if (method === 'tools/call') {
    const params = (d.params ?? {}) as Record<string, unknown>;
    const tname = String(params.name ?? '');
    const args = (params.arguments ?? {}) as Record<string, unknown>;
    const out = callMcpTool(tname, args);
    // unknown tool -> -32601
    const known = MCP_TOOLS.some((t) => t.name === tname) || ['create_repo', 'get_repo', 'create_issue', 'list_issues', 'create_pull_request', 'merge_pull_request'].some((k) => tname.toLowerCase().includes(k));
    if (!known) { sendJson(res, 200, mcpError(id, -32601, `Method not found: ${tname}`)); return; }
    sendJson(res, 200, mcpResult(id, out));
    return;
  }
  sendJson(res, 200, mcpError(id, -32601, `Method not found: ${method}`));
}

// --------------------------------------------------------------- createApp / router
export function createApp() {
  const server = createServer(async (req, res) => {
    try {
      const path = pathOf(req);
      const method = req.method ?? 'GET';
      if (path === '/healthz' && method === 'GET') { sendJson(res, 200, { ok: true }); return; }
      if (path === '/api/graphql' && method === 'POST') { await handleGraphQL(req, res); return; }
      if (path === '/mcp' && method === 'POST') { await handleMcp(req, res); return; }
      if (path.startsWith('/api/v3')) { await handleRest(req, res, path); return; }
      const gm = /^\/([^/]+)\/([^/]+)\.git\/(.*)$/.exec(path);
      if (gm) {
        const owner = decodePathSeg(gm[1]); const name = decodePathSeg(gm[2]); const rest = gm[3];
        const r = getRepo(owner, name);
        if (rest === 'info/refs' && method === 'GET') {
          const q = queryOf(req);
          handleGitInfoRefs(req, res, owner, name, q.get('service') ?? '');
          return;
        }
        if (!r) { sendJson(res, 404, { message: 'Not Found' }); return; }
        if (rest === 'git-upload-pack' && method === 'POST') {
          const body = await readBody(req);
          handleGitUploadPack(req, res, r, body);
          return;
        }
        if (rest === 'git-receive-pack' && method === 'POST') {
          const body = await readBody(req);
          handleGitReceivePack(req, res, r, body);
          return;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return;
      }
      sendJson(res, 404, { message: 'Not Found' });
    } catch (e) {
      if (!res.headersSent) {
        try { sendJson(res, 500, { message: e instanceof Error ? e.message : 'Internal Server Error' }); } catch { /* ignore */ }
      }
    }
  });
  return server;
}
