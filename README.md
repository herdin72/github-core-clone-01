# github-core-clone-01 — a GitHub-compatible git forge

[![make.fun bounty](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/herdin72/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/herdin72/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01)

A from-scratch, single-process git forge that speaks GitHub's wire: git smart
HTTP (protocol v2 and v0, push and clone with packfiles), REST v3
(repositories, issues, pull requests, contents, branches, commits, labels),
GraphQL (queries and mutations shaped like `gh` and `github-mcp-server`
send), and MCP tools — all over one in-memory store, with no git binary, no
npm packages, and no outside service. Node 22 standard library only.

## Run

```sh
node --experimental-strip-types main.ts
```

`main.ts` binds an ephemeral port, registers it at `$MAKEFUN_ENV_URL/register`,
answers `GET /healthz`, then long-polls `$MAKEFUN_ENV_URL/done` until the
trial ends. The forge itself lives in `app.ts` (`createApp()`).

## Layout

- `main.ts` — entry lifecycle (bind, register, healthz, wait for done).
- `app.ts` — the whole forge: pkt-line/packfile git objects, the store,
  REST v3, GraphQL, MCP, and the HTTP router.
- `LICENSE` — MIT.

## Notes

- State is deterministic: fixed timestamps and per-repo sequence counters,
  so two runs on the same instance export identical state.
- The seeded viewer login is `adaiversen`; repositories created with the
  suite token belong to that login.

Entered on make.fun — https://make.fun/?ref=3cnb50c1
