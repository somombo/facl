# facl

Firebase-style access-control rules for HTTP APIs. A small Rust engine, compiled to WebAssembly, decides every request. Rule compilation, path canonicalization, path matching and rule combination are proven against a Lean 4 spec; conditions are tested.

> v0.3 is a prototype. The rules language and the API may change.

## Example

```js
import { Hono } from "hono";
import { compile } from "facl";
import { facl } from "facl/hono";

const policy = compile(`
service http {
  match /users/{userId} {
    allow read: if request.auth != null;
    allow write: if request.auth != null && request.auth.uid == userId;
  }
}
`);

const app = new Hono();
app.use("*", facl(policy, { auth: verifyJwt })); // verifyJwt(request) returns { uid, ... } or null
app.get("/users/:userId", (c) => c.json({ user: c.req.param("userId") }));
```

Any matching `allow` grants access. If nothing matches, the request is denied, and a condition that errors never grants.

## Other frameworks

`authorize` checks any Fetch `Request`:

```js
import { compile, authorize } from "facl";

const { allowed, reason } = await authorize(policy, request, {
  auth: verifyJwt,                   // (request) => facts or null; may be async
  context: { stripeVerified: true }, // or (request) => facts; your own data, read as `context`
});
```

`compile` throws an `Error` whose `diagnostics` list each problem with its line and column.

## Behaviour

- **Path contract.** facl reads `new URL(request.url).pathname`, still percent-encoded, and decodes each segment once. That must be the path your router dispatches on. A path with an empty segment (`//`, or a trailing `/` other than the root) is denied, because routers disagree about such paths.
- **Denials.** The middleware answers 403 `{"error":"forbidden"}` by default. Pass `onDeny(c, decision)` to choose another response, such as 401 when no credentials were sent. Keep the reason in logs, not in responses.
- **Failures deny.** Bad facts, a throwing verifier or a wasm trap all deny the request, with the reason `internal_error`.
- **Footprint.** `policy.footprint` lists what the policy reads: `headers`, `auth` and `context`. `authorize` gathers only those, so a policy that never reads `request.auth` never calls your verifier.
- **CORS.** Browsers send preflight `OPTIONS` requests without credentials, and `read` includes `OPTIONS`. Answer preflights with CORS middleware registered before facl.
- **Large integers.** JavaScript numbers lose precision beyond 2^53. Pass such values in `context` with `JSON.rawJSON("...")`.
- **Runtimes.**
  - Node 20 or later, and Bun.
  - Deno, with `--allow-read` so it can load the wasm file.
  - Cloudflare Workers. Wrangler resolves the package's `workerd` export, which imports the wasm as a module, so no configuration is needed.

## Building from source

The [repository](https://github.com/somombo/facl) holds the Rust engine. Building this package needs Rust with the `wasm32-unknown-unknown` target and `wasm-bindgen-cli` 0.2.130. Then run `npm run build` and `npm test`.

## License

Copyright 2026 Chisomo Makombo Sakala. Licensed under the Apache License, Version 2.0; see LICENSE.
