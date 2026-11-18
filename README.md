# facl

facl protects an HTTP API with a rules file in the style of Firebase Security Rules. Each `match` block names a URL pattern, and each `allow` statement grants HTTP methods when its condition, written in a small subset of CEL, is true. Any matching allow grants access; if nothing matches, the request is denied, and an erroring condition never grants.

All decision logic lives in `facl-core`, a small `no_std` engine written in the Rust subset that Aeneas can extract to Lean 4. The decision procedure is proven against a Lean spec for any condition evaluator. That covers path matching, method filtering, rule combination and the deny reasons; see [verification/](verification/README.md). The CEL evaluator, the parser and path canonicalization are tested, but not proven yet. `verification/check.sh` checks them end to end: it confirms the Lean code is what Aeneas generates from the Rust, then has `lake comparator` check the proofs in a sandbox. v0.3 is a Rust rewrite of the unmaintained 0.2.x JavaScript prototype.

## Example

```
service http {
  match /users/{userId} {
    // Signed-in users can read any profile; only the owner can change it.
    allow read: if request.auth != null;
    allow write: if request.auth != null && request.auth.uid == userId;

    // Rules don't cascade, so files need their own allow.
    match /files/{path=**} {
      allow read, write: if request.auth != null && request.auth.uid == userId;
    }
  }

  match /public/{path=**} {
    allow get, head: if true;
  }

  // The app verifies the Stripe signature against the raw body
  // and passes the result in as a fact.
  match /webhooks/stripe {
    allow post: if context.stripeVerified == true;
  }
}
```

`read` covers GET, HEAD and OPTIONS; `write` covers POST, PUT, PATCH and DELETE.

## CLI

```
cargo run -p facl-cli -- check api.rules
cargo run -p facl-cli -- eval api.rules GET /users/alice --auth '{"uid":"bob"}'
cargo run -p facl-cli -- test api.rules cases.json
```

- `facl check FILE` parses and checks a rules file.
- `facl eval FILE METHOD PATH [--auth JSON] [--header NAME=VALUE]... [--context JSON]` prints one decision as JSON.
- `facl test FILE CASES.json` runs a JSON array of cases such as `{ "request": "GET /admin", "expect": "deny" }` (optional keys: `name`, `headers`, `auth`, `context`, `reason`).

Exit codes: 0 success, 1 errors or failing cases, 2 usage errors.

## Tests

```
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all --check
cargo build -p facl-core --target wasm32-unknown-unknown   # rustup target add wasm32-unknown-unknown
```

The shared conformance cases live in `conformance/` as `NAME.rules` plus `NAME.cases.json` pairs; `crates/facl/tests/conformance.rs` runs every pair.

## JavaScript

The engine ships to JavaScript as WebAssembly in the `facl` npm package (`packages/facl`). It needs Rust with the `wasm32-unknown-unknown` target and `wasm-bindgen-cli` 0.2.130:

```sh
cd packages/facl
npm ci
npm run build   # cargo build for wasm32, then wasm-bindgen into wasm/
npm test
```

Check a Fetch `Request` with `authorize`, or protect a Hono app with the middleware:

```js
import { compile, authorize } from "facl";
import { facl } from "facl/hono";

const policy = compile(rulesText);               // throws an Error with `diagnostics` on bad rules
const { allowed, reason } = await authorize(policy, request, { auth: verifyJwt, context });

app.use("*", facl(policy, { auth: verifyJwt }));
```

- **Path contract.** The adapter passes `new URL(request.url).pathname`, still percent-encoded. The engine decodes each segment once. The path must be the one your router dispatches on. A path with an empty segment (`//`, or a trailing `/` other than the root) is denied as a bad request path, because routers disagree about such paths.
- **Denials.** The middleware answers 403 `{"error":"forbidden"}` by default. Pass `onDeny(c, decision)` to choose another response, such as 401 when no credentials were sent. The reason belongs in logs, not in client responses. Any internal failure (bad facts, a throwing verifier, a wasm trap) is a denial with the reason `internal_error`.
- **Footprint skipping.** `policy.footprint` lists what the policy reads (`headers`, `auth`, `context`). `authorize` gathers only those facts, so a policy that never reads `request.auth` never calls your verifier.
- **Large integers.** JavaScript numbers lose precision beyond 2^53. Pass such values in `context` with `JSON.rawJSON("...")`.
- **CORS.** Browsers send preflight `OPTIONS` requests without credentials, and `read` includes `OPTIONS`. Answer preflights with CORS middleware registered before facl.
- **Runtimes.**
  - Node 20 or later, and Bun.
  - Deno, with `--allow-read` so it can load the wasm file.
  - Cloudflare Workers. Wrangler resolves the package's `workerd` export, which imports the wasm as a module, so no configuration is needed.

## License

Copyright 2026 Chisomo Makombo Sakala. Licensed under the Apache License, Version 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The 0.2.x JavaScript prototype in this repository's history was released under the MIT License.
