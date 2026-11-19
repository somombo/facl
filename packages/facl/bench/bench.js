/** Micro-benchmarks. Run `npm run build` first, then `npm run bench`. */

import assert from "node:assert/strict";
import os from "node:os";
import { authorize, compile } from "../src/index.js";

const README = `
service http {
  match /users/{userId} {
    allow read: if request.auth != null;
    allow write: if request.auth != null && request.auth.uid == userId;
    match /files/{path=**} {
      allow read, write: if request.auth != null && request.auth.uid == userId;
    }
  }
  match /public/{path=**} {
    allow get, head: if true;
  }
  match /webhooks/stripe {
    allow post: if context.stripeVerified == true;
  }
}
`;
const MANY = `service http {\n${Array.from(
  { length: 100 },
  (_, i) => `match /r${i}/{id} { allow read: if request.auth.uid == id; }\n`,
).join("")}}`;
const PUBLIC_ONLY = "service http { match /public/{path=**} { allow get: if true; } }";

/** Runs `f` in batches of about 20 ms and returns the median ns/op. */
async function measure(f) {
  const now = () => Number(process.hrtime.bigint());
  const start = now();
  let n = 0;
  while (now() - start < 100e6) {
    await f();
    n++;
  }
  const size = Math.max(1, Math.floor(20e6 / ((now() - start) / n)));
  const samples = [];
  for (let b = 0; b < 15; b++) {
    const t = now();
    for (let i = 0; i < size; i++) await f();
    samples.push((now() - t) / size);
  }
  return samples.sort((a, b) => a - b)[7];
}

const row = (name, layer, ns) =>
  console.log(`${name.padEnd(24)} ${layer.padEnd(14)} ${ns.toFixed(1).padStart(12)} ${(1e9 / ns).toFixed(0).padStart(14)}`);

console.log(`node ${process.version}, ${os.cpus()[0].model}`);
console.log(`${"scenario".padEnd(24)} ${"layer".padEnd(14)} ${"ns/op".padStart(12)} ${"ops/s".padStart(14)}`);

const alice = { uid: "alice" };
const cases = [
  ["public read", README, "GET", "/public/docs/a.txt", null, true],
  ["owner write", README, "PUT", "/users/alice", alice, true],
  ["no rule", README, "DELETE", "/admin", null, false],
  ["bad path", README, "GET", "/a//b", null, false],
  ["100 rules, last matches", MANY, "GET", "/r99/alice", alice, true],
  ["footprint", PUBLIC_ONLY, "GET", "/public/x", null, true],
];

for (const [name, source, method, path, auth, allowed] of cases) {
  const policy = compile(source);
  const facts = { method, path, auth };
  assert.equal(policy.evaluate(facts).allowed, allowed, name);
  row(name, "wasm evaluate", await measure(() => policy.evaluate(facts)));

  let calls = 0;
  const options = { auth: () => (calls++, auth) };
  const request = new Request("http://localhost" + path, { method });
  assert.equal((await authorize(policy, request, options)).allowed, allowed, name);
  if (name === "footprint") {
    assert.equal(calls, 0, "authorize must not call the auth hook");
  }
  row(name, "authorize", await measure(() => authorize(policy, request, options)));
  if (name === "footprint") {
    assert.equal(calls, 0, "authorize must not call the auth hook");
  }
}
row("compile (README)", "wasm", await measure(() => compile(README)));
