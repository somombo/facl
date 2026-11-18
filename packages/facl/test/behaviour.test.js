/** Behaviour of `authorize` and the Hono middleware. */

import assert from "node:assert/strict";
import { test } from "node:test";
import { Hono } from "hono";
import { authorize, compile } from "../src/index.js";
import { facl } from "../src/hono.js";

const req = (path, init) => new Request(`http://localhost${path}`, init);

test("the verifier is not called when the policy never reads request.auth", async () => {
  const policy = compile("service http { match /open { allow read: if true; } }");
  assert.equal(policy.footprint.auth, false);
  let calls = 0;
  const decision = await authorize(policy, req("/open"), {
    auth: () => (calls++, { uid: "a" }),
  });
  assert.deepEqual(decision, { allowed: true, reason: null });
  assert.equal(calls, 0);
});

test("the verifier is called when the policy reads request.auth", async () => {
  const policy = compile(
    "service http { match /me { allow read: if request.auth != null; } }",
  );
  assert.equal(policy.footprint.auth, true);
  let calls = 0;
  const auth = () => (calls++, { uid: "a" });
  assert.equal((await authorize(policy, req("/me"), { auth })).allowed, true);
  assert.equal(calls, 1);
  assert.equal((await authorize(policy, req("/me"))).allowed, false);
});

test("context may be an object or a function, and is read only when needed", async () => {
  const policy = compile(
    "service http { match /hook { allow post: if context.ok == true; } }",
  );
  const post = () => req("/hook", { method: "POST" });
  assert.equal((await authorize(policy, post(), { context: { ok: true } })).allowed, true);
  assert.equal(
    (await authorize(policy, post(), { context: async () => ({ ok: false }) })).allowed,
    false,
  );
  const open = compile("service http { match /x { allow read: if true; } }");
  let calls = 0;
  await authorize(open, req("/x"), { context: () => (calls++, {}) });
  assert.equal(calls, 0);
});

test("denials carry the engine's reason", async () => {
  const policy = compile("service http { match /a { allow read: if true; } }");
  assert.deepEqual(await authorize(policy, req("/b")), {
    allowed: false,
    reason: "no_matching_rule",
  });
  assert.deepEqual(await authorize(policy, req("/a", { method: "POST" })), {
    allowed: false,
    reason: "no_allow_for_method",
  });
});

test("a throwing verifier is an internal_error denial", async () => {
  const policy = compile(
    "service http { match /me { allow read: if request.auth != null; } }",
  );
  const decision = await authorize(policy, req("/me"), {
    auth: () => {
      throw new Error("jwks down");
    },
  });
  assert.deepEqual(decision, { allowed: false, reason: "internal_error" });
});

test("a FactsError gives 403 and the handler is not called", async () => {
  const policy = compile(
    "service http { match /hook { allow post: if context.n == 1; } }",
  );
  let handled = 0;
  const app = new Hono();
  app.use("*", facl(policy, { context: () => ({ n: 1.5 }) }));
  app.post("/hook", (c) => (handled++, c.text("ok")));
  const res = await app.request("http://localhost/hook", { method: "POST" });
  assert.equal(res.status, 403);
  assert.equal(handled, 0);
  const direct = await authorize(policy, post(), { context: { n: 1.5 } });
  assert.deepEqual(direct, { allowed: false, reason: "internal_error" });

  function post() {
    return req("/hook", { method: "POST" });
  }
});

test("onDeny can answer 401", async () => {
  const policy = compile(
    "service http { match /me { allow read: if request.auth != null; } }",
  );
  const seen = [];
  const app = new Hono();
  app.use(
    "*",
    facl(policy, {
      auth: () => null,
      onDeny: (c, decision) => {
        seen.push(decision.reason);
        return c.json({ error: "unauthorized" }, 401);
      },
    }),
  );
  app.get("/me", (c) => c.text("me"));
  const res = await app.request("http://localhost/me");
  assert.equal(res.status, 401);
  assert.deepEqual(seen, ["conditions_not_met"]);
});

test("compile throws an Error with diagnostics", () => {
  assert.throws(
    () => compile("service http { match /a { allow read: if nope; } }"),
    (e) =>
      e instanceof Error &&
      Array.isArray(e.diagnostics) &&
      e.diagnostics.length > 0 &&
      e.diagnostics[0].severity === "error" &&
      Number.isInteger(e.diagnostics[0].line) &&
      Number.isInteger(e.diagnostics[0].col) &&
      typeof e.diagnostics[0].message === "string",
  );
});
