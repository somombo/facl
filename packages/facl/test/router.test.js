/**
 * Router agreement: the M2 gate. A request facl allows must reach the
 * handler with the very value the policy checked, whatever the path's
 * encoding tricks. Hono decides what the handler sees, so each case first
 * asks Hono, then asks facl about the same request.
 */

import assert from "node:assert/strict";
import { test } from "node:test";
import { Hono } from "hono";
import { compile } from "../src/index.js";
import { facl } from "../src/hono.js";

const policy = compile(`
  service http {
    match /users/{userId} {
      allow read: if userId == request.headers["x-expect"];
    }
  }
`);

/** Builds the app; `guarded` adds facl in front of the same route. */
function makeApp(guarded) {
  const app = new Hono();
  if (guarded) app.use("*", facl(policy));
  app.get("/users/:userId", (c) => c.json({ userId: c.req.param("userId") }));
  app.get("*", (c) => c.json({ other: true }));
  return app;
}

const plain = makeApp(false);
const guarded = makeApp(true);

/** What the handler of /users/:userId saw, or null if that route did not run. */
async function handlerSaw(app, path, headers = {}) {
  const res = await app.request(`http://localhost${path}`, { headers });
  if (res.status !== 200) return { status: res.status, userId: null };
  const body = await res.json();
  return { status: 200, userId: "userId" in body ? body.userId : null };
}

const tricky = [
  "/users/%20",
  "/users/%41",
  "/users/%C3%A9",
  "/users/é",
  "//users//a",
  "/users/a//",
  "/users/a/",
  "/users/a/./",
  "/users/./a",
  "/users/x/../a",
  "/users/x/../",
  "/users/%2e%2e",
  "/users/a%2Fb",
  "/users/%252F",
  "/users/%00",
  "/users/%FF",
  "/users/a/b",
  "/users/%2e",
  "/users/a%20b",
];

test("plain paths are allowed and reach the handler", async () => {
  for (const id of ["alice", "42", "a-b_c"]) {
    const seen = await handlerSaw(guarded, `/users/${id}`, { "x-expect": id });
    assert.deepEqual(seen, { status: 200, userId: id });
  }
});

test("a plain mismatch is denied with 403", async () => {
  const res = await guarded.request("http://localhost/users/alice", {
    headers: { "x-expect": "bob" },
  });
  assert.equal(res.status, 403);
  assert.deepEqual(await res.json(), { error: "forbidden" });
});

const table = [];

/** Header values worth trying besides what the handler saw. */
const guesses = ["a", "x", "A", " ", "b", "é", "a/b", "%2F"];

/** Sends a request through facl with `x-expect`; null if it cannot be sent. */
async function throughFacl(path, expect) {
  try {
    return await guarded.request(`http://localhost${path}`, {
      headers: { "x-expect": expect },
    });
  } catch {
    return null; // not a valid header value, so no such request exists
  }
}

for (const path of tricky) {
  test(`facl and Hono agree on ${path}`, async () => {
    const seen = (await handlerSaw(plain, path)).userId;
    const candidates = new Set(seen === null ? guesses : [seen, ...guesses]);
    const outcomes = [];
    for (const expect of candidates) {
      const res = await throughFacl(path, expect);
      if (res === null) continue;
      if (res.status === 200) {
        // Allowed: the protected handler must have run with exactly the
        // value the policy compared against.
        const body = await res.json();
        assert.equal(body.userId, expect, `allowed, but the handler saw ${JSON.stringify(body)}`);
        outcomes.push(`allow(${JSON.stringify(expect)})`);
      } else {
        assert.equal(res.status, 403);
      }
    }
    const saw = seen === null ? "other route" : JSON.stringify(seen);
    table.push(`${path}\tHono: ${saw}\tfacl: ${outcomes.join(" ") || "deny"}`);
  });
}

test("an allowed request reaches the handler of the route the policy protects", async () => {
  // Another route under a different prefix must not be reachable by the
  // /users rule, and /users/:userId must be what runs for an allowed request.
  const app = new Hono();
  app.use("*", facl(policy));
  let usersCalls = 0;
  let otherCalls = 0;
  app.get("/users/:userId", (c) => (usersCalls++, c.text("users")));
  app.get("/other/:id", (c) => (otherCalls++, c.text("other")));

  const ok = await app.request("http://localhost/users/alice", {
    headers: { "x-expect": "alice" },
  });
  assert.equal(ok.status, 200);
  assert.equal(usersCalls, 1);

  const denied = await app.request("http://localhost/other/alice", {
    headers: { "x-expect": "alice" },
  });
  assert.equal(denied.status, 403);
  assert.equal(otherCalls, 0);
});

test.after(() => {
  console.log("\nrouter agreement table:\n" + table.join("\n"));
});
