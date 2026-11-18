import assert from "node:assert/strict";
import { after, before, test } from "node:test";
import { unstable_startWorker } from "wrangler";

// Runs test/workerd/worker.js in workerd, which resolves facl's "workerd" export.
let worker;

before(async () => {
  process.env.WRANGLER_SEND_METRICS = "false";
  worker = await unstable_startWorker({
    config: new URL("./workerd/wrangler.jsonc", import.meta.url).pathname,
    dev: { server: { port: 0 }, inspector: false, logLevel: "warn" },
  });
  await worker.ready;
});

after(async () => {
  await worker?.dispose();
});

async function get(path, headers = {}) {
  const res = await worker.fetch(`http://facl.test${path}`, { headers });
  return [res.status, await res.text()];
}

test("the Hono middleware decides requests in workerd", async () => {
  assert.deepEqual(await get("/users/alice"), [403, '{"error":"forbidden"}']);
  assert.deepEqual(await get("/users/alice", { authorization: "Bearer bob" }), [
    200,
    '{"user":"alice"}',
  ]);
  assert.deepEqual(await get("/users/alice/", { authorization: "Bearer bob" }), [
    403,
    '{"error":"forbidden"}',
  ]);
});

test("authorize decides requests in workerd", async () => {
  assert.deepEqual(await get("/raw/x"), [200, '{"allowed":true,"reason":null}']);
});
