/**
 * Conformance parity: runs the shared `conformance/` suite through wasm.
 * Cases are evaluated with their raw facts, bypassing the URL parser, which
 * would normalize the dot-segment cases before the engine saw them.
 */

import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { test } from "node:test";
import { compile } from "../src/index.js";

const dir = new URL("../../../conformance/", import.meta.url);
const names = readdirSync(dir)
  .filter((f) => f.endsWith(".rules"))
  .map((f) => f.slice(0, -".rules".length));

/**
 * Parses JSON keeping integers beyond 2^53 exact. Plain `JSON.parse` would
 * round them to a float, which the engine rightly rejects.
 */
function parseExact(text) {
  return JSON.parse(text, (_key, value, { source }) =>
    typeof value === "number" && /^-?\d+$/.test(source) && !Number.isSafeInteger(value)
      ? JSON.rawJSON(source)
      : value,
  );
}

/** Turns a case into the facts shape: `request` is `METHOD PATH`. */
function toFacts(c) {
  const [, method, path] = /^(\S+)\s+(.*)$/s.exec(c.request);
  const facts = { method, path };
  if (c.headers !== undefined) facts.headers = c.headers;
  if (c.auth !== undefined) facts.auth = c.auth;
  if (c.context !== undefined) facts.context = c.context;
  return facts;
}

assert.ok(names.length > 0, "no conformance files found");

for (const name of names) {
  const source = readFileSync(new URL(`${name}.rules`, dir), "utf8");
  const cases = parseExact(readFileSync(new URL(`${name}.cases.json`, dir), "utf8"));
  test(`conformance/${name}`, async (t) => {
    const policy = compile(source);
    for (const c of cases) {
      await t.test(c.name ?? c.request, () => {
        const decision = policy.evaluate(toFacts(c));
        assert.equal(decision.allowed, c.expect === "allow", JSON.stringify(decision));
        if (c.reason !== undefined) assert.equal(decision.reason, c.reason);
      });
    }
  });
}
