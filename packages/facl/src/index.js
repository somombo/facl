/**
 * facl: access-control policies for Fetch-standard requests.
 *
 * The engine is Rust compiled to WebAssembly. This module loads it, wraps a
 * compiled policy, and provides `authorize`, which turns a `Request` into
 * the facts the engine decides on.
 */

import { readFileSync } from "node:fs";
import init, { initSync, Policy as WasmPolicy } from "../wasm/facl_wasm.js";

void init; // the async loader is unused; Node loads the module synchronously
initSync({
  module: readFileSync(new URL("../wasm/facl_wasm_bg.wasm", import.meta.url)),
});

/**
 * Compiles a rules file.
 *
 * @param {string} source
 * @returns {import("./index.js").Policy}
 * @throws {Error} with a `diagnostics` array when the rules are rejected.
 */
export function compile(source) {
  const wasm = WasmPolicy.compile(source);
  const footprint = Object.freeze({ ...wasm.footprint });
  return Object.freeze({
    footprint,
    /** Decides one request from raw facts; throws on unusable facts. */
    evaluate(facts) {
      return JSON.parse(wasm.evaluate(JSON.stringify(facts)));
    },
  });
}

const INTERNAL_ERROR = Object.freeze({
  allowed: false,
  reason: "internal_error",
});

/**
 * Decides a Fetch `Request`. Never throws: any failure, including a wasm
 * trap, bad facts or a failing verifier, is a denial with the reason
 * `internal_error`.
 *
 * Only the facts in the policy's footprint are gathered, so a policy that
 * never reads `request.auth` never calls the verifier.
 *
 * @param {import("./index.js").Policy} policy
 * @param {Request} request
 * @param {import("./index.js").AuthorizeOptions} [options]
 * @returns {Promise<import("./index.js").Decision>}
 */
export async function authorize(policy, request, options = {}) {
  try {
    const { footprint } = policy;
    const facts = {
      method: request.method,
      // The pathname is the percent-encoded path a router dispatches on.
      // It is passed through undecoded; the engine decodes it once.
      path: new URL(request.url).pathname,
    };
    if (footprint.headers) {
      facts.headers = Object.fromEntries(request.headers);
    }
    if (footprint.auth && options.auth) {
      facts.auth = (await options.auth(request)) ?? null;
    }
    if (footprint.context && options.context) {
      const { context } = options;
      facts.context = typeof context === "function" ? await context(request) : context;
    }
    const decision = policy.evaluate(facts);
    return { allowed: decision.allowed === true, reason: decision.reason ?? null };
  } catch {
    return { ...INTERNAL_ERROR };
  }
}
