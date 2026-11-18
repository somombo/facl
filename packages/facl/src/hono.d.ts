import type { Context, MiddlewareHandler } from "hono";
import type { AuthorizeOptions, Decision, Policy } from "./index.js";

export interface FaclOptions extends AuthorizeOptions {
  /** Builds the response for a denied request. Default: 403 `{"error":"forbidden"}`. */
  onDeny?: (c: Context, decision: Decision) => Response | Promise<Response>;
}

/** Hono middleware that enforces `policy` on every request. */
export function facl(policy: Policy, options?: FaclOptions): MiddlewareHandler;
