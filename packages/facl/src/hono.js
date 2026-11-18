/**
 * Hono middleware for facl.
 */

import { authorize } from "./index.js";

/**
 * Creates middleware that checks every request against `policy` before the
 * route handler runs.
 *
 * Denied requests get 403 with `{"error":"forbidden"}` unless `onDeny` is
 * given. The reason is passed to `onDeny` for logging and never sent to the
 * client by default.
 *
 * @param {import("./index.js").Policy} policy
 * @param {import("./hono.js").FaclOptions} [options]
 */
export function facl(policy, options = {}) {
  const { auth, context, onDeny } = options;
  return async (c, next) => {
    const decision = await authorize(policy, c.req.raw, { auth, context });
    if (decision.allowed) {
      await next();
      return;
    }
    if (onDeny) {
      return onDeny(c, decision);
    }
    return c.json({ error: "forbidden" }, 403);
  };
}
