/**
 * Example: the design doc's policy behind matching Hono routes.
 *
 *   npm run build && npm run example
 *   curl -i localhost:3000/public/logo.png
 *   curl -i localhost:3000/users/alice
 *   curl -i -H 'authorization: Bearer alice' localhost:3000/users/alice
 */

import { serve } from "@hono/node-server";
import { Hono } from "hono";
import { compile } from "facl";
import { facl } from "facl/hono";

const rules = `
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

/** A toy verifier: "Bearer <uid>" means that user. Use real JWT checks in production. */
function verifyToken(request) {
  const match = /^Bearer (\w+)$/.exec(request.headers.get("authorization") ?? "");
  return match ? { uid: match[1], token: match[1] } : null;
}

const policy = compile(rules);
const app = new Hono();

app.use(
  "*",
  facl(policy, {
    auth: verifyToken,
    // The app would verify the Stripe signature against the raw body here.
    context: () => ({ stripeVerified: false }),
    onDeny: (c, decision) => {
      console.log(`denied ${c.req.method} ${c.req.path}: ${decision.reason}`);
      return c.json({ error: "forbidden" }, 403);
    },
  }),
);

app.get("/users/:userId", (c) => c.json({ user: c.req.param("userId") }));
app.put("/users/:userId", (c) => c.json({ updated: c.req.param("userId") }));
app.get("/users/:userId/files/*", (c) => c.json({ files: c.req.path }));
app.get("/public/*", (c) => c.text("public"));
app.post("/webhooks/stripe", (c) => c.text("ok"));

serve({ fetch: app.fetch, port: 3000 });
console.log("listening on http://localhost:3000");
