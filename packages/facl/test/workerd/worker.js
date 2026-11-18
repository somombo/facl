import { Hono } from "hono";
import { authorize, compile } from "facl";
import { facl } from "facl/hono";

const policy = compile(`
service http {
  match /users/{userId} {
    allow read: if request.auth != null;
  }
  match /raw/{path=**} {
    allow get: if true;
  }
}
`);

const auth = (request) =>
  request.headers.get("authorization") === "Bearer bob" ? { uid: "bob" } : null;

const app = new Hono();
app.get("/raw/*", async (c) => c.json(await authorize(policy, c.req.raw, { auth })));
app.use("*", facl(policy, { auth }));
app.get("/users/:userId", (c) => c.json({ user: c.req.param("userId") }));

export default app;
