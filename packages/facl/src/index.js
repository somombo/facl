// Node, Bun and Deno: load the wasm module from the file system.
import { readFileSync } from "node:fs";
import { initSync } from "../wasm/facl_wasm.js";

initSync({
  module: readFileSync(new URL("../wasm/facl_wasm_bg.wasm", import.meta.url)),
});

export { authorize, compile } from "./core.js";
