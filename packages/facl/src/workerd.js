// Cloudflare Workers cannot read files or compile wasm at runtime, so the
// module is imported: Wrangler bundles it as a precompiled WebAssembly.Module.
import wasm from "../wasm/facl_wasm_bg.wasm";
import { initSync } from "../wasm/facl_wasm.js";

initSync({ module: wasm });

export { authorize, compile } from "./core.js";
