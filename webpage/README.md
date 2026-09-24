# Browser VM

The IDE loads `pkg/luaae_wasm.js` and `pkg/luaae_wasm_bg.wasm` from this directory. Rebuild both generated files after changing `luaae.rs`:

```console
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.128
cargo build --lib --target wasm32-unknown-unknown --release
wasm-bindgen target/wasm32-unknown-unknown/release/luaae_wasm.wasm --target web --out-dir webpage/pkg --out-name luaae_wasm
```

Serve `webpage/` over HTTP to run the IDE locally. Browser sandbox restrictions apply to filesystem and process APIs. A Rust runtime panic currently traps the WebAssembly instance; the worker restarts it for the next run.
