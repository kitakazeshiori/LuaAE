import init, { run_lua_code } from './pkg/luaae_wasm.js';
let isReady = false;
let lastPanicMsg = "";
const originalConsoleError = console.error;
console.error = function(...args) {
    lastPanicMsg = args.join(" ");
    originalConsoleError.apply(console, args);
};

self.onmessage = async (event) => {
    const code = event.data;
    lastPanicMsg = "";
    try {
        if (!isReady) {
            await init();
            isReady = true;
        }
        const result = run_lua_code(code);
        self.postMessage({ status: 'success', data: result });
        
    } catch (err) {
        const errorData = lastPanicMsg || err.toString();
        self.postMessage({ status: 'panic', data: errorData });
    }
};