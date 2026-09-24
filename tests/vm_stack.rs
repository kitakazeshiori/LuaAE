use std::path::Path;
use std::process::Command;

#[test]
fn command_line_errors_exit_nonzero() {
    for args in [
        vec!["-e", "error('command line failure')"],
        vec!["-l", "__missing_luaae_module__"],
        vec!["__missing_luaae_script__.lua"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
            .args(&args)
            .output()
            .expect("execute failing command line");
        assert!(
            !output.status.success() && !output.stderr.is_empty(),
            "args: {args:?}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn deep_lua_calls_use_vm_frames() {
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/vm_stack.lua");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .arg(script)
        .output()
        .expect("execute VM stack regression");
    assert!(
        output.status.success() && String::from_utf8_lossy(&output.stdout).trim() == "OK",
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn stack_overflow_traceback_has_lua_line_locations() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function recurse() return 1 + recurse() end; local ok, trace = xpcall(recurse, debug.traceback); assert(not ok and trace:find('stack overflow', 1, true)); assert(trace:match(':%d+: in function'))",
        ])
        .output()
        .expect("execute stack overflow traceback regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn xpcall_reports_error_in_error_handler() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local ok, msg = xpcall(error, error); assert(not ok and type(msg) == 'string' and msg:find('error in error handling', 1, true))",
        ])
        .output()
        .expect("execute xpcall double-error regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn xpcall_traceback_preserves_error_metamethod_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local env = {}; setmetatable(env, {__newindex = function() error('metamethod failed') end}); local chunk = assert(load('X = 1', '=(traceback)', 't', env)); local ok, trace = xpcall(chunk, debug.traceback); assert(not ok and trace:find(\"'__newindex'\", 1, true), trace); ok, trace = xpcall(chunk, function(message) local inner_ok = pcall(error, 'inner'); assert(not inner_ok); return debug.traceback(message) end); assert(not ok and trace:find(\"'__newindex'\", 1, true), trace)",
        ])
        .output()
        .expect("execute xpcall metamethod traceback");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn official_big_lua_passes_without_soft_mode() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local run = coroutine.wrap(assert(loadfile('big.lua'))); assert(run() == 'b'); assert(run() == 'a')",
        ])
        .current_dir(&suite)
        .output()
        .expect("execute official big.lua");
    assert!(
        output.status.success()
            && output.stderr.is_empty()
            && String::from_utf8_lossy(&output.stdout).contains("testing large tables\nOK"),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn official_sort_lua_passes_without_soft_mode() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .arg("sort.lua")
        .current_dir(&suite)
        .output()
        .expect("execute official sort.lua");
    assert!(
        output.status.success()
            && output.stderr.is_empty()
            && String::from_utf8_lossy(&output.stdout).ends_with("OK\n"),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "full portable Lua 5.3.4 suite takes about a minute in release"]
fn official_full_portable_suite_passes_without_soft_mode() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args(["-e", "_port=true", "all.lua"])
        .current_dir(&suite)
        .output()
        .expect("execute official all.lua");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success()
            && stdout.contains("***** FILE 'constructs.lua'*****")
            && stdout.contains("***** FILE 'big.lua'*****")
            && stdout.contains("***** FILE 'sort.lua'*****")
            && stdout.contains("testing large programs (>64k)")
            && stdout.contains("final OK !!!"),
        "stdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn nested_sort_comparators_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local calls=0; local function descend(n) if n==0 then return end; local a={2,1}; table.sort(a, function(x,y) calls=calls+1; if x==1 and y==2 then descend(n-1) end; return x<y end); assert(a[1]==1 and a[2]==2) end; descend(6000); assert(calls==12000)",
        ])
        .output()
        .expect("execute nested table.sort comparator regression");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn nested_sort_metamethods_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local mt={}; local calls=0; local function descend(n) if n==0 then return end; local a={setmetatable({rank=2,depth=n},mt),setmetatable({rank=1,depth=n},mt)}; table.sort(a); assert(a[1].rank==1 and a[2].rank==2) end; mt.__lt=function(a,b) calls=calls+1; if a.rank==2 and b.rank==1 then descend(a.depth-1) end; return a.rank<b.rank end; descend(4000); assert(calls==4000)",
        ])
        .output()
        .expect("execute nested table.sort __lt regression");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn table_sort_proxy_callbacks_use_vm_continuations() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local source={3,1,2}; local target={}; local reads=0; local compares=0; local proxy=setmetatable({}, {__len=function() return 3 end, __index=function(_, k) reads=reads+1; return source[k] end, __newindex=function(_, k, v) target[k]=v end}); table.sort(proxy, function(a,b) compares=compares+1; return a<b end); assert(reads==3 and compares>0 and target[1]==1 and target[2]==2 and target[3]==3)",
        ])
        .output()
        .expect("execute proxy table.sort continuation regression");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn stack_overflow_inside_error_handler_reports_error_handling() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function recurse() return 1 + recurse() end; local ok, result = xpcall(recurse, function(message) assert(message:find('stack overflow', 1, true)); local inner_ok, inner_message = pcall(recurse); assert(not inner_ok and inner_message:find('error in error handling', 1, true)); return 15 end); assert(not ok and result == 15)",
        ])
        .output()
        .expect("execute nested stack overflow regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_protected_lua_calls_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function descend(n) if n == 0 then return 0 end; local ok, value = pcall(descend, n - 1); assert(ok); return value + 1 end; assert(descend(10000) == 10000); local function descend_x(n) if n == 0 then return 0 end; local ok, value = xpcall(descend_x, function(e) return e end, n - 1); assert(ok); return value + 1 end; assert(descend_x(5000) == 5000); local ok, message = xpcall(function() error('inner') end, function(e) return e end); assert(not ok and message:find('inner', 1, true))",
        ])
        .output()
        .expect("execute protected VM stack regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_xpcall_error_handlers_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local descend; descend = function(n) if n == 0 then return 42 end; local ok, value = xpcall(function() error('boom') end, function(message) assert(message:find('boom', 1, true)); if n % 250 == 0 then collectgarbage() end; return descend(n - 1), 'ignored' end); assert(not ok); return value end; assert(descend(2000) == 42); local ok, value = xpcall(error, function(message) collectgarbage(); return message end, 'native failure'); assert(not ok and value:find('native failure', 1, true)); local ok2, value2 = xpcall(error, function() error('handler failure') end, 'native failure'); assert(not ok2 and value2:find('error in error handling', 1, true))",
        ])
        .output()
        .expect("execute nested xpcall error handlers");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_print_and_tostring_metamethods_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local original_print, native_tostring = print, tostring; local depth = 0; tostring = function(n) if n > 0 then original_print(n - 1) end; depth = depth + 1; return 'x' end; original_print(2500); assert(depth == 2501); tostring = native_tostring; local mt = {}; mt.__tostring = function(self) if self.n == 0 then return 'done' end; return tostring(setmetatable({n = self.n - 1}, mt)) end; assert(tostring(setmetatable({n = 2500}, mt)) == 'done')",
        ])
        .output()
        .expect("execute deep print and tostring callbacks");
    assert!(
        output.status.success()
            && output.stderr.is_empty()
            && String::from_utf8_lossy(&output.stdout).lines().count() == 2501,
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_io_method_callbacks_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local mt = getmetatable(io.stdout); assert(mt == getmetatable(io.stdin)); mt.write = function(self, n) if n == 0 then return 'written', 17 end; return io.write(n - 1) end; local a, b = io.write(2000); assert(a == 'written' and b == 17); mt.read = function(self, n) if n == 0 then return 'read', 23 end; return io.read(n - 1) end; a, b = io.read(2000); assert(a == 'read' and b == 23); local remaining = 2000; mt.flush = function(self) if remaining == 0 then return 'flushed' end; remaining = remaining - 1; return io.flush() end; assert(io.flush() == 'flushed'); remaining = 2000; mt.close = function(self) if remaining == 0 then return 'closed' end; remaining = remaining - 1; return io.close(self) end; assert(io.close(io.stdout) == 'closed')",
        ])
        .output()
        .expect("execute deep IO method callbacks");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_io_open_callbacks_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local remaining = 2000; io.open = function(path, mode) if mode == 'r' then if remaining == 0 then return io.stdin end; remaining = remaining - 1; return io.input(path) end; if remaining == 0 then return io.stdout end; remaining = remaining - 1; return io.output(path) end; assert(io.input('nested') == io.stdin and io.input() == io.stdin); remaining = 2000; assert(io.output('nested') == io.stdout and io.output() == io.stdout); io.open = function() return nil, 'open failed' end; local ok, message = pcall(io.input, 'missing'); assert(not ok and message:find('open failed', 1, true))",
        ])
        .output()
        .expect("execute deep IO open callbacks");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_load_readers_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function reader(n) local used = false; return function() if used then return nil end; used = true; if n > 0 then assert(assert(load(reader(n - 1)))() == 42) end; return 'return 42', 'ignored' end end; assert(assert(load(reader(2000)))() == 42); local chunks, index = {'return ', '17'}, 0; local f = assert(load(function() index = index + 1; return chunks[index] end)); assert(f() == 17); local bad, message = load(function() error('reader exploded') end); assert(bad == nil and message:find('reader exploded', 1, true)); bad, message = load(function() return 4 end); assert(bad == nil and message:find('reader function must return a string', 1, true)); local used = false; f = assert(load(function() if used then return nil end; used = true; return 'return value' end, 'custom', 't', {value = 9})); assert(f() == 9)",
        ])
        .output()
        .expect("execute deep load readers");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn load_reader_remains_unyieldable_in_coroutines() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "coroutine.wrap(function() assert(coroutine.isyieldable()); local chunk = assert(load(function() assert(not coroutine.isyieldable()); local ok, message = pcall(coroutine.yield); assert(not ok and message:find('C-call boundary', 1, true)); return nil end)); assert(chunk() == nil); assert(coroutine.isyieldable()) end)()",
        ])
        .output()
        .expect("execute unyieldable load reader");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_pairs_metamethods_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local mt = {}; mt.__pairs = function(self) if self.n == 0 then return function() end, 'state', 91 end; return pairs(setmetatable({n = self.n - 1}, mt)) end; local iterator, state, key = pairs(setmetatable({n = 5000}, mt)); assert(type(iterator) == 'function' and state == 'state' and key == 91)",
        ])
        .output()
        .expect("execute deep pairs metamethods");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_table_foreach_callbacks_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function descend(n) if n == 0 then return 0 end; return table.foreach({n}, function(_, value) return descend(value - 1) + 1 end) end; assert(descend(5000) == 5000); local function descend_i(n) if n == 0 then return 0 end; return table.foreachi({n}, function(_, value) return descend_i(value - 1) + 1 end) end; assert(descend_i(5000) == 5000); assert(table.foreach({7}, function() return 'first', 'second' end) == 'first'); assert(table.foreachi({7}, function() return 'first', 'second' end) == 'first'); local items = {entry = 'held'}; assert(table.foreach(items, function(key, value) items[key] = nil; collectgarbage(); return value end) == 'held')",
        ])
        .output()
        .expect("execute deep table foreach callbacks");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_gsub_callbacks_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function deep(n) if n == 0 then return 'done' end; return (string.gsub('x', '.', function() return deep(n - 1) end)) end; assert(deep(3500) == 'done'); local text, count = string.gsub('a1b2', '(%a)(%d)', function(letter, digit) collectgarbage(); return digit .. letter, 'ignored' end); assert(text == '1a2b' and count == 2); text, count = string.gsub('abc', '.', function(letter) if letter == 'b' then return nil end; return false end); assert(text == 'abc' and count == 3); text, count = string.gsub('aba', '^.', function() return 'X' end); assert(text == 'Xba' and count == 1); assert(string.gsub('aba', '^.', 'X') == 'Xba'); assert(string.gsub('aba', '^z', 'X') == 'aba'); text, count = string.gsub('ab', '', function() return '-' end); assert(text == '-a-b-' and count == 3); text, count = string.gsub('ab', '.', function() return 'X' end, 1); assert(text == 'Xb' and count == 1); local ok, err = pcall(string.gsub, 'a', '.', function() return true end); assert(not ok and err:find('invalid replacement value', 1, true)); coroutine.wrap(function() assert(coroutine.isyieldable()); local result = string.gsub('a', '.', function() assert(not coroutine.isyieldable()); local yielded, message = pcall(coroutine.yield); assert(not yielded and message:find('C-call boundary', 1, true)); return 'b' end); assert(result == 'b' and coroutine.isyieldable()) end)()",
        ])
        .output()
        .expect("execute deep string.gsub callbacks");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_ipairs_index_metamethods_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function descend(n) local proxy = setmetatable({}, {__index = function(_, key) if key ~= 1 then return nil end; if n == 0 then return 1 end; return descend(n - 1) + 1, 'ignored' end}); for index, value in ipairs(proxy) do assert(index == 1); return value end end; assert(descend(5000) == 5001); local fallback = setmetatable({}, {__index = function(_, key) if key <= 2 then return key * 3 end end}); local proxy = setmetatable({}, {__index = fallback}); local result = {}; for index, value in ipairs(proxy) do result[index] = value end; assert(result[1] == 3 and result[2] == 6 and result[3] == nil); local co = coroutine.wrap(function() local p = setmetatable({}, {__index = function(_, key) if key == 1 then coroutine.yield('paused'); return 9 end end}); for _, value in ipairs(p) do return value end end); assert(co() == 'paused' and co() == 9)",
        ])
        .output()
        .expect("execute deep ipairs __index metamethods");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_gsub_table_index_callbacks_use_vm_frames() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "local function descend(n) if n == 0 then return 'done' end; local replacement = setmetatable({}, {__index = function() return descend(n - 1) end}); return (string.gsub('x', '.', replacement)) end; assert(descend(3000) == 'done'); local replacement = setmetatable({a = 'X'}, {__index = function(_, key) collectgarbage(); if key == 'b' then return 7, 'ignored' end; return false end}); local text, count = string.gsub('abc', '(.)', replacement); assert(text == 'X7c' and count == 3); local bad = setmetatable({}, {__index = function() return {} end}); local ok, message = pcall(string.gsub, 'a', '.', bad); assert(not ok and message:find('invalid replacement value', 1, true)); local co = coroutine.wrap(function() local table_value = setmetatable({}, {__index = function() assert(coroutine.isyieldable()); coroutine.yield('paused'); return 'R' end}); return (string.gsub('a', '.', table_value)) end); assert(co() == 'paused' and co() == 'R')",
        ])
        .output()
        .expect("execute deep gsub table __index callbacks");
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_require_loaders_use_vm_frames_and_first_result() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "package.preload.m0 = function() return 0 end; for i = 1, 3000 do local previous = 'm' .. (i - 1); package.preload['m' .. i] = function() return require(previous) + 1 end end; assert(require('m3000') == 3000); package.preload.multiple = function() return 7, 8 end; assert(require('multiple') == 7 and package.loaded.multiple == 7)",
        ])
        .output()
        .expect("execute require VM stack regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn official_metamethod_and_coroutine_cases_pass() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    for script in ["events.lua", "coroutine.lua"] {
        let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
            .arg(script)
            .current_dir(&suite)
            .output()
            .unwrap_or_else(|error| panic!("execute {script}: {error}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stderr.is_empty() && stdout.contains("testing"),
            "{script} failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

#[test]
fn syntax_and_error_values_follow_lua() {
    let script = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/syntax_diagnostics.lua");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .arg(script)
        .output()
        .expect("execute syntax regression");
    assert!(
        output.status.success() && String::from_utf8_lossy(&output.stdout).trim() == "OK",
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn hex_integer_strings_wrap_like_lua_integers() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "assert(math.type(tonumber('0x1000000000000000000000000000000')) == 'integer'); assert(tonumber('0x1000000000000000000000000000000') == 0); assert(tonumber('-0xffffffffffffffff') == 1)",
        ])
        .output()
        .expect("execute hexadecimal conversion regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn numeric_conversions_preserve_lua_number_types() {
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args([
            "-e",
            "assert(tonumber('+ 0.01') == nil); assert(tonumber('inf') == nil); assert(tonumber('0x') == nil); assert(math.type(-4.0 % 3) == 'float'); assert(math.mininteger % -1 == 0); assert(math.ult(2, -1) and not math.ult(-1, 2)); assert(math.type(math.fmod(3.0, 2)) == 'float'); assert(not pcall(rawset, {}, 0/0, 1)); assert(table.unpack({42}, nil, nil) == 42)",
        ])
        .output()
        .expect("execute numeric conversion regression");
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn official_math_bitwise_and_io_cases_pass() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    for script in ["math.lua", "bitwise.lua", "files.lua"] {
        let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
            .args(["-e", "_soft=true; _port=true", script])
            .current_dir(&suite)
            .output()
            .unwrap_or_else(|error| panic!("execute {script}: {error}"));
        assert!(
            output.status.success() && output.stderr.is_empty(),
            "{script} failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn official_errors_pass_without_soft_mode() {
    let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/official/lua-5.3.4-tests");
    let output = Command::new(env!("CARGO_BIN_EXE_luaae"))
        .args(["-e", "_port=true", "errors.lua"])
        .current_dir(&suite)
        .output()
        .expect("execute official errors.lua");
    assert!(
        output.status.success()
            && output.stderr.is_empty()
            && String::from_utf8_lossy(&output.stdout).contains("OK"),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
