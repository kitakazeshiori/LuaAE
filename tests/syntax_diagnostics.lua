local source = [[
  local a = {4

]]
local function_, message = load(source)
assert(function_ == nil)
assert(message:match('^%[string ".*"%]:3: .- near <eof>$'), message)

local invalid_return = load("return;;")
assert(invalid_return == nil)

local invalid_symbol, symbol_message = load("*a = 123")
assert(invalid_symbol == nil and symbol_message:find("unexpected symbol", 1, true))
for _, source in ipairs({"while << do end", "for >> do end"}) do
  local _, message = load(source)
  local operator = source:match("([<>][<>])")
  assert(message:find("near '" .. operator .. "'", 1, true))
end
local _, control_message = load("a\1a = 1")
assert(control_message:find([[near '<\1>']], 1, true))
local _, high_byte_message = load(string.char(255) .. "a = 1")
assert(high_byte_message:find([[near '<\255>']], 1, true))
local _, deep_message = load("local a; a=" .. string.rep("{", 201) .. "0" .. string.rep("}", 201))
assert(deep_message:find("too many C levels", 1, true))
local _, blocks_message = load(string.rep("do ", 201) .. string.rep(" end", 201))
assert(blocks_message:find("too many C levels", 1, true))
for _, operator in ipairs({"..", "^"}) do
  local _, message = load("local a; a=" .. string.rep("a" .. operator, 201) .. "a")
  assert(message:find("too many C levels", 1, true))
end
local _, register_message = load("a=f(x" .. string.rep(",x", 260) .. ")")
assert(register_message:find("too many registers", 1, true))
local names = {}
for index = 1, 300 do names[index] = "a" .. index end
local _, locals_message = load("function foo() local " .. table.concat(names, ",") .. " end")
assert(locals_message:find("too many local variables", 1, true))
assert(math.log(8, 2) == 3)
local whole, fraction = math.modf(1/0)
assert(whole == 1/0 and fraction == 0 and math.type(fraction) == "float")
assert(1 // 0.0 == 1 / 0)
assert(math.mininteger // -1 == math.mininteger)
assert(math.maxinteger < math.mininteger * -1.0)
assert(" -0xa " + 1 == -9)

local invalid_escape, escape_message = load([[return "abc\x"]])
assert(invalid_escape == nil and escape_message:find([[\x"]], 1, true))
local invalid_hex, hex_message = load([[return "\xr"]])
assert(invalid_hex == nil and hex_message:find([[\xr']], 1, true))
local invalid_unknown, unknown_message = load([[return "\g"]])
assert(invalid_unknown == nil and unknown_message:find([[\g']], 1, true))
local invalid_unicode, unicode_message = load([[return "abc\u{110000}"]])
assert(invalid_unicode == nil and unicode_message:find([[abc\u{110000']], 1, true))
for _, source in ipairs({"for x do", "x:call"}) do
  local invalid, message = load(source)
  assert(invalid == nil and message:find("expected", 1, true))
end

local file = io.input()
local ok_math, math_message = pcall(math.sin, file)
assert(not ok_math and math_message:find("(number expected, got FILE*)", 1, true))
local named = setmetatable({}, {__name = "My Type"})
local ok_input, input_message = pcall(io.input, named)
assert(not ok_input and input_message:find("(FILE* expected, got My Type)", 1, true))
local ok_write, write_message = pcall(io.write, {})
assert(not ok_write and write_message:find("io.write", 1, true))
local ok_collect, collect_message = pcall(collectgarbage, {})
assert(not ok_collect and collect_message:find("collectgarbage", 1, true))
local ok_option, option_message = pcall(collectgarbage, "nooption")
assert(not ok_option and option_message:find("invalid option", 1, true))
local ok_gc, gc_message = pcall(getmetatable(io.stdin).__gc)
assert(not ok_gc and gc_message:find("no value", 1, true))
local receiver = setmetatable({}, {__index = string})
local ok_self, self_message = pcall(function() receiver:sub() end)
assert(not ok_self and self_message:find("bad self", 1, true))
local ok_method_arg, method_arg_message = pcall(function() return ("a"):sub{} end)
assert(not ok_method_arg and method_arg_message:find("#1", 1, true))
for _, name in ipairs({"@" .. string.rep("x", 70), "=" .. string.rep("x", 70), string.rep("x", 70)}) do
  local _, message = load("x", name)
  local source = message:match("^([^:]*):")
  assert(#source <= 59)
end
local stripped = assert(load(string.dump(function(value) return value + 1 end, true)))
local ok_stripped, stripped_message = pcall(stripped, {})
assert(not ok_stripped and stripped_message:match("^%?:%-1:"))
local multiline = assert(load("local a\n for i=1,'a' do\n end"))
local ok_line, line_message = pcall(multiline)
assert(not ok_line and line_message:match(":2:"))
local function first() error("boom", 2) end
local function second() first() end
local ok_level, level_message = pcall(second)
assert(not ok_level and level_message:match(":%d+: boom"))

local ok, error_value = pcall(error)
assert(not ok and error_value == nil)
local ok_assert, assert_message = pcall(assert, false, "X")
assert(not ok_assert and assert_message == "X")
local ok_empty_assert, empty_assert_message = pcall(assert)
assert(not ok_empty_assert and empty_assert_message:find("value expected", 1, true))
print("OK")
