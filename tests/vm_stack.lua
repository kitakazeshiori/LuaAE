local function descend(n)
  if n == 0 then return 0 end
  return descend(n - 1) + 1
end
assert(descend(20000) == 20000)

local index_mt = {}
index_mt.__index = function(t, key)
  if t.n == 0 then return 0 end
  return setmetatable({n = t.n - 1}, index_mt)[key] + 1
end
assert(setmetatable({n = 20000}, index_mt).x == 20000)

local add_mt = {}
add_mt.__add = function(a, b)
  if a.n == 0 then return b end
  return setmetatable({n = a.n - 1}, add_mt) + b + 1
end
assert((setmetatable({n = 20000}, add_mt) + 0) == 20000)

local function captures_environment() return _G end
local id = debug.upvalueid(captures_environment, 1)
assert(type(id) == "userdata")
assert(id == debug.upvalueid(captures_environment, 1))
local another = 1
assert(id ~= debug.upvalueid(function() return another end, 1))
local ok, message = pcall(debug.setuservalue, id, {})
assert(not ok and message:find("light userdata", 1, true))
collectgarbage("collect")
assert(id == debug.upvalueid(captures_environment, 1))

print("OK")
