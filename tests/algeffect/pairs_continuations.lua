local results = {}
local value = setmetatable({}, {
    __pairs = function()
        return perform Iterator()
    end,
})

handle
    local iterator, state, key = pairs(value)
    results[#results + 1] = {iterator, state, key}
with Iterator(resume)
    resume(function() return nil end, "first", 11)
    resume(function() return nil end, "second", 22)
end

assert(#results == 2)
assert(type(results[1][1]) == "function" and results[1][2] == "first" and results[1][3] == 11)
assert(type(results[2][1]) == "function" and results[2][2] == "second" and results[2][3] == 22)
print("OK")
