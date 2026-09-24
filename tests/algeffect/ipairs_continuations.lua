local results = {}
local proxy = setmetatable({}, {
    __index = function(_, key)
        return perform Lookup(key)
    end,
})

handle
    local iterator, state, key = ipairs(proxy)
    local index, value = iterator(state, key)
    results[#results + 1] = {index, value}
with Lookup(key, resume)
    assert(key == 1)
    collectgarbage()
    resume("first")
    resume("second")
end

assert(results[1][1] == 1 and results[1][2] == "first")
assert(results[2][1] == 1 and results[2][2] == "second")
print("OK")
