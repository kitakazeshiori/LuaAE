local results = {}
local replacement = setmetatable({a = "x"}, {
    __index = function(_, key)
        return perform Missing(key)
    end,
})

handle
    local text, count = string.gsub("ab", ".", replacement)
    results[#results + 1] = {text, count}
with Missing(key, resume)
    assert(key == "b")
    collectgarbage()
    resume("A")
    resume("B")
end

assert(results[1][1] == "xA" and results[1][2] == 2)
assert(results[2][1] == "xB" and results[2][2] == 2)
print("OK")
