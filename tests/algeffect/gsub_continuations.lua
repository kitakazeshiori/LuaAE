local callbacks = 0
local results = {}

handle
    local text, count = string.gsub("aa", ".", function()
        callbacks = callbacks + 1
        if callbacks == 2 then
            return perform Replacement()
        end
        return "x"
    end)
    results[#results + 1] = {text, count}
with Replacement(resume)
    collectgarbage()
    resume("A")
    resume("B")
end

assert(results[1][1] == "xA" and results[1][2] == 2)
assert(results[2][1] == "xB" and results[2][2] == 2)
print("OK")
