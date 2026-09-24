local results = {}
local reverse_less = false
local mt = {}

mt.__lt = function(a, b)
    if a.rank == 2 and b.rank == 1 then
        return perform Compare()
    end
    return reverse_less
end

local values = {
    setmetatable({rank = 2}, mt),
    setmetatable({rank = 1}, mt),
}

handle
    table.sort(values)
    results[#results + 1] = values[1].rank .. "," .. values[2].rank
with Compare(resume)
    reverse_less = false
    resume(true)
    reverse_less = true
    resume(false)
end

assert(#results == 2)
assert(results[1] == "2,1")
assert(results[2] == "1,2")
print("OK")
