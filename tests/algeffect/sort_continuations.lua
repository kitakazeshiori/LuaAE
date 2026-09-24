local results = {}
local values = {2, 1}
local reverse_less = false

handle
    table.sort(values, function(a, b)
        if a == 2 and b == 1 then
            return perform Compare()
        end
        return reverse_less
    end)
    results[#results + 1] = values[1] .. "," .. values[2]
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
