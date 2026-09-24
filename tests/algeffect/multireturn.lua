local a, b, c

handle
    a, b, c = perform Values()
with Values(resume)
    resume("a", nil, "c", "discarded")
end

assert(a == "a" and b == nil and c == "c")

local function pass_through()
    return perform Values()
end

handle
    a, b, c = pass_through()
with Values(resume)
    resume(10, 20, 30)
end

assert(a == 10 and b == 20 and c == 30)
print("OK")
