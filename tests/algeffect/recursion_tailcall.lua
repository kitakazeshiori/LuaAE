local function sum(n, acc)
    if n == 0 then return acc end
    if n == 25 then
        acc = acc + perform Bonus(n)
    end
    return sum(n - 1, acc + n)
end

local result
handle
    result = sum(100, 0)
with Bonus(n, resume)
    assert(n == 25)
    resume(1000)
end

assert(result == 6050)
print("OK")
