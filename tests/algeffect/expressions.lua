local log = {}

local proxy = setmetatable({}, {
    __index = function(_, key)
        return perform MissingKey(key)
    end,
    __add = function(a, b)
        return perform Add(a.value, b.value)
    end,
})

handle
    local values = {
        1 + perform Number(),
        proxy.name,
        (setmetatable({value = 8}, getmetatable(proxy)) + {value = 9}),
    }
    log[#log + 1] = table.concat(values, ":")
with Number(resume)
    resume(4)
with MissingKey(key, resume)
    resume("<" .. key .. ">")
with Add(a, b, resume)
    resume(a + b)
end

assert(log[1] == "5:<name>:17")
print("OK")
