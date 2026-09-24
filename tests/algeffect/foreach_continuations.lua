local table_value = {11, 22}
local results = {}

handle
    local result = table.foreach(table_value, function(key, value)
        if key == 1 then
            table_value[2] = nil
            return perform Choice(value)
        end
        return value
    end)
    results[#results + 1] = result
with Choice(value, resume)
    assert(value == 11)
    collectgarbage()
    resume(nil)
    resume("early")
end

assert(results[1] == 22 and results[2] == "early")

local indexed = {}
handle
    local result = table.foreachi({7}, function()
        return perform Indexed()
    end)
    indexed[#indexed + 1] = result
with Indexed(resume)
    resume("first")
    resume("second")
end

assert(indexed[1] == "first" and indexed[2] == "second")
print("OK")
