local calls = 0
local results = {}

local function reader()
    calls = calls + 1
    if calls == 1 then
        return "return "
    end
    if calls == 2 then
        return perform Source()
    end
    return nil
end

handle
    local chunk = assert(load(reader, "=effectful-load"))
    results[#results + 1] = chunk()
with Source(resume)
    collectgarbage()
    resume("11")
    resume("22")
end

assert(results[1] == 11 and results[2] == 22)
print("OK")
