local mt = getmetatable(io.stdout)
local writes = {}

mt.write = function(_, value)
    return perform Write(value)
end

handle
    local result = io.write("payload")
    writes[#writes + 1] = result
with Write(value, resume)
    assert(value == "payload")
    resume("first")
    resume("second")
end

assert(writes[1] == "first" and writes[2] == "second")

local opened = {}
io.open = function(path, mode)
    return perform Open(path, mode)
end

handle
    local result = io.output("target")
    opened[#opened + 1] = result
with Open(path, mode, resume)
    assert(path == "target" and mode == "w")
    resume(io.stdout)
    resume(io.stdout)
end

assert(#opened == 2 and opened[1] == io.stdout and opened[2] == io.stdout)
assert(io.output() == io.stdout)

print("OK")
