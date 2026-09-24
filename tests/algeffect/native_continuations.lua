package.preload.effectful = function()
    return {answer = perform Choice()}
end

local modules = {}
handle
    local module = require("effectful")
    modules[#modules + 1] = module.answer
with Choice(resume)
    resume("first")
    resume("second")
end

assert(modules[1] == "first" and modules[2] == "second")
assert(package.loaded.effectful.answer == "second")

local protected = {}
handle
    local ok, value = pcall(function()
        return perform Protected()
    end)
    assert(ok)
    protected[#protected + 1] = value
with Protected(resume)
    resume(11)
    resume(22)
end

assert(protected[1] == 11 and protected[2] == 22)

local extended = {}
handle
    local ok, value = xpcall(function()
        return perform Extended()
    end, function(message)
        return message
    end)
    assert(ok)
    extended[#extended + 1] = value
with Extended(resume)
    resume("left")
    resume("right")
end

assert(extended[1] == "left" and extended[2] == "right")

print("OK")
