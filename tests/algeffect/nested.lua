local trace = {}

handle
    handle
        local result = perform Ping("body")
        trace[#trace + 1] = result
    with Ping(value, resume)
        trace[#trace + 1] = "inner:" .. value
        local outer_value = perform Ping("handler")
        resume(outer_value)
    end
with Ping(value, resume)
    trace[#trace + 1] = "outer:" .. value
    resume("routed")
end

assert(#trace == 3)
assert(trace[1] == "inner:body")
assert(trace[2] == "outer:handler")
assert(trace[3] == "routed")
print("OK")
