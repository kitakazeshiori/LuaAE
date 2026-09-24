local saved
local result

handle
    local payload = {marker = "alive"}
    result = (perform Suspend(payload)).marker
with Suspend(payload, resume)
    assert(payload.marker == "alive")
    saved = resume
end

for i = 1, 2000 do
    local garbage = {i, tostring(i), {i * 2}}
end
collectgarbage("collect")
saved({marker = "resumed"})
assert(result == "resumed")
print("OK")
