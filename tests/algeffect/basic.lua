local seen = {}

handle
    local x = perform Read("answer")
    seen[#seen + 1] = x
    perform Write(x + 1)
    seen[#seen + 1] = "done"
with Read(key, resume)
    assert(key == "answer")
    resume(41)
with Write(value, resume)
    seen[#seen + 1] = value
    resume()
end

assert(#seen == 3)
assert(seen[1] == 41 and seen[2] == 42 and seen[3] == "done")
print("OK")
