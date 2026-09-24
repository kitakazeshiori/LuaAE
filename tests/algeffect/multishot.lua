local paths = {}

handle
    local left = perform Choose("left")
    local right = perform Choose("right")
    paths[#paths + 1] = left .. right
with Choose(label, resume)
    if label == "left" then
        resume("A")
        resume("B")
    else
        resume("1")
        resume("2")
    end
end

assert(#paths == 4)
assert(paths[1] == "A1" and paths[2] == "A2")
assert(paths[3] == "B1" and paths[4] == "B2")
print("OK")
