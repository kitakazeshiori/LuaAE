local results = {}

local function make_worker(seed)
    local state = seed
    return function(limit)
        for i = 1, limit do
            if i == 2 then
                state = state + perform Step(i, state)
                continue
            end
            if i == 4 then break end
            state = state + i
        end
        return state
    end
end

local worker = make_worker(10)
handle
    results[#results + 1] = worker(5)
with Step(i, state, resume)
    assert(i == 2 and state == 11)
    resume(20)
end

assert(results[1] == 34)
print("OK")
