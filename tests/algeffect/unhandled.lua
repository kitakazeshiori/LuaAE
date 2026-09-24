local function middle()
    return perform Missing("payload")
end

local function outer()
    return middle()
end

outer()
