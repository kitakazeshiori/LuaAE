# LuaAE: Lua with Algebraic Effects

LuaAE is a lightweight, embeddable bytecode virtual machine written entirely in Rust, implementing a fully-featured dialect of Lua, closely resembling Lua 5.1 (with some 5.2, 5.3 features).

LuaAE has been tested on official Lua 5.1 Test Suite and passed most of its modules.

Try the online [LuaAE interpreter](https://kitakazeshiori.github.io/LuaAE/webpage/).

### Features

- Keyword `continue`;
- Operator `!=` (same as `~=`);
- Algebraic Effects.

## 0. Philosophy

### Why Algebraic Effects？

While features like `async/await`, generators, and standard exceptions provide mechanisms for control flow, they often come with severe architectural trade-offs. Algebraic Effects solve these fundamental problems by offering a unified, first-class model for non-local control flow.

In traditional programming, calling a side-effecting function (like `io.open()`) hardcodes the implementation into your business logic. With Algebraic Effects, you only perform the intent (`perform ReadFile(...)`). The implementation is delegated to the `handle` block.

This helps debugging, for example, instantly swap a real database handler with a mock handler in the test suite without changing a single line of the core business logic, or when a  contextual execution is needed, the exact same function can run asynchronously in a web server environment, synchronously in a CLI script, or completely mocked in a CI environment - all determined by the outer `handle` block.

Languages with `async/await` suffer from the "Colored Function" problem: an `async` function can only be called by another `async` function. This infects the entire call stack, requiring you to rewrite large portions of your codebase just to make one deep function non-blocking. Algebraic effects are "colorless". You can trigger a `perform` deep inside an array mapping function, a sorting algorithm, or any pure-looking function. The suspension bubbles up seamlessly to the nearest handler without requiring `async` keywords or altering intermediate function signatures.

### Why Multi-shot?

Every time `resume(value)` is called, the VM duplicates the suspended stack slices and resumes execution from the exact point of the `perform`, branching the universe of your program into different paths. For example, if a database transaction deep in the call stack fails due to a conflict, the handler can simply invoke `resume()` again to replay the transaction from the exact moment of failure.

This also provides the capability for Probabilistic Programming: you can evaluate a function over a distribution of values. `perform FlipCoin()` might trigger a handler that calls `resume(true)` and then `resume(false)`, computing the probabilities of both branching outcomes. 

## 1. Algebraic Effects

Algebraic Effects provide a structured, composable, and first-class mechanism for non-local control flow.

Unlike traditional exception handling (`try/catch`), which unwinds the execution stack permanently, algebraic effects capture the delimited continuation (the remaining computation within the handling scope). This allows effect handlers to resume the computation from the exact point where the effect was performed, optionally passing a value back.

In LuaAE, this mechanism enables elegant implementations of advanced programming patterns—such as async/await, generators, state management, dependency injection, and cooperative multitasking—directly inside user space without altering the global runtime architecture.

Search the web for more informations about Algebraic Effects.

## 2. Syntax

LuaAE introduces three new contextual keywords to the grammar. Below is the formal syntax notation.

### perform
The `perform` keyword triggers an effect. It can be used either as an expression (returning values upon resumption) or as a standalone statement.

```lex
expression ::= ... | 'perform' IDENTIFIER '(' [expression_list] ')'
statement  ::= ... | 'perform' IDENTIFIER '(' [expression_list] ')'
```

For example:

```lua
-- As a statement
perform Log("Application started")

-- As an expression capturing return values
local data = perform FetchData("https://api.example.com")

```

### handle ... with ... 

A `handle` block defines a delimited scope for monitoring and intercepting effects. It wraps a structural block of code (the *thunk*) and attaches one or more `with` branches to handle specific effects.

```lex
handle_statement ::= 'handle' 
                         block 
                     ('with' IDENTIFIER '(' [parameter_list] ')' block)+ 
                     'end'

```

For example:

```lua
handle
    local content = perform ReadFile("config.json")
    perform WriteLog("File content read successfully")
    return content
with ReadFile(filename, k)
    -- 'k' is the continuation object passed as the trailing argument
    print("Intercepted ReadFile for: " .. filename)
    k("mocked file content") -- Resumes the handle thunk
with WriteLog(message, resume)
    print("[LOG] " .. message)
    resume() -- Resumes with no value
end
```

> We recommend the continuation be named `resume` for a clearer annotation.

## 3. Semantics

### perform

When a `perform` instruction is encountered at runtime, the Virtual Machine carries out:

1. The VM walks down the internal `handler_stack` starting from the top (the most deeply nested handler) to find an active handler whose `effect_id` matches the performed effect string.

2. If a matching handler is found, the VM captures the entire execution context *delimited* by that handler. This includes freezing the current slice of the call stack, data stack, and handler stack.

3. The execution of the thunk is suspended. The frozen state is wrapped into a first-class `Continuation` object. The VM then packages the arguments provided to `perform` along with the `Continuation` object (passed as the final argument) and transfers control to the handler closure.

### handle / with

The `handle` keyword establishes a dynamic barrier.

- Upon entry, all closures defined within the associated `with` branches are instantiated (via `OpCode::MakeClosure`) and pushed onto the `handler_stack` (via `OpCode::PushHandler`).

- Branches are evaluated sequentially during compilation. Multiple `with` blocks attached to a single `handle` statement allow a single block of code to be guarded against distinct types of effects simultaneously.

> When the code inside the `handle` thunk completes successfully, or when the scope is exited via a `return`, the VM automatically discards the registered handlers from the stack (`OpCode::PopHandler`).

### Continuation

The continuation represents the "rest of the computation" inside the `handle` block.

- The continuation is always supplied to your `with` block as the **last parameter** after any explicit arguments declared in the effect signature.

- Continuations are invoked like standard functions (e.g., `resume(value)`). When called, the VM duplicates the frozen stack slices, adjusts stack base pointers to map to the new activation area, and injects the arguments passed into `resume()` back into the data stack as the result of the original `perform` expression.

- **Multi-Shot Resumption:** Because stack states are cloned upon invocation, a continuation can be called **multiple times** (multi-shot continuations) or discarded entirely to abort the computation early.

## 4. Scoping

### Shadowing

Effects follow dynamic scoping rules identical to exception bubble-up patterns. If multiple nested `handle` blocks catch the same effect, the **innermost** active handler takes precedence.

> A handler becomes temporarily inactive (`is_active = false`) while executing its own `with` body. This prevents infinite cycles if a handler performs the same effect it is designed to catch; such an effect will naturally bubble up to the next outer handler.

### Multi-Return

LuaAE preserves Lua's native support for multiple values across the effect boundary. A `perform` call can return multiple values if the continuation resubmits them (e.g., `resume(val1, val2)`).

> The compiler generates `OpCode::AdjustStack` boundaries to truncate or pad incoming multiple return values based on assignment configurations, maintaining total stability in the data stack alignment.

## 5. Security

### C-Call Boundary

Algebraic effects cannot yield control across a C-Call boundary. Performing an effect inside a standard library abstraction implemented natively in the host engine (such as `pcall`, `xpcall`, `table.sort`) will trigger a runtime error.

> Use the native language constructs (`handle/with`) for structured error interception instead of legacy `pcall` primitives if effect propagation is anticipated.

### Unhandled Effects

If a `perform` invocation fails to locate a matching handler anywhere on the execution chain, execution halts immediately, with the error message like:

```text
Uncaught Error: unhandled effect 'ToString'
stack traceback:
        @example1.lae:7 in function
        @example1.lae:12 in function
        @example1.lae:18 in function
        @example1.lae:23 in function
        @example1.lae:29 in main chunk
```

### Loop Context

When jumps such as `break` or `continue` are executed within loops inside a `handle` block:

- Jumps safely unwind local block variables (`OpCode::CloseLocals`).
- Iteration tracking tables for numeric or generic loops (`for`) are kept clean, ensuring variables captured in continuations reflect distinct iteration states via precise `OpCode::DetachUpvals` checkpoints.

## 6. Samples

### One-shot

```lua
-- Define the core orchestration logic completely free of side effects
local function processOrder(orderId)
    perform Log("Processing order #" .. orderId)
    
    local inventoryExists = perform CheckInventory(orderId)
    if not inventoryExists then
        perform Log("Order failed: Out of stock")
        return false
    end
    
    local paymentSuccess = perform ChargeCard(orderId, 150.00)
    if paymentSuccess then
        perform Log("Order completed successfully")
        return true
    else
        perform Log("Order failed: Payment declined")
        return false
    end
end

-- Wire up handlers at the boundaries of the application
handle
    local success = processOrder("ORD-90210")
    print("Final result: ", success)
with CheckInventory(id, k)
    -- Simulate async inventory database check
    k(true) 
with ChargeCard(id, amount, k)
    -- Simulate external payment gateway integration
    k(true)
with Log(msg, k)
    -- Centralized streaming logger
    print("[SYSTEM LOG]: " .. msg)
    k() -- Continue without returning a value
end
```

### Multishot (with some language features tested)

```lua
counter = 100
proxy = {}

setmetatable(proxy, {
    __index = function(self, key)
        counter = counter + 1
        return perform KeyNotFound(key) .. "_" .. perform ToString(counter)
    end
})

function f()
    local a = proxy.first
    local b = proxy.second
    return a .. " & " .. b
end

handle
    result = f()
    print(result)
with KeyNotFound(key, resume)
    print("Handling " .. key)
    if key == "first" then
        resume("Alpha")
        resume("Beta")
    elseif key == "second" then
        resume("One")
        resume("Two")
    end
with ToString(arg, resume)
    resume('tostring(' .. tostring(arg) .. ')')
end
print("Final result is ".. result)
```

## About

* Lua was chosen for its relatively simple standard, which makes it easier to implement. Its syntax is clean, intuitive, and concise. Furthermore, it is not an overly obscure language and boasts its own established ecosystem.

* While it passes the majority of the test suite (with minor modifications made to the official Lua 5.1 test suite), LuaAE should still be considered a "toy" language.

* Algebraic effects are not a new concept; languages like Koka have already implemented them. However, languages supporting **multi-shot continuations** remain rare. This project is an attempt to materialize this concept—it is more of an "academic artifact" than a production-ready tool.

* The goal of this project is not to create an "upgraded Lua," a "JavaScript replacement," or a "next-generation programming language." As mentioned above, multi-shot continuations are currently largely academic (e.g., probabilistic programming) and have limited utility in practical business development. Critical questions remain: If an open file handle is resumed multiple times and distributed across different "branches" of the program, what happens? Will the file handle be closed multiple times? These are vast and complex issues. Regrettably, LuaAE (at least in its first iteration) does not offer a universal solution for these problems. This is why you may notice that the implementation of system resources (such as the `io` module) in LuaAE feels somewhat rudimentary or rushed.

* Please note that while **parts of the code were assisted by AI**, the architecture, design, code merging, and testing processes were entirely performed and managed by me. In my view, this represents the future paradigm of software development.


