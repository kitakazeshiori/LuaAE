# Algebraic effect regression tests

These cases exercise expression and statement effects, multiple return values,
multi-shot continuation branching, nested handler shadowing and forwarding,
captured locals in loops, tail calls, effects inside metamethods, continuation
lifetime across garbage collection, multi-shot effects across require,
protected calls, IO callbacks, load readers, pairs and ipairs metamethods,
table iteration callbacks, and string substitution callbacks (including table
`__index`), plus diagnostics for unhandled effects.

Run them together with the Rust integration harness:

```console
cargo test --test algeffect
```
