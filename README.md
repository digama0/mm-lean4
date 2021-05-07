# Lean 4 Metamath verifier

This is a straightforward verifier for [Metamath](http://us.metamath.org/) files written in [Lean 4](https://github.com/leanprover/lean4/), a new dependently typed functional programming language. As of this writing it will compile [`set.mm`](https://github.com/metamath/set.mm) in around 10 seconds.

To compile the verifier, you need to acquire lean, and it is recommended to use [`elan`](https://github.com/leanprover/elan) for this since Lean 4 is still rapidly changing and this version builds on a nightly release of Lean 4. Once you have it, you should be able to run

```
elan override set leanprover/lean4:nightly
elan update leanprover/lean4:nightly
leanmake bin
```

and it will produce the binary as `build/bin/Metamath`, which can be run as:

```
build/bin/Metamath path/to/set.mm
```

to compile `set.mm` in the current folder.