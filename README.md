# Lean 4 Metamath verifier

This is a straightforward verifier for [Metamath](http://us.metamath.org/) files written in [Lean 4](https://github.com/leanprover/lean4/), a dependently typed functional programming language. As of this writing it will compile [`set.mm`](https://github.com/metamath/set.mm) in around 10 seconds.

To compile the verifier, you need to acquire lean, and it is recommended to use [`elan`](https://github.com/leanprover/elan). Once you have it, you should be able to run

```
lake build
```

and it will produce the binary as `.lake/build/bin/mm-lean4`, which can be run as:

```bash
lake exe mm-lean4 path/to/set.mm
# or
.lake/build/bin/mm-lean4 path/to/set.mm
```

to compile `set.mm` in the current folder.
