# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Metamath Lean 4 Verifier Soundness Proof** - A formal verification in Lean 4 that the Metamath proof checker correctly validates mathematical theorems. This is a bottom-up architecture implementing the verifier from first principles, with each phase proving the previous layer correct.

**Key Achievement**: A mathematically sound proof checker implementation with formal soundness theorem (`verify_impl_sound`) connecting runtime behavior to mathematical validity.

# Formalization Rules

- Always prove that which can be proven without using axioms.  No exceptions.
- Build a solid foundation of concretely proven theorems/lemmas (instead of writing proof sketches with sorries and moving on).

# Help

- Consult how-to-lean.md when needing help with Lean formalizations.
- Upgrade how-to-lean.md when learning something new.


## Build & Test Commands

### Build the project
```bash
lake build
```

### Build specific modules
```bash
lake build Metamath.Verify           # Parser implementation
lake build Metamath.KernelClean      # Main soundness proof
lake build Metamath.ParserInvariants # Parser correctness theorems
```

### Check a single file for errors (without building dependencies)
```bash
lean /path/to/file.lean
```

### Run the verifier executable
```bash
lake build validateDB
./.lake/build/bin/validateDB
```

### View build warnings/errors
```bash
lake build 2>&1 | grep -E "^(error|warning):" | head -20
```

## Architecture Overview

### Layer Structure (Bottom-Up)

The project uses a **phased bottom-up architecture** where each layer depends only on lower layers:

**Phase 1: Core Specifications** (`Metamath.Spec`)
- Formal definition of Metamath proof state and validity
- What the verifier should achieve mathematically

**Phase 2: Runtime Implementation** (`Metamath.Verify`)
- Byte-level parser (feed function, feedTokens)
- Database operations (insertHyp, checkHyp)
- Proof checker state machine
- **Critical fact**: Feed processes bytes with error monotonicity (error once set never clears)

**Phase 3: Parser Correctness** (`Metamath.ParserInvariants`)
- **What's proven**: Parser success implies well-formed objects in database
- Float hypothesis structure: size=2, first element is const, second is var
- Float hypothesis uniqueness: no two floats bind same variable
- **Key blocking lemma**: `feedTokens_is_only_float_source` - proves floats can ONLY be added via feedTokens.float case

**Phase 4: Bridge Functions** (`Metamath.Bridge.Basics`)
- Conversion from runtime DB representation to specification frames
- Pattern extraction from Metamath objects

**Phase 5-8: Kernel Soundness** (`Metamath.KernelClean`)
- Stepwise proof that each verifier operation maintains mathematical soundness
- Main theorem: `verify_impl_sound` - proves parser success implies valid theorem

