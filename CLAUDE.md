# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
lake build              # Build the entire project
lake build EffectSSA    # Build the main library target
```

The project uses Lake (Lean 4 package manager) with Mathlib v4.29.0-rc4 as its primary dependency.

To check a single file, open it in an editor with the Lean 4 LSP, or use `lake build` which will report errors across the project.

## Project Overview

**EffectSSA** is a Lean 4 formalization of a type system and semantics for programs with explicit memory effects tracked via *effect traces*. The central idea is that memory operations (load/store/alloc/free) can either hide effects implicitly or expose them explicitly through linear *effect* variables that carry a `Trace`.

## Architecture

### Key Abstraction Layers

1. **Assumptions** (`Assumptions/`) — Abstract interfaces, not proofs:
   - `MemorySignature.lean` — `Ptr`, `DVal : DType → Type`
   - `MemoryModel.lean` — `read`, `LegalTrace`, `Compat` (all with `Decidable` instances)
   - `LawfulMemoryModel.lean` — Equational laws on the model
   - `Compat.lean` — The `⌣` (compatible) relation typeclass

2. **Types** (`Types/`) — The type system:
   - `Basic.lean` — `Ty.Typ`: three base kinds: `ptr`, `eff`, `data d`
   - `Context/Basic.lean` — `Context τ`: a snoc-list of `Option Typ`, indexed by de Bruijn position; key ops: `<:` (snoc), `eraseVar`, `take`, `drop`, `isUnrestricted`
   - `Context/IsDerivedFrom.lean` — `IsDerivedFrom` relation between contexts
   - `WellTyped.lean` — `Instruction.WellTyped Γ i Γ'` typing judgment

3. **Syntax** (`Syntax/`) — Program representation:
   - `Untyped/Basic.lean` — `Instruction τ` and `InstructionSeq τ`; instructions are either *implicit* (`loadI`, `storeI`, `allocI`, `freeI`) or *explicit/Effect-SSA* (`loadE`, `storeE`, `allocE`, `freeE`), plus `split`, `merge`, `createEff`, `consumeEff`
   - `Untyped/Var.lean` — De Bruijn variable operations
   - `Typed/` — Typed variants and substitution

4. **Trace** (`Trace/`) — Events and their composition:
   - `Defs.lean` — `Event τ`, `ClockedEvent τ c`, `Trace τ` (includes `isUB : Bool` and pairwise compatibility proof), `TraceZipper`
   - `SplitMerge.lean` — How traces split and merge for effect variable tracking
   - `Interleave.lean` — Event interleaving/reordering

5. **Semantics** (`Semantics/`) — Execution:
   - `Environment.lean` — `Ty.TVal : Typ → Type` maps `ptr→Ptr`, `eff→Trace`, `data d→DVal d`; `Environment τ` maps de Bruijn vars to values
   - `ExecM.lean` — State monad carrying `Environment × Trace`
   - `Program.lean` — `Instruction.execM` executes one instruction; whole-program semantics by composition
   - `Equiv/` — Program equivalence (in progress)

6. **ITC** (`ITC/`) — Interval Temporal Calculus stubs for clock/concurrency model

## Proof Style

Proofs should be **succinct**. Use `grind` and `simp` aggressively — if a goal closes with either, don't write a manual proof.

For every lemma, ask: *should this be a `@[simp]` or `@[grind]` lemma?* Tag it if yes. Simp/grind lemmas should be oriented so the RHS is simpler than the LHS.

If a proof grows beyond a few lines: identify the missing intermediate lemma,
prove that (tagged `@[grind]` if appropriate),
then use it to shorten the original proof.

After finishing any proof, check if it can be shortened without sacrificing readability.
In particular:

- If a proof is simp followed by grind, see if just grind works.
- Prefer `split` over the Mathlib-specific `split_ifs`, but recall that grind will split automatically
- If both branches of an inductive proof can be solved by grind, use the `induction ... <;> grind`
   pattern; this is preferable over spelling out two distinct proofs even if one branch could be solved
   by a less powerful tactic


### Important Design Choices

- Variables use **de Bruijn indices**; the context `Context τ` is a snoc-list so index 0 is the most recent binding.
- **Linearity** is enforced via `eraseVar`: consuming an effect variable removes it from the context. `isUnrestricted` checks no effect variables remain.
- Implicit instructions (e.g., `loadI`) require an unrestricted context entry for the effect, while explicit instructions (e.g., `loadE`) consume a dedicated `eff`-typed variable.
- `Trace τ` bundles events with a `Clock` and a proof that all events are pairwise compatible (`Compat`); appending an event (`consLegal`) checks legality against the existing trace.
