# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
lake build              # Build the entire project
lake build EffectSSA    # Build the main library target
```

The project uses Lake (Lean 4 package manager) with Mathlib v4.29.0-rc4 as its primary dependency.

To check a single file, open it in an editor with the Lean 4 LSP, or use `lake build` which will report errors across the project.

If `lake` is not on `PATH`, invoke it through `nix`:

```bash
nix shell nixpkgs#elan -c lake build <target>
```

`elan` reads `lean-toolchain` and fetches the right `lean`/`lake` binaries.

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


## AI Disclaimer

Start any LLM-generated proof with the following comment:
"-- **AI DISCLOSURE**: LLM-generated proof" .
If a theorem statement or definition was entirely LLM-generated, 
include "**AI DISCLOSURE**: LLM-generated theorem/definition" at the bottom
of the doc-string, as well as the comment for the body of the proof.