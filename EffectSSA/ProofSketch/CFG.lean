module

public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Dominance

public import Std.Data.HashMap

/-!
# ContextCFG

A `ContextCFG n` models a CFG (control flow graph) with up to `n` named holes,
making it a multi-context.
-/
@[expose] public section
namespace EffectSSA.ProofSketch

/-!
## CFG Types
-/
section Types

structure BlockId where
  id : String
deriving Hashable, DecidableEq

def BlockContext := List BlockId

axiom TerminatorOp : Type

structure Block (n : Nat) where
  code : MultiContext n
  term : TerminatorOp

/--
`ContextCFG n` is a control-flow graph with `n` holes.
-/
structure ContextCFG n where
  blocks : Std.HashMap BlockId (Block n)
  entryId : BlockId
  entryId_mem_blocks : entryId ∈ blocks

abbrev ProgramCFG := ContextCFG 0

end Types

/-!
## TerminatorOp API
-/
namespace TerminatorOp

axiom canJumpTo : TerminatorOp → BlockId → Bool
axiom isReturn : TerminatorOp → Bool

end TerminatorOp

/-!
## ContextCFG API
-/
namespace ContextCFG
variable {C : ContextCFG n}

attribute [simp, grind .] entryId_mem_blocks

/-! ### BlockRef -/
section BlockRef

abbrev BlockRef (C : ContextCFG n) := { b : BlockId // b ∈ C.blocks }
abbrev entry (C : ContextCFG n) : C.BlockRef :=
  ⟨C.entryId, C.entryId_mem_blocks⟩

abbrev BlockRef.get (b : C.BlockRef) : Block n :=
  C.blocks[b.val]'b.property

end BlockRef

/-! ### Completeness -/
section Completeness

def Complete (C : ContextCFG n) : Prop :=
  ∀ h : Hole n, ∃ b ∈ C.blocks.values, .inr h ∈ b.code

end Completeness

/-! ### WellFormedness -/
section WellFormedness
variable {C : ContextCFG n}

instance : HasDominance (C.BlockRef) where
  entry := C.entry
  cfg a b := a.get.term.canJumpTo b.val
  isExit b := b.get.term.isReturn

end WellFormedness

/-! ### Plug -/
section Plug

def plug (C : ContextCFG n) (I : Pattern n) : ProgramCFG :=
  { C with
    blocks := C.blocks.map fun _ block => { block with
      code := block.code.plug I
    }
    entryId_mem_blocks := by simp
  }

end Plug



end ContextCFG
