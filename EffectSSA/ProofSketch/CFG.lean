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
structure Terminator where
  op : TerminatorOp
  successors : List BlockId

structure Block (n : Nat) (BId : Type) where
  insts : MultiContext n
  term : TerminatorOp
  succ : List BId

/--
`ContextCFG n` is a control-flow graph with `n` holes.
-/
structure ContextCFG n where
  blockIds : List BlockId
  blocks : {b // b ∈ blockIds} → (Block n {b // b ∈ blockIds})
  entryId : BlockId
  entryId_mem_blocks : entryId ∈ blockIds

abbrev ProgramCFG := ContextCFG 0

end Types

/-!
## TerminatorOp API
-/
namespace TerminatorOp

axiom isReturn : TerminatorOp → Bool

end TerminatorOp

/-!
## ContextCFG API
-/
namespace ContextCFG
variable {C : ContextCFG n}

/-! ### BlockRef -/
section BlockRef

abbrev BlockRef (C : ContextCFG n) := { b : BlockId // b ∈ C.blockIds }
abbrev entry (C : ContextCFG n) : C.BlockRef :=
  ⟨C.entryId, C.entryId_mem_blocks⟩

abbrev BlockRef.get (b : C.BlockRef) : Block n C.BlockRef :=
  C.blocks b

end BlockRef

/-! ### Completeness -/
section Completeness

def Complete (C : ContextCFG n) : Prop :=
  ∀ h : Hole n, ∃ b : C.BlockRef, .inr h ∈ b.get.insts

end Completeness

/-! ### WellFormedness -/
section WellFormedness
variable {C : ContextCFG n}

instance : HasDominance (C.BlockRef) where
  entry := C.entry
  cfg a b := b ∈ a.get.succ
  isExit b := b.get.term.isReturn

end WellFormedness

/-! ### Plug -/
section Plug

def plug (C : ContextCFG n) (I : Pattern n) : ProgramCFG :=
  { C with blocks := fun b =>
    let block := C.blocks b
    { block with insts := block.insts.plug I }
  }

end Plug



end ContextCFG
