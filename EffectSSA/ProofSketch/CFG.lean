module

public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Dominance
public import EffectSSA.ProofSketch.Effect

public import Std.Data.HashMap

/-!
# ContextCFG

A `ContextCFG n` models a CFG (control flow graph) with up to `n` named holes,
making it a multi-context.
-/
@[expose] public section
namespace EffectSSA.ProofSketch
open ITree

variable {ε : Type} {κε : ε → Type} [Effect ε κε]

/-!
## CFG Types
-/
section Types

structure BlockId where
  toString : String
deriving Hashable, DecidableEq
instance : ToString BlockId where toString := BlockId.toString

def BlockContext := List BlockId

/-- A terminator -/
axiom Term : Type

structure Block (n : Nat) where
  args : List VarId
  code : MultiContext n
  term : Term

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
## Semantics
-/

structure Branch where
  target : BlockId
  args : List Val

structure ReturnVals where
  toList : List Val

axiom Term.denote [ErrUB -< ε] [SideEff -< ε] [LocalEff -< ε] :
    Term → ITree ε (Branch ⊕ ReturnVals)

noncomputable
def ContextCFG.denote (C : ContextCFG n) : ITree (HoleEff ⊕ InstEff ⊕ LocalEff ⊕ SideEff ⊕ ErrUB) ReturnVals :=
  ITree.iter (fun (⟨bId, args⟩ : Branch) => do
    let some b := C.blocks[bId]? | raiseError s!"Missing Block: {bId}"
    unless b.args.length = args.length do
      raiseError s!"Block {bId} expected {b.args.length} arguments, but got {args.length}"
    (b.args.zip args).forM pushVar.uncurry
    -- ^^ push all block arguments to the local stack
    b.code.denote -- denote the instructions that make up the block
    b.term.denote -- denote the block terminator
  ) ⟨C.entryId, []⟩

def Hole.fromId? {n} (h : HoleId) : Option (Hole n) :=
  if hr : h.toNat < n then some ⟨h.toNat, hr⟩ else none

noncomputable
def ContextCFG.interp (C : ContextCFG n) (f : Hole n → ITree (ErrUB ⊕ InstEff) Unit) :
    (ITree (SideEff ⊕ ErrUB)) ReturnVals := do
  let ⟨res, _finalStack⟩ ←
    C.denote
    |> interpHoles (fun holeId => do
        let some (h : Hole n) := Hole.fromId? holeId | raiseError s!"Unknown hole: {holeId}"
        f h
    )
    |> interpInst
    |> interpLocalStack
    |>.run {}
  return res

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

-- instance : HasDominance (C.BlockRef) where
--   entry := C.entry
--   cfg a b := a.get.term.canJumpTo b.val
--   isExit b := b.get.term.isReturn

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
