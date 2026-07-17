module

public import EffectSSA.ProofSketch.MultiContext
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

axiom Term.denote : Term → ITree InterpEff (Branch ⊕ ReturnVals)

noncomputable
def Block.denote (b : Block n) (bId : BlockId) (args : List Val) :
    ITree OpaqueCtxEff (Branch ⊕ ReturnVals) := do
  unless b.args.length = args.length do
    raiseError s!"Block {bId} expected {b.args.length} arguments, but got {args.length}"
  (b.args.zip args).forM pushVar.uncurry
                -- ^^ push block arguments to the local stack
  liftM <| b.code.denote -- denote the instructions that make up the block
  liftM <| b.term.denote -- denote the block terminator

noncomputable
def ContextCFG.denote (C : ContextCFG n) : ITree OpaqueCtxEff ReturnVals :=
  ITree.iter step ⟨C.entryId, []⟩
where
  step := fun (⟨bId, args⟩ : Branch) => do
    let some b := C.blocks[bId]? | raiseError s!"Missing Block: {bId}"
    b.denote bId args

noncomputable
def ContextCFG.interp (C : ContextCFG n) (f : Hole n → ITree (ErrUB ⊕ InstEff) Unit) :
    (ITree (SideEff ⊕ ErrUB)) ReturnVals := do
  C.denote |> interpAll (f · |>.lift)

noncomputable
def ProgramCFG.interp (P : ProgramCFG) : (ITree (SideEff ⊕ ErrUB)) ReturnVals :=
  ContextCFG.interp P Hole.elim0

/-!
## ContextCFG API
-/
namespace ContextCFG
variable {C : ContextCFG n}

attribute [simp, grind .] entryId_mem_blocks

/-! ### Plug -/
section Plug

def plug (C : ContextCFG n) (I : Pattern n) : ProgramCFG :=
  { C with
    blocks := C.blocks.map fun _ block => { block with
      code := MultiContext.ofSeq (block.code.plug I)
    }
    entryId_mem_blocks := by simp
  }

end Plug

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

end ContextCFG
