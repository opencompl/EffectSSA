module

public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Effect

public import ITreeExtras

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

def Hole.fromId? {n} [ErrUB -< ε] (h : HoleId) : ITree ε (Hole n) :=
  if hr : h.toNat < n then
    return ⟨h.toNat, hr⟩
  else
    raiseError s!"Unknown hole: {h}"

abbrev Hole.elim0 : Hole 0 → α := Fin.elim0

noncomputable
def ContextCFG.interp (C : ContextCFG n) (f : Hole n → ITree (ErrUB ⊕ InstEff) Unit) :
    (ITree (SideEff ⊕ ErrUB)) ReturnVals := do
  C.denote
  |> interpHoles (Hole.fromId? · >>= f)
  |> interpInst
  |> interpLocalStack

noncomputable
def ProgramCFG.interp (P : ProgramCFG) : (ITree (SideEff ⊕ ErrUB)) ReturnVals :=
  ContextCFG.interp P Hole.elim0


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

/-! ### Plug -/
section Plug

def plug (C : ContextCFG n) (I : Pattern n) : ProgramCFG :=
  { C with
    blocks := C.blocks.map fun _ block => { block with
      code := block.code.plug I
    }
    entryId_mem_blocks := by simp
  }

-- @[simp, grind =] theorem fromId?_zero : Hole.fromId? (n := 0) x = raiseError _ := by
--   simp [Hole.fromId?]

@[simp, grind .]
axiom hasEffect_raiseError [ErrUB -< ε] (e : ε) :
    (raiseError reason : ITree ε α).HasEffect e ↔
      (Subeffect.map (.error reason : ErrUB)).fst = e

/-!
For now, I've specialized the pushVar lemmas to `OpaqueCtxEff`, since I'm not
100% certain how to prove the following, deceptively simple looking, lemmas in
full generality.
-/
section PushVarLemmas

@[simp, grind .]
theorem mayReturn_pushVar {u : PUnit} :
    (pushVar (ε:=OpaqueCtxEff) var value).MayReturn u := by
  sorry

end PushVarLemmas

@[simp, grind =]
theorem Block.denote_hasEffect_hole_iff (b : Block n) (bId : BlockId) (args : List Val) (h : HoleId) :
    (b.denote bId args).HasEffect (.inl h) ↔
      b.args.length = args.length ∧ (b.code.denote).HasEffect (.inl h) := by
  sorry

theorem interpHoles_program (P : ProgramCFG) {f g : HoleId → ITree (ErrUB ⊕ InstEff) Unit} :
    interpHoles f P.denote = interpHoles g P.denote := by
  simp only [interpHoles]
  apply ITree.interpLeft_congr
  intro e he
  exfalso -- there cannot actually be any hole effects in P.denote!
  simp only [denote] at he
  obtain ⟨⟨bId, args⟩, hb⟩ := ITree.hasEffect_iter he
  grind [denote.step]

theorem interp_plug {C : ContextCFG n} {I : Pattern n} :
    (C.plug I).interp = C.interp (liftM <| I[·].denote) := by
  simp only [ProgramCFG.interp, interp, Pattern.getElem_hole]
  congr 2
  rw [denote]

  stop

  generalize ht : denote (C.plug I) = t


  simp only [interpHoles, ITree.interpFirst, denote]
  rw [ITree.interpM_iter', ITree.interpM_iter']
  · sorry
  · sorry
  · intro b


  stop

  simp only [ContextCFG.interp, ProgramCFG.interp, bind_pure_comp]
  simp only [fromId?_zero, denote, Pattern.getElem_hole]
  simp only [plug, Std.HashMap.getElem?_map]
  congr 4
  -- TODO: figure out how to do a proof by bisimulation in the ITree library
  cases C.blocks[x.target]?
  simp [interpHoles, denote, ITree.interpLeft]
  simp only [ITree.interp_iter']

  -- simp only [ITree.interp, bind_pure_comp]


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
