module

public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Dominance
public import EffectSSA.ProofSketch.Effect

public import EffectSSA.ProofSketch.ITree.Coe
public import EffectSSA.ProofSketch.ITree.Stub

public import Std.Data.HashMap

/-!
# ContextCFG

A `ContextCFG n` models a CFG (control flow graph) with up to `n` named holes,
making it a multi-context.
-/
@[expose] public section
namespace EffectSSA.ProofSketch
open ITree

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
def Block.denote (b : Block n) (bId : BlockId) (args : List Val) :
    ITree (HoleEff ⊕ₑ InstEff ⊕ₑ LocalEff ⊕ₑ SideEff ⊕ₑ ErrUB) (Branch ⊕ ReturnVals) := do
  unless b.args.length = args.length do
    raiseError s!"Block {bId} expected {b.args.length} arguments, but got {args.length}"
  (b.args.zip args).forM pushVar.uncurry
                -- ^^ push block arguments to the local stack
  b.code.denote -- denote the instructions that make up the block
  b.term.denote -- denote the block terminator

noncomputable
def ContextCFG.denote (C : ContextCFG n) :
    ITree (HoleEff ⊕ₑ InstEff ⊕ₑ LocalEff ⊕ₑ SideEff ⊕ₑ ErrUB) ReturnVals :=
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
def ContextCFG.interp (C : ContextCFG n) (f : Hole n → ITree (ErrUB ⊕ₑ InstEff) Unit) :
    (ITree (SideEff ⊕ₑ ErrUB)) ReturnVals := do
  C.denote
  |> interpHoles (Hole.fromId? · >>= f)
  |> interpInst
  |> interpLocalStack

noncomputable
def ProgramCFG.interp (P : ProgramCFG) : (ITree (SideEff ⊕ₑ ErrUB)) ReturnVals :=
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

#check denote
#check ITree.Bisim.coinduct

open ITree.ITree (Bisim)

-- theorem Block.denote_eq_vis_hole_iff (b : Block n) (bid) (args) :
--   b.denote bid args = vis (.inl h) k ↔

@[simp, grind .]
axiom hasEffect_raiseError [ErrUB -< ε] (e : ε.I) :
    (raiseError reason : ITree ε α).HasEffect e ↔ e = (Subeffect.map (E₁:=ErrUB) <| .error reason).1

theorem hasEffect_denote_step :
    (denote.step P b).HasEffect (Sum.inl hole)

theorem interpHoles_program (P : ProgramCFG) : ∀ {f g : HoleId → ITree (ErrUB ⊕ₑ InstEff) Unit},
    interpHoles f P.denote = interpHoles g P.denote := by
  let ε := ErrUB ⊕ₑ InstEff
  suffices ∀ f,
      interpHoles (ε:=ε) f P.denote = interpHoles (ε:=ε) (fun _ => .forever) P.denote by
    grind
  intro f
  simp only [interpHoles, ITree.interpFirst]
  rw [ITree.interp_congr]
  intro e he
  cases e with
  | inr e => rfl
  | inl hole =>
    exfalso
    simp [denote] at he
    obtain ⟨b, hb⟩ : ∃ b : Branch, (denote.step P b).HasEffect (.inl hole) := by grind
    simp [denote.step] at hb

    generalize ht : denote.step P b = t at *
    generalize heff : Sum.inl hole = eff at *
    induction hb
    case vis_self t i k ht' =>
      obtain rfl : t = .vis i k := by grind
      clear ht'
      subst heff
      simp [denote.step] at ht
      split at ht
      next block hb =>
        simp [Block.denote]

        sorry
      next =>
        exfalso
        sorry
    case vis_cont =>
      grind
    case tau =>
      grind


theorem interp_plug {C : ContextCFG n} {I : Pattern n} :
    (C.plug I).interp = C.interp (I[·].denote) := by
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
  simp [interpHoles, denote, ITree.interpFirst, ITree.interpSum]
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

/-! ### WellFormedness -/
section WellFormedness
variable {C : ContextCFG n}

-- instance : HasDominance (C.BlockRef) where
--   entry := C.entry
--   cfg a b := a.get.term.canJumpTo b.val
--   isExit b := b.get.term.isReturn

end WellFormedness



end ContextCFG
