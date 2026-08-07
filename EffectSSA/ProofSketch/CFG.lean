module

public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Effect
public import EffectSSA.ProofSketch.Notation.Refinement

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
abbrev ContextCFG.interp (C : ContextCFG n) (f : Hole n → ITree (ErrUB ⊕ InstEff) Unit) :
    ExceptT ErrUB (ITree SideEff) ReturnVals := do
  C.denote |> interpAll (f · |>.lift)

noncomputable
abbrev ProgramCFG.interp (P : ProgramCFG) : ExceptT ErrUB (ITree SideEff) ReturnVals :=
  ContextCFG.interp P Hole.elim0

/-!
## ReturnVals API
-/
namespace ReturnVals

abbrev length (xs : ReturnVals) := xs.toList.length

@[grind, grind cases]
inductive IsRefinedBy : ReturnVals → ReturnVals → Prop
  | nil : IsRefinedBy ⟨[]⟩ ⟨[]⟩
  | cons : x ⊒ y → IsRefinedBy ⟨xs⟩ ⟨ys⟩ → IsRefinedBy ⟨x :: xs⟩ ⟨y :: ys⟩

variable {xs ys zs : ReturnVals}

axiom isRefinedBy_trans : xs.IsRefinedBy ys → ys.IsRefinedBy zs → xs.IsRefinedBy zs

instance : Refinement ReturnVals where
  IsRefinedBy := IsRefinedBy
  refl xs := by
    rcases xs with ⟨xs⟩
    induction xs <;> grind
  trans := isRefinedBy_trans

end ReturnVals

/-!
## ContextCFG API
-/
variable {C : ContextCFG n}
attribute [simp, grind .] ContextCFG.entryId_mem_blocks

namespace ContextCFG

/-! ### InterpHoles -/
section InterpHoles

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
    interpHoles (f ·) P.denote = interpHoles g P.denote := by
  simp only [interpHoles]
  apply ITree.interpLeft_congr
  intro e he
  exfalso -- there cannot actually be any hole effects in P.denote!
  obtain ⟨⟨bId, args⟩, hb⟩ : ∃ b, (denote.step P b).HasEffect e := by
    grind [denote]
  grind [denote.step]

end InterpHoles
end ContextCFG

/-! ### Plug -/
section Plug

def Block.plug (b : Block n) (I : Pattern n) : Block 0 :=
  { b with code := b.code.plug I }

def ContextCFG.plug (C : ContextCFG n) (I : Pattern n) : ProgramCFG :=
  { C with
    blocks := C.blocks.map fun _ block => block.plug I
    entryId_mem_blocks := by simp
  }

@[simp, grind =] theorem ContextCFG.entryId_plug : (C.plug I).entryId = C.entryId := by rfl

@[simp, grind =] theorem ContextCFG.getElem?_blocks_plug (bId : BlockId) :
    (C.plug I).blocks[bId]? = (·.plug I) <$> C.blocks[bId]? := by
  simp [plug]

@[simp]
theorem Block.interp_plug {b : Block n} {br : Branch} {I : Pattern n}
    {f : HoleId → ITree OpaqueEff Unit} :
    ((b.plug I).denote br.target br.args).interpLeft f
    = let g : Hole n → ITree (InstEff ⊕ ErrUB) Unit := fun h => I[h].denote.lift
      (b.denote br.target br.args).interpLeft (do
          let h ← Hole.fromId ·
          (g h).lift) := by
  -- rcases b with ⟨args, code, term⟩
  simp only [denote, plug, ITree.pure_eq_ret, List.forM_eq_forM, ITree.bind_ret,
    Nat.toString_eq_repr, bind_raiseError, Pattern.getElem_hole]
  by_cases b.args.length = br.args.length
  case neg => grind
  case pos hargs =>
    simp only [hargs, ↓reduceIte, ITree.interpLeft_bind]
    simp only [ITree.interpLeft_forM, MultiContext.denote_ofSeq, ITree.liftM_eq_lift]
    congr 2
    · funext ⟨var, val⟩
      simp [Effect.trigger, ITree.interpLeft, pushVar]
    funext ⟨⟩
    congr 1
    · -- The main interesting bit of the proof
      induction b.code
      case nil =>
        -- TODO: interpLeft_ret simp-lemma
        simp [ITree.interpLeft]
      case cons i_or_h is ih =>
        rcases i_or_h with i|h
        · simp only [MultiContext.plug_cons_inst, InstSeq.denote_cons, ITree.lift_seqRight,
          ITree.interpLeft_seqRight, ih, MultiContext.denote_cons_inst];
          simp [ITree.interpLeft, Effect.trigger]
        · simp only [MultiContext.plug_cons_hole, Pattern.getElem_hole, InstSeq.denote_append,
          ITree.lift_seqRight, ITree.interpLeft_seqRight, ih, MultiContext.denote_cons_hole]
          congr 1
          conv => {
            rhs; simp [ITree.interpLeft, Effect.trigger]
          }
          sorry
          -- ^^ ought to be trivial, with the right lemmas
    · sorry
      -- ^^ ought to be trivial, with the right lemmas

open ITree in
theorem ContextCFG.interp_plug {C : ContextCFG n} {I : Pattern n} :
    (C.plug I).interp = C.interp (liftM <| I[·].denote) := by
  simp only [ProgramCFG.interp, interp, interpAll, interpAllM]
  congr 4
  simp only [denote, entryId_plug]
  apply ITree.eq_of_bisim
  apply ITree.Bisim.coinduct <| fun t u =>
    ∃ b : Branch,
      t = (interpHoles (ε:=ErrUB ⊕ InstEff) (fun x => Hole.fromId x >>= Hole.elim0)
            (ITree.iter (denote.step (C.plug I)) b))
      ∧ u = (interpHoles (ε:=ErrUB ⊕ InstEff)
              (fun x => do
                let x : Hole n ← Hole.fromId x
                liftM I[x].denote)
              (ITree.iter (denote.step C) b))
  · rintro t u ⟨br, ht, hu⟩
    simp only [ITree.iter, denote.step, getElem?_blocks_plug, Option.map_eq_map,
      interpHoles, interpLeft_bind] at ht hu
    cases hb : C.blocks[br.target]?
    case none =>
      simp [hb] at ht hu ⊢
      simp_all
      sorry
    case some b =>
      simp only [hb, Option.map_some] at ht hu ⊢
      simp at ht hu
      sorry

  · refine ⟨⟨C.entryId, []⟩, ?_⟩
    simp only [interpHoles, lift, Subeffect.mapEff, bind_ret, pure_eq_ret, ITree.map_bind, map_map,
      Subeffect.mapCont, Fin.getElem_fin, Hole.val_toFin, liftM_eq_lift, Subeffect.mapEff_eq_inr,
      Subeffect.mapEff_eq_self, Subeffect.map_inr, Subeffect.map_eq_inl, Subeffect.map_eq_self,
      Subeffect.map_eq_inr, id_eq, Subeffect.map_inl, Pattern.getElem_hole, withErrorContext]
    and_intros <;> (
      congr 1
      funext h
      cases Hole.fromId? h
      <;> simp
      <;> grind
    )

end Plug

namespace ContextCFG

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
