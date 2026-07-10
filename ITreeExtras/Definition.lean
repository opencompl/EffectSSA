module

-- TODO: can we make this a non-public import and hide all CoInd things from clients of this?
public import Coinductive
public import ITreeExtras.Effect

/-!
# ITree definition

Vendored from the `ITree` library
(https://github.com/ISTA-PLV/coinductive, `ITree/Definition.lean`,
upstream rev `d1aeffe87ec7bd4bd13ed92fdc00ef6c5d58f800`).
-/

@[expose] public section

namespace ITree
open Coinductive Lean.Order

inductive ITreeF (ε : Type u) {κ : ε → Type u} [Effect ε κ]
    (α : Type v) (ITree : Type w) : Type (max u v w) where
  | ret (r : α)
  | tau (t : ITree)
  | vis (i : ε) (k : κ i → ITree)

inductive ITreeF.In (ε : Type u) (α : Type u) : Type u where
  | ret (r : α)
  | tau
  | vis (i : ε)

instance (ε : Type u) {κ : ε → Type u} [Effect ε κ] (α : Type u) : PF (ITreeF ε α) where
  P := ⟨ITreeF.In ε α, fun
    | .ret _ => PEmpty
    | .tau => PUnit
    | .vis i => κ i⟩
  unpack
    | .ret r => .obj (.ret r) nofun
    | .tau t => .obj .tau λ _ => t
    | .vis i k => .obj (.vis i) k
  pack
    | .obj (.ret r) _ => .ret r
    | .obj .tau k => .tau (k ⟨⟩)
    | .obj (.vis i) k => .vis i k
  unpack_pack := by rintro _ ⟨⟩ <;> simp
  pack_unpack := by rintro _ (⟨⟨⟩, _⟩ | ⟨⟨⟩⟩) <;> simp <;> funext x <;> cases x

abbrev ITree (ε : Type u) {κ : ε → Type u} [Effect ε κ] (α : Type u) : Type u :=
  CoInd (ITreeF ε α)
abbrev ITreeN (ε : Type u) {κ : ε → Type u} [Effect ε κ] (α : Type u) (n : Nat) : Type u :=
  CoIndN (ITreeF ε α) n

variable {ε} {κ} [Effect.{u} ε κ] {α}

def ITree.fold (t : ITreeF ε α (ITree ε α)) : ITree ε α := CoInd.fold _ t
def ITree.ret (r : α) : ITree ε α := ITree.fold (.ret r)
def ITree.tau (t : ITree ε α) : ITree ε α := ITree.fold (.tau t)
def ITree.vis (i : ε) (k : κ i → ITree ε α) : ITree ε α := ITree.fold (.vis i k)
def ITree.unfold (t : ITree ε α) : ITreeF ε α (ITree ε α) := CoInd.unfold _ t

/- Ideally everything above this would be automatically generated -/

instance : Inhabited (ITreeF ε α PUnit) where default := .tau ⟨⟩

@[simp]
theorem ITree.unfold_fold (t : ITree ε α) :
  ITree.fold (ITree.unfold t) = t := by simp [ITree.fold, ITree.unfold]

@[simp]
theorem ret_approx_1 (r : α) n :
  (ITree.ret (ε:=ε) r).approx (n + 1) = ITreeF.ret r := by
    simp [ITree.ret, ITree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_ret_approx_1 (r : α) n :
  (ITree.fold (ITreeF.ret (ε:=ε) r)).approx (n + 1) = ITreeF.ret r :=
    ret_approx_1 r n

@[simp]
theorem tau_approx_1 (t : ITree ε α) n :
  t.tau.approx (n + 1) = ITreeF.tau (t.approx n) := by
    simp [ITree.tau, ITree.fold, CoInd.fold, PF.map, PF.pack, PF.unpack]

@[simp]
theorem fold_tau_approx_1 (t : ITree ε α) n :
  (ITree.fold (ITreeF.tau t)).approx (n + 1) = ITreeF.tau (t.approx n) :=
    tau_approx_1 t n

@[simp]
theorem vis_approx_1 i (t : κ i → ITree ε α) n :
  (ITree.vis i t).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := by
    simp [ITree.vis, ITree.fold, CoInd.fold, PF.map, PF.pack]
    rfl

@[simp]
theorem fold_vis_approx_1 i (t : κ i → ITree ε α) n :
  (ITree.fold (ITreeF.vis i t)).approx (n + 1) = ITreeF.vis i (λ o => (t o).approx n) := vis_approx_1 i t n

@[simp]
theorem unfold_ret (r : α) :
  ITree.unfold (ITree.ret r) = ITreeF.ret (ε:=ε) r := by
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_tau (t : ITree ε α) :
  ITree.unfold (ITree.tau t) = ITreeF.tau t := by
    simp [ITree.tau, ITree.fold, ITree.unfold]

@[simp]
theorem unfold_vis i (t : κ i → ITree ε α) :
  ITree.unfold (ITree.vis i t) = ITreeF.vis i t := by
    simp [ITree.vis, ITree.fold, ITree.unfold]


theorem tau_monoN (t1 t2 : ITree ε α) n :
  CoIndN.le _ (t1.approx n) (t2.approx n) →
  CoIndN.le _ (t1.tau.approx (n + 1)) (t2.tau.approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem tau_mono γ [PartialOrder γ] (f : γ → ITree ε α) :
  monotone f →
  monotone (λ x => ITree.tau (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply tau_monoN
    grind [CoInd.leN_le, monotone]

theorem vis_monoN i (t1 t2 : κ i → ITree ε α) n :
  (∀ o, CoIndN.le _ ((t1 o).approx n) ((t2 o).approx n)) →
  CoIndN.le _ ((ITree.vis i t1).approx (n + 1)) ((ITree.vis i t2).approx (n + 1))
 := by
    intro hs
    simp [CoIndN.le, PF.unpack]
    right
    constructor <;> try rfl
    grind [coherent1]

@[partial_fixpoint_monotone]
theorem vis_mono γ [PartialOrder γ] i (f : γ → κ i → ITree ε α) :
  monotone f →
  monotone (λ x => ITree.vis i (f x)) := by
    intro hf t1 t2 hle
    apply CoInd.le_leN
    rintro ⟨n⟩; simp [CoIndN.le]
    apply vis_monoN
    intro o
    have := hf t1 t2 hle o
    grind [CoInd.leN_le]

def ITree.spin : ITree ε α := spin.tau
partial_fixpoint

@[simp]
theorem ITree.bot_eq :
  CoInd.bot (ITreeF ε α) = ITree.spin := by
    ext n
    induction n; congr 0
    rw [CoInd.bot_eq, spin]
    simp [PF.map, PF.pack, CoInd.fold, *, PF.unpack, default]

theorem ITree.le_unfold (t1 t2 : ITree ε α) :
  (t1 ⊑ t2) = (t1 = .spin ∨
    (∃ r, t1 = .ret r ∧ t2 = .ret r) ∨
    (∃ t1' t2', t1 = .tau t1' ∧ t2 = .tau t2' ∧ t1' ⊑ t2') ∨
    (∃ i t1' t2', t1 = .vis i t1' ∧ t2 = .vis i t2' ∧ ∀ o, t1' o ⊑ t2' o)) := by
    ext
    constructor
    · intro h
      rw [CoInd.le_unfold] at h
      rcases h with (rfl|⟨i, _, _, _, _, h1, h2⟩); simp
      rw [<-Coinductive.unfold_fold _ t1, <-Coinductive.unfold_fold _ t2]
      rw [<-PF.unpack_pack (CoInd.unfold _ t1), <-PF.unpack_pack (CoInd.unfold _ t2)]
      simp only [h1, h2]
      right
      cases i <;> simp [PF.pack, ret, tau, vis, fold]
      · grind
      · grind
      · right
        right
        exists ?_, ?_; rotate_left 1
        constructor; rfl
        apply Exists.intro
        constructor; rfl
        simp_all
    · rintro (rfl| ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
      · simp [CoInd.le_unfold]
      · apply PartialOrder.rel_refl
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack, ITree.tau, ITree.fold]
        constructor <;> try rfl
        grind
      · simp [CoInd.le_unfold]
        right
        simp [PF.unpack, ITree.vis, ITree.fold]
        constructor <;> try rfl
        grind

-- use Bind.bind instead
def ITree.bind {β} (t1 : ITree ε α) (t2 : α → ITree ε β) :=
  match t1.unfold with
  | .ret r => t2 r
  | .tau t => .tau (ITree.bind t t2)
  | .vis i k => .vis i (λ o => ITree.bind (k o) t2)
partial_fixpoint

@[simp]
theorem itree_ret_bind {β} r (t : β → ITree ε α) :
  ITree.bind (.ret r) t = t r := by
    rw [ITree.bind]
    simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem itree_vis_bind {β} i k (t : β → ITree ε α) :
  ITree.bind (.vis i k) t = .vis i (λ o => ITree.bind (k o) t) := by
    rw [ITree.bind]
    simp [ITree.vis, ITree.fold, ITree.unfold]

@[simp]
theorem itree_tau_bind {β} t1 (t : β → ITree ε α) :
  ITree.bind (t1.tau) t = .tau (ITree.bind t1 t) := by
    rw [ITree.bind]
    simp [ITree.tau, ITree.fold, ITree.unfold]


@[partial_fixpoint_monotone]
theorem bind_mono {γ} {β} [PartialOrder γ]
  (f : γ → ITree ε α) (g : γ → α → ITree ε β) :
  monotone f →
  monotone g →
  monotone (λ x => ITree.bind (f x) (g x)) := by
    intro hf hg t1 t2 hle
    apply CoInd.le_leN
    intro n
    dsimp only
    have hlef : (f t1) ⊑ (f t2) := by apply hf; assumption
    generalize f t1 = t1, f t2 = t2 at hlef
    induction n generalizing t1 t2; simp [CoIndN.le]
    unfold ITree.bind
    rw [ITree.le_unfold] at hlef
    rcases hlef with (rfl|⟨_, rfl, rfl⟩|⟨_, _, rfl, rfl, _⟩|⟨_, _, _, rfl, rfl, _⟩)
    · unfold ITree.spin
      simp [CoIndN.le, CoIndN.bot]
      left
      unfold ITree.spin
      simp
      congr
      ext n
      induction n; congr 0
      unfold ITree.bind ITree.spin
      simp_all
    · rename_i x
      simp
      have := hg t1 t2 hle x
      grind [CoInd.leN_le, monotone]
    · simp
      apply tau_monoN
      grind [CoInd.leN_le, monotone]
    · simp
      apply vis_monoN
      grind [CoInd.leN_le, monotone]


instance : Monad (ITree.{u} ε) where
  pure := ITree.ret
  bind := ITree.bind

@[elab_as_elim, cases_eliminator]
def ITree.cases {ε} {κ} [Effect.{u} ε κ] {α}
    {motive : ITree ε α → Sort v}
    (ret : ∀ r, motive (pure r))
    (tau : ∀ t : ITree ε α, motive (t.tau))
    (vis : ∀ i k, motive (ITree.vis i k))
    (t : ITree ε α) : motive t := by
    rw [<-ITree.unfold_fold t]
    cases t.unfold
    · apply ret
    · apply tau
    · apply vis

@[simp]
theorem unfold_pure (r : α) :
  ITree.unfold (pure r) = ITreeF.ret (ε:=ε) r := by
    simp [pure]

@[simp]
theorem pure_approx_1 (r : α) n :
  (pure r : ITree _ _).approx (n + 1) = ITreeF.ret (ε:=ε) r := by
    simp [pure]

instance : LawfulMonad (ITree ε) := LawfulMonad.mk' (ITree ε)
  (id_map := by
    simp [Functor.map]
    intro _ t
    ext n
    induction n generalizing t; congr 0
    unfold ITree.bind
    cases t <;> simp [*])
  (pure_bind := by simp [pure, Bind.bind])
  (bind_assoc := by
    simp [Bind.bind]
    intro _ _ _ t1 t2 t3
    ext n
    induction n generalizing t1; congr 0
    rw [ITree.bind.eq_def t1]
    rw [ITree.bind.eq_def t1]
    split <;> simp [*])

instance : MonoBind (ITree ε) where
  bind_mono_left := by
    intro _ _ _ _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => x) <;> grind [monotone, PartialOrder.rel_refl]
  bind_mono_right := by
    intro _ _ a _ _ _
    dsimp [Bind.bind]
    apply bind_mono (λ x => a) (λ x => x)
    · grind [monotone, PartialOrder.rel_refl]
    · grind [monotone, PartialOrder.rel_refl]
    · intro _; grind

@[simp]
theorem tau_bind {β} t1 (t : β → ITree ε α) :
  t1.tau >>= t = .tau (t1 >>= t) := by simp [Bind.bind]

@[simp]
theorem vis_bind {β} i k (t : β → ITree ε α) :
  (.vis i k) >>= t = .vis i (λ o => k o >>= t) := by simp [Bind.bind]


def Effect.trigger (ε₁) {κ₁} [Effect.{u} ε₁ κ₁]
    {ε₂} {κ₂} [Effect.{u} ε₂ κ₂]
    [ε₁ -< ε₂] (i : ε₁) : ITree.{u} ε₂ (κ₁ i) :=
  let ⟨i₂, f⟩ := (Subeffect.map i);
  ITree.vis i₂ (λ x => return (f x))

end ITree
