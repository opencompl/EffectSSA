module

public import EffectSSA.ProofSketch.ProofSketch
public import EffectSSA.ProofSketch.EqnInv

/-!
# LeanMLIR Comparison

In this file, we define a notion of "contigous" refinement,
as an analogue of the local soundness used in LeanMLIR,
and show that under the assumptions made in LeanMLIR,
contiguous refinement implies denotational refinement.

That is, we show that we admit at least all rewrites that LeanMLIR did.
-/
public section
namespace EffectSSA.ProofSketch
variable [SSA ι σ ν]

/-!
## Upstreamable
-/
section Upstream

/-- Extract the first `m` components of a pattern. -/
def Pattern.take (P : Pattern ι n) (m : Nat) : Pattern ι (min m n) :=
  ofVector <| P.toVector.take m
/-- Delete the first `m` components of a pattern. -/
def Pattern.drop (P : Pattern ι n) (m : Nat) : Pattern ι (n - m) :=
  ofVector <| P.toVector.drop m

abbrev Pattern.snoc (P : Pattern ι n) (I : InstSeq ι) : Pattern ι (n + 1) :=
  P ++ (ofVector #v[I])

axiom Pattern.denote_eq_denote_drop_take (P : Pattern ι n) (k : Hole n) :
    ⟦P⟧ = ⟦P.drop (k.val + 1)⟧ ∘ ⟦P[k]⟧ ∘ ⟦P.take k.val⟧ -- := by
  -- funext ρ
  -- simp only [Function.comp_apply]

end Upstream

/-!
## Contiguous Refinement

Assumption 1: LeanMLIR only allows rewriting at the "root" of the pattern.
We encode this by saying a rewrite is a triple `(M, s, t)`, where
`M` is an `n`-ary pattern giving the sparsely matched instructions,
`s` is the root of the source pattern and `t` is the rewriten root of the target.
-/

/--
`M; s` is contigously refined by `M; t`,
when executing `M; s` as a straight-line (contigous) program
is refined by the execution of `M; t` as the same, under any environment.
-/
def Pattern.IsContRefinedBy (M : Pattern ι n) (s t : InstSeq ι) : Prop :=
  ∀ ρ, ⟦s⟧ (⟦M⟧ ρ) ⊒ ⟦t⟧ (⟦M⟧ ρ)


/-!
## Assumption 2: Purity

LeanMLIR assumed all rewriten operations are pure.
-/
section Pure

/--
An instruction is pure, if it is locally pure and
does not modify the global state at all.

Note: a pure instruction may still set the global "error" flag.
-/
@[expose, grind]
def Inst.Pure (i : Inst ι) : Prop :=
  i.LocallyPure ∧ ∀ ρ, (⟦i⟧ ρ).state = ρ.state

@[expose, grind] def InstSeq.Pure (is : InstSeq ι) := ∀ i ∈ is, i.Pure
@[expose, grind] def Pattern.Pure (P : Pattern ι n) := ∀ is ∈ P, is.Pure

section Lemmas

@[simp, grind =>] theorem Inst.state_denote {i : Inst ι} (hp : i.Pure) :
    (⟦i⟧ ρ).state = ρ.state := by
  grind

@[simp, grind =>] theorem InstSeq.state_denote {I : InstSeq ι} (hp : I.Pure) :
    (⟦I⟧ ρ).state = ρ.state := by
  induction I generalizing ρ
  case nil => simp
  case cons ih => rw [denote_cons, ih, Inst.state_denote] <;> grind

@[simp, grind =>] theorem Pattern.state_denote {P : Pattern ι n} (hp : P.Pure) :
    (⟦P⟧ ρ).state = ρ.state := by
  induction P generalizing ρ
  case nil => simp
  case cons ih => rw [denote_cons, ih, InstSeq.state_denote] <;> grind

end Lemmas
end Pure

/-!
## Assumption 2: Root-only Rewrites

LeanMLIR only allowed rewriting at the "root", i.e., last component, of a pattern.
We model this via an n-ary rewrite `(S, T)` such that the first `n - 1`
components of `S` and `T` are equal.
-/

/-!
## Assumption 3: No Errors

LeanMLIR included an extensible typesystem that ensured, among other things,
that instructions are given the right number and *type* of arguments.
We don't have a static analogue, instead relying on a dynamic error.

Although the number of arguments is solely a property of the program itself,
the types of the arguments is also a property of the supplied environment.
LeanMLIR enforced that the environment respected the typesystem.
We encode this property by assuming that `⟦s⟧ ρ` raises an error iff `⟦t⟧ ρ`
raises an error, too.
-/


/-!
## Contiguous Implies Denotational
-/

/--
Proof that denotational refinement is implied by "contiguous" refinement,
under a set of assumptions.
-/
theorem denRefine_of_isContRefinedBy (M : Pattern ι n) (s t : InstSeq ι)
    (wf_S : (M.cons s).WellFormed Γs) (wf_T : (M.cons t).WellFormed Γt)
    (pure_M : M.Pure) (pure_s : s.Pure) (pure_t : t.Pure)
    (herr : ∀ ρ, (⟦s⟧ ρ).error = (⟦t⟧ ρ).error)
    (hr : M.IsContRefinedBy s t) :
    (M.snoc s).DenRefine (M.snoc t) := by
  replace hr : ∀ ρ η, ρ ⊒ η → ⟦s⟧ (⟦M⟧ ρ) ⊒ ⟦t⟧ (⟦M⟧ η) := by
    intro ρ η hρη
    calc ⟦s⟧ (⟦M⟧ ρ)
      _ ⊒ ⟦s⟧ (⟦M⟧ η) := by grind
      _ ⊒ ⟦t⟧ (⟦M⟧ η) := hr _

  intro k ρ η hρη hS hT
  by_cases hk : k.val < n
  case pos => grind
  case neg =>
    obtain rfl : k = .last _ := by grind
    clear hk
    suffices ⟦s⟧ ρ ⊒ ⟦t⟧ η by simpa
    suffices (⟦s⟧ ρ).locals ⊒ (⟦t⟧ η).locals by
      -- have hstate : ∀ {ρ}, (⟦M⟧ ρ).state = ρ.state := by grind
      simp [SEnv.isRefinedBy_iff, herr]




    rw [InstSeq.denote_eq_of_args]



    suffices ⟦M⟧ ρ = ρ ∧ ⟦M⟧ η = η by grind



    -- let S₀ := S.take k.val
    -- let Sₙ := S.drop (k.val + 1)
    -- have S_eq : ⟦S⟧ = ⟦Sₙ⟧ ∘ ⟦S[k]⟧ ∘ ⟦S₀⟧ := S.denote_eq_denote_drop_take _
    -- let T₀ := T.take k.val
    -- let Tₙ := T.drop (k.val + 1)
    -- have T_eq : ⟦T⟧ = ⟦Tₙ⟧ ∘ ⟦T[k]⟧ ∘ ⟦T₀⟧ := T.denote_eq_denote_drop_take _
    -- Since `S` and `T` are pure, we need only show refinement for locals
    suffices (⟦S⟧ ρ).locals ⊒ (⟦T⟧ η).locals by
      simp only [SEnv.isRefinedBy_iff, Bool.not_eq_eq_eq_not, Bool.not_true]
      intro ρerr
