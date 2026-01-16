import EffectSSA.Types.WellTyped
import EffectSSA.Types.Lemmas

/-!
# Decidable Typechecking

This file implements `Instruction.typeCheck` and `Program.typeCheck` functions,
which compute the resulting context of an instruction (resp. program), and
return this bundled with a proof that the instruction (resp. program) is wellformed.

These functions are leveraged to show that Program.WellTyped is decidable, but
the `typeCheck` functions are also public (e.g., to be used by other decidable
instances).
-/
namespace EffectSSA

/-!
## `typeCheck`
--------------------------------------------------------------------------------
-/

inductive Instruction.TypeCheckResult (Γ : Context τ n) (i : Instruction τ n) where
  | isTrue {m} (Δ : Context τ m) (h : WellTyped Γ i Δ := by grind) (hm : m = i.results := by grind)
  | isFalse (h : ∀ {m} (Δ : Context τ m), ¬WellTyped Γ i Δ := by grind)

def Instruction.typeCheck (Γ : Context τ n) : (i : Instruction τ n) → i.TypeCheckResult Γ
  | .loadI t p =>
      if h : Γ[p] = .ptr then
        .isTrue (Γ <: t)
      else .isFalse
  | .storeI t p x =>
      if h : Γ[p] = .ptr ∧ Γ[x] = t then
        .isTrue Γ
      else .isFalse
  | .allocI .. | .freeI .. => .isFalse
  -- FIXME: these should have type rules also!
  | .loadE t e p =>
      if h : Γ[e] = .eff ∧ Γ[p] = .ptr then
        have := e.toFin.isLt
        .isTrue (Γ.eraseVar e <: .eff <: t)
      else .isFalse
  | .storeE t e p x =>
      if h : Γ[e] = .eff ∧ Γ[p] = .ptr ∧ Γ[x] = t then
        have := e.toFin.isLt
        .isTrue (Γ.eraseVar e <: .eff)
      else .isFalse
  | .allocE .. | .freeE .. => .isFalse
  -- FIXME: these should have type rules also!
  | .merge e₁ e₂ => .isFalse
  | .split e => .isFalse
  | .createEff =>
      if h : Γ.isUnrestricted then
        .isTrue _ (by apply WellTyped.createEff; grind)
      else .isFalse
  | .consumeEff e =>
      let Γ' := Γ.eraseVar e
      if h : Γ[e] = .eff ∧ Γ'.isUnrestricted then
        .isTrue Γ'
      else .isFalse

inductive Program.TypeCheckResult (Γ : Context τ n) (p : Program τ n) where
  | isTrue {m} (Δ : Context τ m)
            (h₁ : WellTypedWith Γ p Δ := by grind)
            (h₂ : Δ.isUnrestricted := by grind)
            (hm : m = p.results := by grind)
  | isFalse (h : ∀ {m} (Δ : Context τ m), ¬WellTypedWith Γ p Δ ∨ ¬Δ.isUnrestricted := by grind)

def Program.typeCheck (Γ : Context τ n) : (p : Program τ n) → p.TypeCheckResult Γ
  | .nil =>
    if h₂ : Γ.isUnrestricted then
      .isTrue Γ .nil h₂
    else
      .isFalse
  | i ;> p =>
    match i.typeCheck Γ with
    | .isFalse h => .isFalse
    | .isTrue Δ hᵢ (Eq.refl _) =>
      match p.typeCheck Δ with
      | .isFalse h => .isFalse
      | .isTrue Δ' h₁ h₂ hm => .isTrue Δ'

/-!
## `Decidable` instance
--------------------------------------------------------------------------------
-/

instance : Decidable (Program.WellTyped Γ p) :=
  match p.typeCheck Γ with
  | .isTrue Δ h₁ h₂ (Eq.refl _) => .isTrue <| by use Δ
  | .isFalse h => .isFalse <| by grind
