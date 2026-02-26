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
attribute [local grind] Instruction.WellTyped

inductive Instruction.TypeCheckResult (Γ : Context τ) (i : Instruction τ) where
  | isTrue (Δ : Context τ) (h : WellTyped Γ i Δ := by grind)
  | isFalse (h : ∀ (Δ : Context τ), ¬WellTyped Γ i Δ := by grind)

def Instruction.typeCheck (Γ : Context τ) : (i : Instruction τ) → i.TypeCheckResult Γ
  | .loadI t p =>
      if h : Γ.isUnrestricted ∧ Γ[p]? = some .ptr then
        .isTrue (Γ <: t)
      else .isFalse
  | .storeI t p x =>
      if h : Γ.isUnrestricted ∧ Γ[p]? = some .ptr ∧ Γ[x]? = some t then
        .isTrue Γ
      else .isFalse
  | .allocI .. | .freeI .. => .isFalse
  -- FIXME: these should have type rules also!
  | .loadE t e p =>
      if h : Γ[e]? = some .eff ∧ Γ[p]? = some .ptr then
        .isTrue (Γ.eraseVar e <: .eff <: t)
      else .isFalse
  | .storeE t e p x =>
      if h : Γ[e]? = some .eff ∧ Γ[p]? = some .ptr ∧ Γ[x]? = some t then
        .isTrue (Γ.eraseVar e <: .eff)
      else .isFalse
  | .allocE .. | .freeE .. => .isFalse
  -- FIXME: these should have type rules also!
  | .merge e₁ e₂ => .isFalse
  | .split e => .isFalse
  | .createEff =>
      if h : Γ.isUnrestricted then
        .isTrue (Γ <: .eff)
      else .isFalse
  | .consumeEff e =>
      let Γ' := Γ.eraseVar e
      if h : Γ[e]? = some .eff ∧ Γ'.isUnrestricted then
        .isTrue Γ'
      else .isFalse

inductive InstructionSeq.TypeCheckResult (Γ : Context τ) (p : InstructionSeq τ) where
  | isTrue (Δ : Context τ) (h : WellTypedWith Γ p Δ := by grind)
  | isFalse (h : ∀ (Δ : Context τ), ¬WellTypedWith Γ p Δ := by grind)

def InstructionSeq.typeCheck (Γ : Context τ) : (p : InstructionSeq τ) → p.TypeCheckResult Γ
  | nil => .isTrue Γ (.nil rfl)
  | i ;> p =>
    match i.typeCheck Γ with
      | .isFalse h => .isFalse
      | .isTrue Δ hᵢ =>
        match p.typeCheck Δ with
        | .isFalse h => .isFalse <| by grind
        | .isTrue Δ' h => .isTrue Δ'

inductive Program.TypeCheckResult (Γ : Context τ) (p : Program τ) (ts : List τ.Typ) where
  | isTrue (Δ : Context τ) (h : Program.WellTyped Γ p ts := by grind)
  | isFalse (h : ¬Program.WellTyped Γ p ts := by grind)

/-!
## Program `Decidable` instance
--------------------------------------------------------------------------------
-/

instance : Decidable (Program.WellTyped Γ p ts) :=
  match p.instructions.typeCheck Γ with
  | .isTrue Δ h₁ =>
      let vs := p.returnVars
      if hun : ¬(Δ.eraseVars vs).isUnrestricted then
        .isFalse (by grind)
      else if hlen : vs.length ≠ ts.length then
        .isFalse (by grind)
      else if hret : ∃ (i : Fin vs.length), Δ[vs[i]]? ≠ ts[i]? then
        .isFalse (by grind)
      else
        have hret : ∀ (i : Fin vs.length), Δ[vs[i]]? = ts[i]? := by grind
        .isTrue ⟨Δ, h₁, by grind, by grind, fun i hi => hret ⟨i, hi⟩⟩
  | .isFalse h => .isFalse (by grind)
