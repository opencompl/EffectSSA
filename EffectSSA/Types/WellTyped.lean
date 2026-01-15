import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Basic
import EffectSSA.Types.Context

/-!
# Type Rules

This file defines the type rules of our language via the `WellTyped` predicate.

-/
namespace EffectSSA
variable {τ} [MemorySignature τ]

/-!
## WellTyped Predicate
--------------------------------------------------------------------------------
-/
open Ty.Typ (ptr eff)

@[grind]
inductive Instruction.WellTyped : Context τ n → Instruction τ n → Context τ m → Prop
  | loadI :
      Γ[p] = ptr →
      ---------------------------------
      WellTyped Γ (.loadI t p) (Γ <: t)

  | storeI :
      Γ[p] = ptr →
      Γ[x] = .data t →
      -- FIXME: I would prefer writing `Γ[x] = t` here, but then Lean searches
      --   for (and fails to find) a `GetElem` instance with `τ.DType` as the
      --   return value, instead of the intended `τ.Typ` return value to which
      --   `τ.DType` can be coerced. I should minimize and report this.
      ---------------------------------
      WellTyped Γ (.storeI t p x) Γ

  | loadE :
      Γ[e] = eff →
      Γ[p] = ptr →
      ---------------------------------
      WellTyped Γ (.loadE t e p) (Γ.eraseVar e <: eff <: t)

  | storeE :
      Γ[e] = eff →
      Γ[p] = ptr →
      Γ[x] = .data t →
      ---------------------------------
      WellTyped Γ (.storeE t e p x) (Γ.eraseVar e <: eff)

  | createEff :
      Γ.isUnrestricted →
      ---------------------------------
      WellTyped Γ .createEff (Γ <: eff)

  | consumeEff :
      Γ[e] = .eff →
      (Γ.eraseVar e).isUnrestricted →
      ---------------------------------
      WellTyped Γ (.consumeEff e) (Γ.eraseVar e)

open Instruction.WellTyped in
attribute [grind ←] loadI storeI loadE storeE createEff consumeEff

/--
`WellTypedWith Γ p Δ` holds when the instruction in program `p` are welltyped under
`Γ`, and result in a final context `Δ` after execution.

NOTE: linearity is not yet checked
-/
@[grind cases]
inductive Program.WellTypedWith : Context τ n → Program τ n → Context τ m → Prop
  /--
  An empty program does not change the context.

  NOTE: This does *not* yet enforce that linear variables must be used.
  -/
  | nil : WellTypedWith Γ .nil Γ
  /--
  A program is welltyped if it's instructions are welltyped, under appropriately
  adjusted contexts.
  -/
  | cons :
      Instruction.WellTyped Γ i Δ →
      WellTypedWith Δ p Ξ →
      ---------------------------------
      WellTypedWith Γ (.cons i p) Ξ

/--
`WellTyped Γ p` holds when program `p` is welltyped under `Γ`, *and* the
resulting context is unrestricted.

This enforces that linear variables must be used *at least* once.
-/
@[grind]
def Program.WellTyped (Γ : Context τ n) (p : Program τ n) : Prop :=
  ∃ (Δ : Context τ p.results),
      WellTypedWith Γ p Δ
      ∧ Δ.isUnrestricted

/-!
## Decidability of type checking
--------------------------------------------------------------------------------
-/

inductive Instruction.TypeCheckResult (Γ : Context τ n) (i : Instruction τ n) where
  | isTrue (Δ : Context τ i.results) (h : WellTyped Γ i Δ := by grind)
  | isFalse (h : ∀ {m} (Δ : Context τ m), ¬WellTyped Γ i Δ := by grind)

def Instruction.typeCheck (Γ : Context τ n) : (i : Instruction τ n) → i.TypeCheckResult Γ
  | .loadI t p =>
      if h : Γ[p] = .ptr then
        .isTrue _ (by apply WellTyped.loadI <;> grind)
      else .isFalse
  | .storeI t p x =>
      if h : Γ[p] = .ptr ∧ Γ[x] = t then
        .isTrue _ (by apply WellTyped.storeI <;> grind)
      else .isFalse
  | .loadE t e p =>
      if h : Γ[p] = .ptr then
        .isTrue _ (by apply WellTyped.loadE <;> grind)
      else .isFalse
  | .storeE t e p x =>
      if h : Γ[p] = .ptr then
        .isTrue _ (by apply WellTyped.storeE <;> grind)
      else .isFalse
  | .merge e₁ e₂ => .isFalse
  | .split e => .isFalse
  | .createEff =>
      if h : Γ.isUnrestricted then
        .isTrue _ (by apply WellTyped.createEff <;> grind)
      else .isFalse
  | .consumeEff e => sorry

inductive Program.TypeCheckResult (Γ : Context τ n) (p : Program τ n) where
  | isTrue (Δ : Context τ p.results)
            (h₁ : WellTypedWith Γ p Δ := by grind) (h₂ : Δ.isUnrestricted := by grind)
  | isFalse (h : ∀ {m} (Δ : Context τ m), ¬WellTypedWith Γ p Δ ∨ ¬Δ.isUnrestricted := by grind)

#exit

def Program.typeCheck (Γ : Context τ n) : (p : Program τ n) → p.TypeCheckResult Γ
  | .nil =>
    if h₂ : Γ.isUnrestricted then
      .isTrue Γ .nil h₂
    else
      .isFalse
  | i ;> p =>
    match i.typeCheck Γ with
    | .isFalse h => .isFalse
    | .isTrue Δ hᵢ =>
      match p.typeCheck Δ with
      | .isFalse h => .isFalse
      | .isTrue Δ' h₁ h₂ => .isTrue Δ'

instance : Decidable (Program.WellTyped Γ p) :=
  match p.typeCheck Γ with
  | .isTrue Δ h₁ h₂ => .isTrue <| by use Δ
  | .isFalse h => .isFalse <| by grind
