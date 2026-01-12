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
## WellTyped
-/
open Ty.Typ (ptr eff)

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



inductive Program.WellTyped : Context τ n → Program τ n → Prop
  /--
  An empty program is welltyped under `Γ` only if `Γ` is unrestricted.

  This enforces that linear variables must be used *at least* once.
  -/
  | nil :
      Γ.isUnrestricted →
      ---------------------------------
      WellTyped Γ .nil
  /--
  A program is welltyped if it's instructions are welltyped, under appropriately
  adjusted contexts.
  -/
  | cons :
      Instruction.WellTyped Γ i Δ →
      WellTyped Δ p →
      ---------------------------------
      WellTyped Γ (.cons i p)
