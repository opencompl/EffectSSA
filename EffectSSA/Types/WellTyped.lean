import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax
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
open Ty.Typ (ptr eff data)

inductive Instruction.WellTyped : Context τ → Instruction τ → Context τ → Prop
  | loadI :
      Γ[p]? = some ptr →
      ---------------------------------
      WellTyped Γ (.loadI t p) (Γ <: t)

  | storeI :
      Γ[p]? = some ptr →
      Γ[x]? = some (data t) →
      -- FIXME: I would prefer writing `Γ[x] = t` here, but then Lean searches
      --   for (and fails to find) a `GetElem` instance with `τ.DType` as the
      --   return value, instead of the intended `τ.Typ` return value to which
      --   `τ.DType` can be coerced. I should minimize and report this.
      ---------------------------------
      WellTyped Γ (.storeI t p x) Γ

  | loadE :
      Γ[e]? = some eff →
      Γ[p]? = some ptr →
      ---------------------------------
      WellTyped Γ (.loadE t e p) (Γ.eraseVar e <: eff <: t)

  | storeE :
      Γ[e]? = some eff →
      Γ[p]? = some ptr →
      Γ[x]? = some (data t) →
      ---------------------------------
      WellTyped Γ (.storeE t e p x) (Γ.eraseVar e <: eff)

  | createEff :
      Γ.isUnrestricted →
      ---------------------------------
      WellTyped Γ .createEff (Γ <: eff)

  | consumeEff :
      Γ[e]? = some eff →
      (Γ.eraseVar e).isUnrestricted →
      ---------------------------------
      WellTyped Γ (.consumeEff e) (Γ.eraseVar e)


/--
`WellTypedWith Γ p Δ` holds when the instruction in sequence `p` are welltyped
under `Γ`, and result in a final context `Δ` after execution.

NOTE: linearity is not yet checked
-/
inductive InstructionSeq.WellTypedWith : Context τ → InstructionSeq τ → Context τ → Prop
  /--
  An empty program does not change the context.

  NOTE: This does *not* yet enforce that linear variables must be used.
  -/
  | nil (h : Γ = Δ) : WellTypedWith Γ .nil Δ
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
`WellTyped Γ p ts` holds for a program `p`, when the constituent instruction
sequence `p` is welltyped under `Γ`, returning an *unrestricted* context `Δ`
such that the i-th return variable of `p` is assigned the respective type
`ts[i]` in context `Δ`

NOTE: The requirement that `Δ` is unrestricted enforces that linear variables
must be used *at least* once.
-/
@[grind =]
def Program.WellTyped (Γ : Context τ) (p : Program τ) (ts : List τ.Typ) : Prop :=
  ∃ (Δ : Context τ),
    InstructionSeq.WellTypedWith Γ p.instructions Δ
    ∧ Δ.isUnrestricted
    -- And the returnVariables' types match `ts`
    ∧ p.returnVars.length = ts.length
    ∧ ∀ (i : Nat), (hi : i < p.returnVars.length) →
        Δ[p.returnVars[i]]? = ts[i]?
