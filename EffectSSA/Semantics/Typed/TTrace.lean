import EffectSSA.Types
import EffectSSA.Trace

/-!
# Intrinsically Typed Trace
A program expects to be executed with an ambient trace iff its
context is unrestricted, and it will return an ambient trace iff the returnTypes
are unrestricted. Thus, we encode this into `TTrace Γ` intrinsically typed trace.
-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

noncomputable section -- TODO: #19 remove once ITC has been implemented

@[grind] def Trace.WellTyped (es? : Option (Trace τ)) (Γ : Context τ) : Prop :=
  es?.isSome ↔ Γ.isUnrestricted

/--
`TTrace Γ` encodes an `Option (Trace τ)`, with the invariant that the trace
is present iff `Γ` is unrestricted.
-/
structure TTrace (Γ : Context τ) where
  get? : Option (Trace τ)
  wt : Trace.WellTyped get? Γ := by grind

/-!
## Grind Lemmas
--------------------------------------------------------------------------------
-/
namespace TTrace
variable {Γ : Context τ}

grind_pattern TTrace.wt => TTrace.get? self
@[simp, grind = ] theorem get?_eq_none (es : TTrace Γ) : es.get? = none ↔ ¬Γ.isUnrestricted := by
  grind [Option.not_isSome_iff_eq_none]


/-!
## Coercions
--------------------------------------------------------------------------------
-/
variable {Γ : Context τ}

instance : CoeOut (TTrace Γ) (Option (Trace τ)) where coe := TTrace.get?

/-!
## Definitions
--------------------------------------------------------------------------------
-/

/--
Retrieve the trace, given a proof that the context `Γ` is unrestricted.
-/
def get (t : TTrace Γ) (h : Γ.isUnrestricted := by grind) : Trace τ :=
  t.get?.get (by grind)

@[grind =] theorem get?_eq_none_of (t : TTrace Γ) (h : ¬Γ.isUnrestricted := by grind) :
    t.get? = none := by
  grind [Option.eq_none_of_isNone, Option.not_isSome]

instance : EmptyCollection (TTrace (τ:=τ) ∅) where
  emptyCollection := ⟨some ∅, by grind⟩

/-- `missing` corresponds to a `none : Option (Trace τ)`. -/
def missing (h : ¬Γ.isUnrestricted) : TTrace Γ where
  get? := none

/-!
## Lemmas
--------------------------------------------------------------------------------
-/

@[simp, grind =]
theorem get?_isSome_eq (es : TTrace Γ) : es.get?.isSome = Γ.isUnrestricted := by grind

@[simp, grind =]
theorem get?_missing (h : ¬Γ.isUnrestricted) : get? (missing h) = none := by rfl
