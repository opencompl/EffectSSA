module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.Notation.Refinement

namespace EffectSSA.ProofSketch
public section

/-!
## SSA Assumptions
-/

class SSA (ι : Type) (σ : outParam Type) (ν : outParam Type) : Type where
  [decidableEq : DecidableEq ι]
  [stateRefine : Refinement σ]
  [valRefine : Refinement ν]
  initialState : σ
  denoteInst : ι → σ → List ν → σ × List ν

attribute [implicit_reducible, instance]
  SSA.stateRefine SSA.valRefine SSA.decidableEq

@[reducible] instance SSA.instDenote [ssa : SSA ι σ ν] : Denote ι (σ → List ν → σ × List ν) where
  denote := ssa.denoteInst

/-!
## Environment
-/
section Env
variable [SSA ι σ ν]

/--
A local environment is a partial map from variables to values.
-/
structure LocalEnv (ι) {σ ν} [SSA ι σ ν] : Type where
  get? : VarId → Option ν := fun _ => none

instance : CoeFun (LocalEnv ι) (fun _ => VarId → Option ν) where
  coe := LocalEnv.get?

/--
A stateful environment `ρ : SEnv` consists of a
- local environment, a
- global state, and
- an error flag
-/
structure SEnv (ι) {σ ν} [ssa : SSA ι σ ν] : Type where
  /-- A partial map from local variables (i.e, virtual registers) to values. -/
  locals : LocalEnv ι := { }
  /-- The global state, e.g, for memory and UB -/
  state : σ := ssa.initialState
  /-- Whether an interpretation occurred (indicating a mallformed program). -/
  error : Bool := false

/-! ### LocalEnv API -/
namespace LocalEnv

section Refinement

instance : Refinement (LocalEnv ι) where
  IsRefinedBy ℓ κ := ∀ v, ℓ v ⊒ κ v

@[simp, grind =]
theorem isRefinedBy_iff {ℓ κ : LocalEnv ι} :
    ℓ ⊒ κ ↔ ∀ v, ℓ v ⊒ κ v := by rfl

end Refinement

/--
`ℓ.with? xs vs` returns the local environment `ℓ` with each variable `xs[i]`
set to the corresponding value `vs[i]`,
returining `none` if `xs` and `vs` are of different lengths.
-/
def with? (ℓ : LocalEnv ι) (xs : List VarId) (vs : List ν) : Option (LocalEnv ι) :=
  if xs.length != vs.length then
    none
  else
    some { get? x :=
      match xs.idxOf? x with
      | some idx => vs[idx]?
      | none => ℓ x
    }

def «with» (ℓ : LocalEnv ι) (x : VarId) (v : ν) : LocalEnv ι where
  get? y := if x = y then v else ℓ y

section Lemmas
variable (ℓ : LocalEnv ι)

@[ext, grind ext]
theorem ext {ℓ κ : LocalEnv ι} (h : ∀ x, ℓ x = κ x) : ℓ = κ := by
  cases ℓ; cases κ; congr; funext x; apply h x

@[simp, grind =]
theorem with?_cons_cons : ℓ.with? (x :: xs) (v :: vs) = (·.with x v) <$> ℓ.with? xs vs := by
  simp only [with?, List.length_cons, Nat.reduceBneDiff, bne_iff_ne, ne_eq, ite_not]
  by_cases hl : xs.length = vs.length
  case neg => grind
  case pos =>
    simp only [hl, ↓reduceIte, Option.map_eq_map, Option.map_some, Option.some.injEq]
    congr 1; funext y
    grind

@[simp, grind =]
theorem with?_nil_nil : ℓ.with? [] [] = some ℓ := by
  simp [with?]

@[simp, grind =] theorem get?_with :
    (ℓ.with x v).get? y = if x = y then some v else ℓ y := by rfl


end Lemmas
end LocalEnv

/-! ### SEnv API-/
namespace SEnv

/--
`getD (some ρ)` returns `ρ`, `getD none` returns a default environment
with the `error` flag set. -/
abbrev getD : Option (SEnv ι) → SEnv ι :=
  (Option.getD · { error := true})

section Refinement

/--
We say that a non-erroneous `ρ` is refined by `η`,
written as `ρ ⊒ η`, when:

* `η` is also non-erroneous
* the global state of `ρ` is refined by the global state of `η`, and
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.

An erroneous environment `ρ`, on the other hand, is refined by anything.
-/
instance : Refinement (SEnv ι) where
  IsRefinedBy ρ η := !ρ.error →
    !η.error ∧ ρ.state ⊒ η.state ∧ (∀ v, ρ.locals v ⊒ η.locals v)

variable {ρ η : SEnv ι}

@[grind =]
theorem isRefinedBy_iff : ρ ⊒ η ↔ !ρ.error →
    !η.error ∧ ρ.state ⊒ η.state ∧ (∀ v, ρ.locals v ⊒ η.locals v) := by rfl

@[simp, grind =>]
theorem isRefinedBy_of_error :
    ρ.error → ρ ⊒ η := by
  simp [(· ⊒ ·)]; grind

@[simp, grind =>]
theorem isRefinedBy_iff_of_error_right {ρ η : SEnv ι} :
    η.error → (ρ ⊒ η ↔ ρ.error) := by
  simp [(· ⊒ ·)]; grind

end Refinement
end SEnv
end Env

/-!
## Axiomatized SSA Instance
-/

axiom OpCode : Type

/-- The type of runtime values. -/
axiom Val : Type

/-- The type of global runtime state (e.g., memory). -/
axiom State : Type

/-- `SSA` instance for the concrete `Inst` type. -/
@[instance] axiom instSSA : SSA OpCode State Val

end
