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

/--
`getD (some ρ)` returns `ρ`, `getD none` returns a default environment
with the `error` flag set. -/
abbrev SEnv.getD : Option (SEnv ι) → SEnv ι :=
  (Option.getD · { error := true})

/-! ### LocalEnv API -/
namespace LocalEnv

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
