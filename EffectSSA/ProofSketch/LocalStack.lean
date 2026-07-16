module

public import EffectSSA.ProofSketch.VarSet

import Std.Data.HashMap

/-!
# LocalStack Structure

This file defines a `LocalStack` structure, which is used to assign values to
local (i.e, SSA) variables.
-/
namespace EffectSSA.ProofSketch
public section

open Std (HashMap)

/-- `Val` is the type of runtime values -/
axiom Val : Type

def LocalStack.Raw :=
  @Quot (Std.HashMap VarId Val) Std.HashMap.Equiv


/-!
## LocalStack Structure
--------------------------------------------------------------------------------
-/

open LocalStack (Raw) in
structure LocalStack where
  raw : Raw

namespace LocalStack

def empty : LocalStack where
  raw := Quot.mk _ (.mk {})
instance : EmptyCollection LocalStack where emptyCollection := empty

def contains (s : LocalStack) (v : VarId) : Bool :=
  Quot.lift (·.contains v) (fun _ _ h => h.contains_eq) s.raw

instance : Membership VarId LocalStack where
  mem s v := s.contains v
instance (v : VarId) (s : LocalStack) : Decidable (v ∈ s) :=
  inferInstanceAs <| Decidable (s.contains v)

@[simp, grind =]
theorem mem_iff (s : LocalStack) (v : VarId) : v ∈ s ↔ s.contains v := by rfl

def get? (s : LocalStack) (v : VarId) : Option Val :=
  (Quot.lift (fun m : HashMap VarId Val => m[v]?) · s.raw) <| by
    intro a b hab; exact hab.getElem?_eq

def get (s : LocalStack) (v : VarId) (h : v ∈ s) : Val :=
  (s.get? v).get <| by
    obtain ⟨raw⟩ := s
    cases raw using Quot.ind
    case mk m =>
      exact HashMap.mem_iff_isSome_getElem?.mp h

instance : GetElem?  LocalStack VarId Val (fun s v => v ∈ s) where
  getElem := get
  getElem? := get?

def insert (s : LocalStack) (v : VarId) (x : Val) : LocalStack where
  raw := Quot.lift (fun m => Quot.mk _ (m.insert v x))
    (fun _ _ h => Quot.sound (h.insert v x)) s.raw

section Lemmas

@[ext, grind ext]
theorem ext {s t : LocalStack} : (h : ∀ v : VarId, s[v]? = t[v]?) → s = t := by
  rcases s with ⟨s⟩
  cases s using Quot.ind
  case mk s =>
  rcases t with ⟨t⟩
  cases t using Quot.ind
  case mk t =>
  intro (h : ∀ v : VarId, s[v]? = t[v]?)
  suffices s.Equiv t by
    simp only [Quot.sound this]
  apply HashMap.Equiv.of_forall_getElem?_eq h

end Lemmas
end LocalStack

/-!
## LocalStackT Monad Transformer
--------------------------------------------------------------------------------
-/
@[expose] public section Expose

abbrev LocalStackT := StateT LocalStack

namespace LocalStackT
variable {m} [Monad m]

/--
Read the value of variable `v` from the monadic state,
returning `none` if `v` has no value assigned.
-/
def read? (v : VarId) : LocalStackT m (Option Val) := do
  let ρ ← get
  return ρ[v]?

/--
Assign value `x` to variable `v` in the monadic state.

This is infallible, overwriting any value already present.
-/
def push (var : VarId) (val : Val) : LocalStackT m Unit :=
  modify (·.insert var val)
  -- NOTE: it seems tempting to throw an error here if `x` is already defined.
  -- However, since we never remove variables, a variable being defined twice
  -- does not necessarily indicate a mall-formed program. In particular, the
  -- pre-existing value might actually come from the same instruction in
  -- a previous iteration of a loop.

end LocalStackT
end Expose
