module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Assumptions

public import Std.Data.HashMap

/-!
# LocalStack Structure

This file defines a `LocalStack` structure, which is used to assign values to
local (i.e, SSA) variables.
-/
namespace EffectSSA.ProofSketch
public section

open Std (HashMap)

def LocalStack.Raw (ν) :=
  @Quot (Std.HashMap VarId ν) Std.HashMap.Equiv


/-!
## LocalStack Structure
--------------------------------------------------------------------------------
-/

open LocalStack (Raw) in
structure LocalStack (ν) where
  raw : Raw ν

namespace LocalStack
variable {ν}

def empty : LocalStack ν where
  raw := Quot.mk _ (.mk {})
instance : EmptyCollection (LocalStack ν) where emptyCollection := empty

def contains (s : LocalStack ν) (v : VarId) : Bool :=
  Quot.lift (·.contains v) (fun _ _ h => h.contains_eq) s.raw

instance : Membership VarId (LocalStack ν) where
  mem s v := s.contains v
instance (v : VarId) (s : LocalStack ν) : Decidable (v ∈ s) :=
  inferInstanceAs <| Decidable (s.contains v)

@[simp, grind =]
theorem mem_iff (s : LocalStack ν) (v : VarId) : v ∈ s ↔ s.contains v := by rfl

def get? (s : LocalStack ν) (v : VarId) : Option ν :=
  (Quot.lift (fun m : HashMap VarId ν => m[v]?) · s.raw) <| by
    intro a b hab; exact hab.getElem?_eq

def get (s : LocalStack ν) (v : VarId) (h : v ∈ s) : ν :=
  (s.get? v).get <| by
    obtain ⟨raw⟩ := s
    cases raw using Quot.ind
    case mk m =>
      exact HashMap.mem_iff_isSome_getElem?.mp h

instance : GetElem? (LocalStack ν) VarId ν (fun s v => v ∈ s) where
  getElem := get
  getElem? := get?

def insert (s : LocalStack ν) (v : VarId) (x : ν) : LocalStack ν where
  raw := Quot.lift (fun m => Quot.mk _ (m.insert v x))
    (fun _ _ h => Quot.sound (h.insert v x)) s.raw

section Lemmas

@[ext, grind ext]
theorem ext {s t : LocalStack ν} : (h : ∀ v : VarId, s[v]? = t[v]?) → s = t := by
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


abbrev LocalStackT ν := StateT (LocalStack ν)

namespace LocalStackT
variable {m} [Monad m] {ν}

/--
Read the value of variable `v` from the monadic state,
returning `none` if `v` has no value assigned.
-/
def read? (v : VarId) : LocalStackT ν m (Option ν) := do
  let ρ ← get
  return ρ[v]?

/--
Assign value `x` to variable `v` in the monadic state.

This is infallible, overwriting any value already present.
-/
def push (var : VarId) (val : ν) : LocalStackT ν m Unit :=
  modify (·.insert var val)
  -- NOTE: it seems tempting to throw an error here if `x` is already defined.
  -- However, since we never remove variables, a variable being defined twice
  -- does not necessarily indicate a mall-formed program. In particular, the
  -- pre-existing value might actually come from the same instruction in
  -- a previous iteration of a loop.

end LocalStackT
end Expose
