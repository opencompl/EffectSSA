import EffectSSA.Types.Context.Basic

/-!
# Intrinsically Well-typed Variables
-/
namespace EffectSSA
variable {τ}

/--
`TVar Γ t` is a variable which is guaranteed to be assigned
type `t` in context `Γ`.
-/
structure TVar (Γ : Context τ) (t : τ.Typ) where
  ofVar ::
    toVar : Var
    wt : Γ[toVar]? = some t := by grind

/--
`vs : TVarList Γ ts` is a list of variables, such that `vs[i]`
is assinged the respective type `ts[i]` in `Γ`.
-/
structure TVarList (Γ : Context τ) (ts : List τ.Typ) where
  toList : List Var
  length_eq : toList.length = ts.length := by grind
  wt : ∀ (i : Fin ts.length), Γ[toList[i]]? = some ts[i] := by grind

/-!
## Coercions
--------------------------------------------------------------------------------
The typed structures can be implicitly coerced into the underlying
untyped variants
-/
variable {Γ : Context τ}

instance : CoeOut (TVar Γ t) Var where coe := TVar.toVar

/-!
## Grind Attributes
--------------------------------------------------------------------------------
-/

grind_pattern TVar.wt => TVar.toVar self
attribute [grind =] TVarList.wt

grind_pattern TVarList.length_eq => TVarList.toList self

/-!
## TVarList Definitions
--------------------------------------------------------------------------------
-/
namespace TVarList

@[grind] abbrev length (vs : TVarList Γ ts) : Nat := vs.toList.length

/--
Map a function into a non-dependent type `α` over a TVarList
-/
def map (f : ∀ {i : Fin ts.length}, TVar Γ ts[i] → α) (vs : TVarList Γ ts) : List α :=
  vs.toList.zipIdx.attach.map fun ⟨⟨v, i⟩, h⟩ =>
    have : vs.toList.length = ts.length := by grind
    let i : Fin ts.length := ⟨i, by grind⟩
    let v : TVar Γ ts[i] := ⟨v, by
      have : vs.toList[i] = v := by
        show vs.toList[i] = v; grind
      grind⟩
    f v

def get (vs : TVarList Γ ts) (i : Fin ts.length) : TVar Γ ts[i] :=
  .ofVar <| vs.toList[i]'(by grind)

end TVarList

/-!
## TVarList Lemmas
--------------------------------------------------------------------------------
-/
namespace TVarList
variable {ts} (f : ∀ {i : Fin ts.length}, TVar Γ ts[i] → α) (vs : TVarList Γ ts)

@[simp] theorem length_map : (vs.map f).length = vs.length := by
  simp [map]

@[grind =]
theorem getElem?_map  (i : Nat) :
    (vs.map @f)[i]? =
      if hi : i < ts.length then
        some <| f <| vs.get ⟨i, hi⟩
      else
        none := by
  split
  · simp [map];
    use vs.toList[i]'(by grind)
    and_intros
    · grind
    · use (by grind)
      congr
  · simp; grind
