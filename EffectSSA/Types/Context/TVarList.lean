import EffectSSA.Types.Context.Basic
import EffectSSA.Types.Context.Lemmas
import EffectSSA.Types.Context.TVar
import EffectSSA.Types.Context.Hom

/-!
# Intrinsically Well-typed List of Variables

`TVarList Γ Δ` is essentially a list of `TVar`s in the same context `Γ`, but
with different types, as specified by the output context `Δ`.
This can be seen as a context homomorphism `Δ.Hom Γ` (note the reversal of the
contexts), as shown by `TVarList.asHom`.
-/
namespace EffectSSA
variable {τ}

/-
TODO: If `TVarList` is isomorphic to a context isomorphism, do we really need both?

One argument is that they have different tradeoffs: the `TVarList` materializes
the mapping as a list, making it computationally nicer (but we do really care
about this?), whereas the `Hom` definition is easier to compose with an arbitrary
function without needing extra API (although this API certainly could be written
for TVarList as well).

In particular, the TVarList is a natural evolution of specifying return variables
of a program as a list of variables, but `Hom` makes sense for specifying an
arbitrary substitution. Let's see how these things actually get used before
unifying them.
-/

/--
`vs : TVarList Γ Δ` is a list of variables,
such that `vs[i]` is assigned the respective type `Δ[i]` in `Γ`.

Note that this includes that if `Δ[i]` is stale, the corresponding variable
`vs[i]` is required to be stale, too.
-/
structure TVarList (Γ : Context τ) (Δ : Context τ) where
  toList : List Var
  length_eq : toList.length = Δ.size := by grind
  wt : ∀ (i : Fin Δ.size), Γ[toList[i]]? = Δ[Var.ofNat i]? := by grind


/-!
## Grind Attributes
--------------------------------------------------------------------------------
-/

grind_pattern TVar.wt => TVar.toVar self
attribute [grind =] TVarList.wt

grind_pattern TVarList.length_eq => TVarList.toList self

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace TVarList

@[grind] abbrev length (vs : TVarList Γ ts) : Nat := vs.toList.length

/--
A `TVarList Γ Δ` can be seen as a context homomorphism `Δ.Hom Γ`.

This works because a list `vs : TVarList Γ Δ` has exactly as many elements as
variables in `Δ`, and the element of `vs` that corresponds to some `TVar Δ t` is
a `TVar Γ t`.
Thus, the induced morphism just looks up the corresponding entry in the list.
-/
def asHom (vs : TVarList Γ Δ) : Δ.Hom Γ where
  raw v := vs.toList[v.toNat]?.getD v
  ty_eq := by
    intro v t (hv : _ = some _)
    have := vs.wt ⟨v.toNat, by grind⟩
    grind

/--
`vs.get v` returns the variable (in `Γ`) that the list `vs : TVarList Γ Δ`
associates with a variable `v` in `Δ`.

This is an alias for `vs.asHom.apply`.
-/
abbrev get (vs : TVarList Γ Δ) : TVar Δ t → TVar Γ t :=
  vs.asHom.apply

/--
Map a function into a non-dependent type `α` over a TVarList, yielding a regular
(homogeneous) list.

Note that the function is _only_ applied to variables which are live,
any stale variables are mapped to `none` in the resulting list.
-/
def map (f : ∀ {t}, TVar Γ t → α) (vs : TVarList Γ Δ) : List (Option α) :=
  Δ.toList.zipIdx.attach.map fun ⟨⟨t?, i⟩, h⟩ =>
    t?.attach.map fun ⟨t, ht⟩ =>
      let v : TVar Δ t := ⟨.ofNat i, by
        show Δ.toList[i]?.join = some t
        grind⟩
      f (vs.get v)

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
section Lemmas
variable {ts} (f : ∀ {t}, TVar Γ t → α) (vs : TVarList Γ Δ)

attribute [grind =] List.mk_mem_zipIdx_iff_getElem?

@[simp, grind =] theorem length_map : (vs.map f).length = Δ.size := by
  simp [map]

@[grind =]
theorem getElem?_map (i : Nat) :
    (vs.map @f)[i]? =
      let i := Var.ofNat i
      if hi : i.LiveIn Δ then
        some <| some <| @f Δ[i] <| vs.get ⟨i, by grind⟩
      else if i.toNat < Δ.size then
        some none
      else
        none := by
  grind [map, Var.LiveIn, Context.get?]

end Lemmas
