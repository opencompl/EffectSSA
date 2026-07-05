module

public import ITree
public import ITreeExtras.Bisim
public import ITreeExtras.Interp

/-!
# `interpM` Axioms

The `MonadIter` / `LawfulMonadIter` classes and the `interpM` function itself
now live upstream in the `ITree` library. The `Effect.Transform` abbrev and
`⤳` notation now live in `ITreeExtras.Interp`.

This file just carries the two composition axioms that haven't been proven
upstream yet.
-/

@[expose] public section
namespace ITree.ITree

section Interp
variable {E F : Effect.{u}} {R : Type u}
variable (h : ε ⤳ ITree δ)

@[simp, grind =] theorem interp_ret (r : R) :
    interp h (ret r) = return r :=
  interp_pure ..

end Interp

/-!
axiom statements are translated from proven theorems in the rocq itrees library
-/

axiom interpM_interpM (f : ε ⤳ ITree δ) (g : δ ⤳ ITree ζ) (t : ITree ε α) :
    interpM g (interpM f t) = interpM (interpM g <| f ·) t

axiom interpM_iter' {E F} (f : E ⤳ ITree F) {I A}
    (t : I → ITree E (I ⊕ A))
    (t' : I → ITree F (I ⊕ A))
    (EQ_t : ∀ i, interpM f (t i) = t' i) :
    ∀ i, interpM f (ITree.iter t i) = ITree.iter t' i

end ITree.ITree
