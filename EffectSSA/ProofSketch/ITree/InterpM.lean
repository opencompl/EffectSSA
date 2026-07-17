module

public import ITreeExtras
public import ITreeExtras.Interp

/-!
# `interpM` Axioms

`MonadIter`, `LawfulMonadIter`, `interpM`, and their basic lemmas are now
provided by `ITreeExtras`. This file carries only the composition axioms
that haven't been proven upstream yet.
-/

@[expose] public section
namespace ITree.ITree

section Interp
variable {ε δ : Type} {κε : ε → Type} {κδ : δ → Type} [Effect ε κε] [Effect δ κδ]
variable (h : ε ⤳ ITree δ) {R : Type}

@[simp, grind =] theorem interp_ret (r : R) :
    interp h (ret r) = ret r :=
  interp_pure ..

end Interp

/-!
axiom statements translated from proven theorems in the Rocq ITrees library

TODO: I'm not sure these are actually needed anymore; but they might become
useful later
-/

axiom interpM_interpM {ε δ ζ : Type} {κε : ε → Type} {κδ : δ → Type} {κζ : ζ → Type}
    [Effect ε κε] [Effect δ κδ] [Effect ζ κζ] {R : Type}
    (f : ε ⤳ ITree δ) (g : δ ⤳ ITree ζ) (t : ITree ε R) :
    interpM g (interpM f t) = interpM (fun e => interpM g (f e)) t

axiom interpM_iter' {ε δ : Type} {κε : ε → Type} {κδ : δ → Type}
    [Effect ε κε] [Effect δ κδ] {I A : Type}
    (f : ε ⤳ ITree δ)
    (t : I → ITree ε (I ⊕ A)) (t' : I → ITree δ (I ⊕ A))
    (EQ_t : ∀ i, interpM f (t i) = t' i) :
    ∀ i, interpM f (ITree.iter t i) = ITree.iter t' i

end ITree.ITree
