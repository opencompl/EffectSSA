module

public import ITreeExtras.Definition
public import ITreeExtras.Iter

/-!
# Monadic Interpretation of ITrees (`interpM`)

Vendored from the `ITree` library
(https://github.com/ISTA-PLV/coinductive, `ITree/InterpM.lean`,
upstream rev `d1aeffe87ec7bd4bd13ed92fdc00ef6c5d58f800`).

Kept verbatim to minimise the maintenance burden of re-syncing with upstream.

`ITree.interpM` interprets an `ITree ε α` into any monad `m` equipped with a loop/iteration
operator (`MonadIter`).

This generalises `ITree.interp` (which targets only another ITree) to arbitrary monads,
matching the `interp` function from the Rocq library.

## Main declarations

* `MonadIter`: typeclass for monads with a loop/iteration combinator
* `LawfulMonadIter`: a lawful iter combinator can be unfolded
* `ITree.interpM`: interpret an `ITree ε α` into any `MonadIter`-monad

Additionally, instances of (`Lawful`)`MonadIter` are provided for:
* `ITree ε`, and
* `StateT σ m`, assuming that `m` has a (`Lawful`)`MonadIter` instance,

## References

* Rocq InteractionTrees library:
  <https://deepspec.github.io/InteractionTrees/master/ITree.Basics.Basics.html#MonadIter>
-/

@[expose] public section
namespace ITree

/-! ## MonadIter Classes -/

/--
`MonadIter m` indicates that `m` is a monad with a loop/iteration combinator.
-/
class MonadIter (m : Type u → Type u) where
  /--
  `iter f init` is a loop/iteration combinator.

  The precise meaning is defined by the `MonadIter` instance on the monad `m`,
  but the intention is that this runs the function `f` repeatedly, starting from
  initial state `init`, where:

  - if `f` returns `inl a`, the loop continues from the new state `a`, and
  - if `f` returns `inr b`, the loop terminates and returns the result `b`.
  -/
  iter : {α β : Type u} → (f : α → m (α ⊕ β)) → (init : α) → m β
open MonadIter (iter)

/--
A `MonadIter` satisfying the unfolding equation: one step of `iter` peels off
one call to `f`, then either loops (`.inl`) or returns (`.inr`).
-/
class LawfulMonadIter (m : Type u → Type u) [Monad m] [MonadIter m] where
  tau : ∀ {α}, m α → m α
  iter_eq : ∀ {α β : Type u} (f : α → m (α ⊕ β)) (init : α),
    MonadIter.iter f init =
      f init >>= fun
        | .inl a => tau <| MonadIter.iter f a
        | .inr b => return b

variable {ι : Type u} {ε : ι → Type u} {α}
variable {m : Type u → Type u} [Monad m] [MonadIter m]

section Instances

/-! ### ITree -/

/-- `ITree` is a (lawful) `MonadIter`. -/
instance : MonadIter (ITree ε) where iter := ITree.iter

@[simp] theorem ITree.iter_eq : @MonadIter.iter (ITree ε) _ α β = ITree.iter := by rfl

instance : LawfulMonadIter (ITree ε) where
  tau := ITree.tau
  iter_eq f a := by
    rw [ITree.iter_eq, ITree.iter]
    congr 1; grind


/-! ### StateT -/
section State
variable {σ : Type u} {m : Type u → Type u} [Monad m] [Functor m] [MonadIter m]

/-- `StateT σ m` is a (lawful) `MonadIter` when `m` is, threading the state through each step. -/
instance : MonadIter (StateT σ m) where
  iter f a s :=
    MonadIter.iter (init := (a, s)) <| fun (a, s) =>
      (fun (ba, s) => ba.map (·, s) (·, s)) <$> (f a).run s

omit [Monad m] in
@[simp, grind =] theorem StateT.run_iter {f : α → StateT σ m (α ⊕ β)}  :
    StateT.run (iter (m := StateT σ m) f a) s
    = iter (fun (a, s) => (fun (ba, s) => ba.map (·, s) (·, s)) <$> (f a).run s) (a, s) := by
  rfl

attribute [simp, grind] LawfulMonadIter.tau
instance {σ : Type u} {m : Type u → Type u} [Monad m] [LawfulMonad m]
    [MonadIter m] [im : LawfulMonadIter m] : LawfulMonadIter (StateT σ m) where
  tau x := im.tau ∘ x
  iter_eq f a := by
    ext s
    rw [StateT.run_iter, StateT.run_bind, im.iter_eq]
    simp only [bind_map_left]
    congr 1; funext ⟨ba, s⟩; cases ba <;> rfl

end State
end Instances

/-! ## Monadic ITree Interpretation -/
namespace ITree

/--
Map an `ITree ε α` into a generic monad `m` equiped with a `MonadIter` instance,
using handler `h` to interpret effects.

See also `ITree.interp` for a specialization where the target monad is an `ITree`,
do note that `interp` and `interpM (m := ITree _)` differ slightly in how they
handle `tau`s in the given `ITree`.
-/
def interpM (h : (i : ι) → m (ε i)) : ITree ε α → m α :=
  MonadIter.iter fun t =>
    match t.unfold with
    | .ret r   => return (.inr r)
    | .tau t'  => return (.inl t')
    | .vis i k => h i >>= fun o => return (.inl (k o))

section Lemmas
variable [LawfulMonad m] [LawfulMonadIter m] (h : (i : ι) → m (ε i))

@[simp, grind =] theorem interpM_ret (r : α) :
    interpM h (ret r) = return r := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

@[simp, grind =] theorem interpM_pure (r : α) :
    interpM h (pure r) = return r :=
  interpM_ret ..

@[simp, grind =] theorem interpM_tau (t : ITree ε α) :
    interpM h (.tau t) = LawfulMonadIter.tau (interpM h t) := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

@[simp, grind =] theorem interpM_vis (i : ι) (k : ε i → ITree ε α) :
    interpM h (vis i k) = (do
      let o ← h i
      LawfulMonadIter.tau <| interpM h (k o)) := by
  rw [interpM, LawfulMonadIter.iter_eq]; simp

end Lemmas
end ITree
end ITree
