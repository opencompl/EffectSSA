module

public import ITree

/-!
# ITree `HasEffect` and `MayReturn` Predicates
-/

@[expose] public section
namespace ITree.ITree

/--
`t.HasEffect e` holds when the effect `e : ε.I` is used to label any node in tree `t`.
-/
coinductive HasEffect : ITree ε α → ε.I → Prop where
  | vis {t i} {k : ε.O i → ITree ε α} :
      t.unfold = .vis i k → HasEffect t i
  | vis_cont {t i i'} {k : ε.O i' → ITree ε α} {o} :
      t.unfold = .vis i' k → HasEffect (k o) i → HasEffect t i
  | tau {t i t'} :
      t.unfold = .tau t' → HasEffect t' i → HasEffect t i

/--
`t.MayReturn x` hodlds when there is a leaf `ret x` anywhere in tree `t`.
-/
coinductive MayReturn : ITree ε α → α → Prop where
  | ret {t r} : t.unfold = .ret r → MayReturn t r
  | tau {t r t'} : t.unfold = .tau t' → MayReturn t' r → MayReturn t r
  | vis  {t r i} {k : ε.O i → ITree ε α} {o}
         : t.unfold = .vis i k → MayReturn (k o) r → MayReturn t r


/-! ## Lemmas -/
section Lemmas

/-! ### HasEffect -/


/-! ### MayReturn -/


end Lemmas
