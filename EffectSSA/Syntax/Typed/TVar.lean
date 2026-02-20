import EffectSSA.Syntax.Untyped
import EffectSSA.Types

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
  vs : List.Vector Var ts.length
  wt : ∀ (i : Fin ts.length), Γ[vs[i]]? = some ts[i] := by grind

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

/-!
## TVarList Accessor
--------------------------------------------------------------------------------
-/

def TVarList.get (vs : TVarList Γ ts) (i : Fin ts.length) : TVar Γ ts[i] :=
  .ofVar vs.vs[i]
