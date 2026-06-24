module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.ITree.InterpM
public import EffectSSA.ProofSketch.ITree.HasEffect
public import EffectSSA.ProofSketch.ITree.Stub

public import ITree

public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Basic

/-! ## Upstream -/
namespace ITree.ITree
@[expose] public section

-- interpSum

def interpFirst
    (f : (e : ε.I) → ITree δ (ε.O e)) :
    ITree (ε ⊕ₑ δ) α → ITree δ α :=
  interp (Sum.casesOn · f δ.trigger)


-- iter_iter

-- theorem interp_iter' {ε₁ ε₂ : Effect}
--     {f : (i : ε₁.I) → ITree ε₂ (ε₁.O i)}
--     {t₁ : α → ITree ε₁ (α ⊕ β)}
--     {t₂ : α → ITree ε₂ (α ⊕ β)}
--     (ht : ∀ i, interp f (t₁ i) = t₂ i) :
--     ∀ i, ITree.interp f (ITree.iter t₁ i) = ITree.iter t₂ i := by
--   sorry

end
end ITree.ITree

/-!
# Effects
-/
@[expose] public section
namespace EffectSSA.ProofSketch
open ITree
open Effect (trigger)
open MonadIter (iter)

/-!
## Errors / UB
--------------------------------------------------------------------------------
-/

inductive ErrUBKind
  | ub (reason : String)
  | error (reason : String)

/--
`ErrUB` allows raising errors (which indicate a mallformed program)
as well as Undefined Behaviour.
-/
def ErrUB : ITree.Effect where
  I := ErrUBKind
  O _ := Empty

/-! ### Helpers -/

def raiseUB [ErrUB -< ε] (reason := "") : ITree ε α :=
  trigger ErrUB (.ub reason) >>= Empty.elim

def raiseError [ErrUB -< ε] (reason := "") : ITree ε α :=
  trigger ErrUB (.error reason) >>= Empty.elim

/-!
## Opaque Side Effects
--------------------------------------------------------------------------------
-/

/--
Let `SideEff` be some arbitrary set of language-specific side-effects.
This could, e.g, model memory operations.
-/
axiom SideEff : ITree.Effect

/-!
## Hole Execution
--------------------------------------------------------------------------------
-/

structure HoleId where
  toNat : Nat
instance : ToString HoleId where toString h := s!"{h.toNat}"

/--
We consider a (multi-)context to be a program with holes in it.
Such programs can be denoted into an ITree with each hole id having a unique
placeholder effect in `HoleEff`.

Note that although holes in the AST have an intrinsically typed upper bound,
`HoleEff` carries only the raw `Nat`-typed id of the hole, to prevent too many
depedent types showing up in the semantics.
-/
def HoleEff : ITree.Effect where
  I := HoleId
  O _ := Unit

/-! ### Helper -/

/-- Continue execution at the instructions that will be substituted for hole `h`. -/
def jumpToHole (h : HoleId) : ITree HoleEff Unit :=
  .vis h .ret

/-! ### Interpretation -/

-- TODO: docstring
def interpHoles [ε -< δ] (f : HoleId → ITree ε Unit) :
    (x : ITree (HoleEff ⊕ₑ δ) α) → ITree δ α :=
  ITree.interpFirst (f · |>.lift)

/--
`interpHoles'` is an alias of `interpHoles` for the special case where `ε = δ`.

It can be used to avoid having to specify `ε` when Lean fails to infer it.
-/
@[simp, grind]
abbrev interpHoles'  : (f : HoleId → ITree δ Unit) →
    (x : ITree (HoleEff ⊕ₑ δ) α) → ITree δ α :=
  interpHoles

/-!
## Local Stack Effects
--------------------------------------------------------------------------------
-/

structure VarId where
  raw : String
  deriving DecidableEq, Hashable
instance : ToString VarId where toString := VarId.raw

/-- `Val` is the type of runtime values -/
axiom Val : Type

inductive LocalEffKind
  | read (var : VarId)
  | push (var : VarId) (value : Val)

def LocalEff : ITree.Effect where
  I := LocalEffKind
  O := fun
    | .read _ => Val
    | .push _ _ => Unit

/-! ### Helpers -/

def readVar [LocalEff -< ε] (var : VarId) : ITree ε Val :=
  trigger (E₁ := LocalEff) <| .read var

def pushVar [LocalEff -< ε] (var : VarId) (value : Val) : ITree ε Unit :=
  trigger (E₁ := LocalEff) <| .push var value

/-! ### Interpretation -/

structure LocalStack where
  raw : Std.HashMap VarId Val := { }

def interpLocalStackM [ErrUB -< ε] :
    (x : ITree (LocalEff ⊕ₑ ε) α) → StateT LocalStack (ITree ε) α :=
  ITree.interpM fun
    | .inr e => liftM <| ITree.vis e .ret
    | .inl (.read x) => do
        let ρ ← get
        let some val := ρ.raw[x]? |
          liftM <| raiseError (ε:=ε) s!"Unknown variable: {x}"
        return val
    | .inl (.push x val) => do
        modify (⟨·.raw.insert x val⟩)
        -- NOTE: it seems tempting to throw an error here if `x` is already defined.
        -- However, since we never remove variables, a variable being defined twice
        -- does not necessarily indicate a mall-formed program. In particular, the
        -- pre-existing value might actually come from the same instruction in
        -- a previous iteration of a loop.

/-- Interpret local stack effects starting from an empty initial stack. -/
def interpLocalStack [ErrUB -< ε] (x : ITree (LocalEff ⊕ₑ ε) α) : ITree ε α :=
  (interpLocalStackM x).run' { }

/-!
## Instructions
--------------------------------------------------------------------------------
-/

/-!
We assume an arbitrary types of instructions, which we can cleanly "denote" by
considering each instructions as a unique effect without output. The result of
an instruction is added to the environment via the `LocalStack` push side effect.

N.B: Terminators are *not* considered effects, since we want to unroll the CFG
structure right away.
-/

/-- In `InstEff`, each instruction is a unique effect. -/
@[expose] def InstEff : ITree.Effect where
  I := Inst
  O _ := Unit

/-! ### Handler -/

axiom handleInst [ErrUB -< ε] [SideEff -< ε] [LocalEff -< ε] : (i : Inst) → ITree ε Unit

noncomputable
def interpInst [ErrUB -< ε] [SideEff -< ε] [LocalEff -< ε] :
    ITree (InstEff ⊕ₑ ε) α → ITree ε α :=
  ITree.interpFirst handleInst
