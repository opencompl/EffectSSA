module

public import EffectSSA.ProofSketch.Inst

public import ITreeExtras

public import Std.Data.HashMap

/-!
# Effects
-/
@[expose] public section
namespace EffectSSA.ProofSketch
open ITree
open Effect (trigger)
open MonadIter (iter)

variable {ε : Type} {κε : ε → Type} [Effect ε κε]
         {δ : Type} {κδ : δ → Type} [Effect δ κδ]
         {α : Type}

/-!
## Errors / UB
--------------------------------------------------------------------------------
-/

/--
`ErrUB` allows raising errors (which indicate a mallformed program)
as well as Undefined Behaviour.
-/
inductive ErrUB
  | ub (reason : String)
  | error (reason : String)

instance : Effect ErrUB (fun _ => Empty) := ⟨⟩

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
axiom SideEff : Type
axiom SideEff.κ : SideEff → Type
instance : Effect SideEff SideEff.κ := ⟨⟩

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
abbrev HoleEff := HoleId

instance : Effect HoleEff (fun _ => Unit) := ⟨⟩

/-! ### Helper -/

/-- Continue execution at the instructions that will be substituted for hole `h`. -/
def jumpToHole (h : HoleId) : ITree HoleEff Unit :=
  .vis h .ret

/-! ### Interpretation -/

/-- Interpret hole effects by delegating each hole id to `f`. -/
def interpHoles [ε -< δ] (f : HoleId → ITree ε Unit) :
    (x : ITree (HoleEff ⊕ δ) α) → ITree δ α :=
  ITree.interpLeft (f · |>.lift)

/--
`interpHoles'` is an alias of `interpHoles` for the special case where `ε = δ`.

It can be used to avoid having to specify `ε` when Lean fails to infer it.
-/
@[simp, grind]
abbrev interpHoles'  : (f : HoleId → ITree δ Unit) →
    (x : ITree (HoleEff ⊕ δ) α) → ITree δ α :=
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

inductive LocalEff
  | read (var : VarId)
  | push (var : VarId) (value : Val)

instance : Effect LocalEff (fun
    | .read _ => Val
    | .push _ _ => Unit) := ⟨⟩

/-! ### Helpers -/

def readVar [LocalEff -< ε] (var : VarId) : ITree ε Val :=
  trigger LocalEff <| .read var

def pushVar [LocalEff -< ε] (var : VarId) (value : Val) : ITree ε Unit :=
  trigger LocalEff <| .push var value

/-! ### Interpretation -/

structure LocalStack where
  raw : Std.HashMap VarId Val := { }

def interpLocalStackM [ErrUB -< ε] :
    (x : ITree (LocalEff ⊕ ε) α) → StateT LocalStack (ITree ε) α :=
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
def interpLocalStack [ErrUB -< ε] (x : ITree (LocalEff ⊕ ε) α) : ITree ε α :=
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
abbrev InstEff := Inst

instance : Effect InstEff (fun _ => Unit) := ⟨⟩

/-! ### Handler -/

axiom handleInst [ErrUB -< ε] [SideEff -< ε] [LocalEff -< ε] : (i : Inst) → ITree ε Unit

noncomputable
def interpInst [ErrUB -< ε] [SideEff -< ε] [LocalEff -< ε] :
    ITree (InstEff ⊕ ε) α → ITree ε α :=
  ITree.interpLeft handleInst
