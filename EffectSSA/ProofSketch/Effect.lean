module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.Hole

public import ITreeExtras

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.LocalStack
public import EffectSSA.ProofSketch.Hole

/-!
# Effects
-/
@[expose] public section
namespace EffectSSA.ProofSketch
open ITree
open Effect (trigger)
open MonadIter (iter)

variable {ι : Type} {ε : ι → Type}
         {ιδ : Type} {δ : ιδ → Type}
         {α : Type}

/-!
## Errors / UB
--------------------------------------------------------------------------------
-/

/--
`ErrUB` allows raising errors (which indicate a malformed program)
as well as Undefined Behaviour.
-/
inductive ErrUB
  | ub (reason : String)
  | error (reason : String)

/-- The `ErrUB` effect family: raising an error yields no continuation. -/
abbrev ErrUBE : ErrUB → Type := fun _ => Empty

/-! ### Helpers -/

def raiseUB [ErrUBE -< ε] (reason := "") : ITree ε α :=
  trigger ErrUBE (.ub reason) >>= Empty.elim

def raiseError [ErrUBE -< ε] (reason := "") : ITree ε α :=
  trigger ErrUBE (.error reason) >>= Empty.elim

section Lemmas
open Subeffect (map)

@[simp, grind =]
theorem bind_raiseUB [ErrUBE -< ε] {α β} (reason : String) (f : α → ITree ε β) :
    raiseUB reason >>= f = raiseUB reason := by
  rw [raiseUB, bind_assoc]
  exact congrArg _ <| funext (·.elim)

@[simp, grind =]
theorem bind_raiseError [ErrUBE -< ε] {α β} (reason : String) (f : α → ITree ε β) :
    raiseError reason >>= f = raiseError reason := by
  rw [raiseError, bind_assoc]
  exact congrArg _ <| funext (·.elim)

@[simp, grind =]
theorem interpLeft_raiseError [ErrUBE -< δ] (f : ε ⤳ ITree δ) (reason : String) :
    ITree.interpLeft f (raiseError reason : ITree (ε ⊕ₑ δ) α)
      = raiseError reason := by
  simp only [raiseError, ITree.interpLeft_bind, tau_bind, ITree.bind_ret,
    ITree.interpLeft_trigger_inr f (ErrUB.error reason), ITree.pure_eq_ret, bind_assoc]
  congr; grind

@[grind =]
theorem raiseError_eq_vis_iff [ErrUBE -< ε] {reason : String} {j : ι}
    {k : ε j → ITree ε α} :
    (raiseError reason : ITree ε α) = ITree.vis j k ↔
    (map (ε₁:=ErrUBE) (ε₂:=ε) (.error reason)).fst = j ∧
    (fun x : ε (map (ε₁ := ErrUBE) (ε₂:=ε) (.error reason)).fst =>
      (Empty.elim ((map (ε₁ := ErrUBE) (ε₂:=ε) (.error reason)).snd x) : ITree ε α)) ≍ k := by
  simp [raiseError, trigger]

end Lemmas

/-!
## Opaque Side Effects
--------------------------------------------------------------------------------
-/

/--
Let `SideEff` be some arbitrary set of language-specific side-effects.
This could, e.g, model memory operations.
-/
axiom SideEff : Type
axiom SideEffE : SideEff → Type

/-!
## Hole Execution
--------------------------------------------------------------------------------
-/

/--
We consider a (multi-)context to be a program with holes in it.
Such programs can be denoted into an ITree with each hole id having a unique
placeholder effect in `HoleEff`.

Note that although holes in the AST have an intrinsically typed upper bound,
`HoleEff` carries only the raw `Nat`-typed id of the hole, to prevent too many
dependent types showing up in the semantics.
-/
abbrev HoleEff : HoleId → Type := fun _ => Unit

/-! ### Helper -/

/-- Continue execution at the instructions that will be substituted for hole `h`. -/
def jumpToHole (h : HoleId) : ITree HoleEff Unit :=
  .vis h .ret

/-! ### Interpretation -/

/-- Interpret hole effects by delegating each hole id to `f`. -/
def interpHoles [ε -< δ] (f : HoleId → ITree ε Unit) :
    (x : ITree (HoleEff ⊕ₑ δ) α) → ITree δ α :=
  ITree.interpLeft (f · |>.lift)

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

inductive LocalEff
  | read (var : VarId)
  | push (var : VarId) (value : Val)

/-- The `LocalEff` family: reads return a value, pushes return unit. -/
abbrev LocalEffE : LocalEff → Type
  | .read _ => Val
  | .push _ _ => Unit

/-! ### Helpers -/

def readVar [LocalEffE -< ε] (var : VarId) : ITree ε Val :=
  trigger LocalEffE <| .read var

def pushVar [LocalEffE -< ε] (var : VarId) (value : Val) : ITree ε Unit :=
  trigger LocalEffE <| .push var value

section Lemmas
variable [LocalEffE -< ε]
open Subeffect (map)

@[simp, grind =]
theorem hasEffect_pushVar {e : ι} :
    (pushVar (ε:=ε) var value).HasEffect e
    ↔ (Subeffect.map (ε₁ := LocalEffE) (ε₂ := ε) (.push var value)).fst = e := by
  simp [pushVar, Effect.trigger]

end Lemmas

/-! ### Interpretation -/

def interpLocalStackM [ErrUBE -< ε] :
    (x : ITree (LocalEffE ⊕ₑ ε) α) → StateT LocalStack (ITree ε) α :=
  ITree.interpM fun
    | .inr e => liftM <| ITree.vis e .ret
    | .inl (.read x) => do
        let val? ← LocalStackT.read? x
        match val? with
        | some val => return val
        | none => liftM <| raiseError (ε:=ε) s!"Unknown variable: {x}"
    | .inl (.push x val) => LocalStackT.push x val


/-- Interpret local stack effects starting from an empty initial stack. -/
def interpLocalStack [ErrUBE -< ε] (x : ITree (LocalEffE ⊕ₑ ε) α) : ITree ε α :=
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
abbrev InstEff : Inst → Type := fun _ => Unit

/-!
## Effect Aliasses
--------------------------------------------------------------------------------
-/

/--
`BaseEff` gives the "base" effects, which is some arbitrary notion of
side-effects enriched with errors and UB.
-/
abbrev BaseEff := SideEffE ⊕ₑ ErrUBE

/--
`InterpEff` gives the effects into which instructions and terminators are
interpreted.
-/
noncomputable
abbrev InterpEff := LocalEffE ⊕ₑ SideEffE ⊕ₑ ErrUBE

/--
`OpaqueEff` is the totality of effects resulting from unrolling a (closed) CFG
(which includes interpreting terminators),
*before* interpreting individual instructions.

That is, each instruction is still an "opaque" effect.
-/
noncomputable
abbrev OpaqueEff := InstEff ⊕ₑ InterpEff

/--
`OpaqueCtxEff` is the totality of effects resulting from unrolling a CFG with
holes (which includes interpreting terminators),
*before* interpreting individual instructions.

That is, each instruction is still an "opaque" effect.

See also `OpaqueEff`, which omits the holes.
-/
noncomputable
abbrev OpaqueCtxEff := HoleEff ⊕ₑ OpaqueEff

/-!
## Handlers
--------------------------------------------------------------------------------
-/

/-! ### Instruction -/

axiom handleInst : (i : Inst) → ITree InterpEff Unit

noncomputable
def interpInst : ITree OpaqueEff α → ITree InterpEff α :=
  ITree.interpLeft handleInst

/-! ### Combined -/

/--
Resolve a raw `HoleId` into a well-scoped `Hole n`, raising an error if the
id is out of range.
-/
def Hole.fromId {n} [ErrUBE -< ε] (h : HoleId) : ITree ε (Hole n) :=
  match Hole.fromId? h with
  | some x => return x
  | none => raiseError s!"Unknown hole: {h}"

noncomputable
def interpAll
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : ITree BaseEff α :=
  t
  |> interpHoles (Hole.fromId · >>= fHole)
  |> interpInst
  |> interpLocalStack
