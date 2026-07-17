module

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

variable {ε : Type} {κε : ε → Type} [Effect ε κε]
         {δ : Type} {κδ : δ → Type} [Effect δ κδ]
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

instance : Effect ErrUB (fun _ => Empty) := ⟨⟩

/-! ### Helpers -/

def raiseUB [ErrUB -< ε] (reason := "") : ITree ε α :=
  trigger ErrUB (.ub reason) >>= Empty.elim

def raiseError [ErrUB -< ε] (reason := "") : ITree ε α :=
  trigger ErrUB (.error reason) >>= Empty.elim

def withErrorContext [Monad m] [MonadLiftT (ITree ErrUB) m] (reason : String) (x? : m (Option α)) : m α := do
  let x ← x?
  match x with
  | some x => return x
  | none => liftM <| (raiseError reason : ITree ErrUB _)

abbrev raiseErrorOnNone [ErrUB -< ε] (reason := "") (t : ITree ε (Option α)) : ITree ε α := do
  withErrorContext reason t

section Lemmas
open Subeffect (map)

@[simp, grind =]
theorem bind_raiseUB [ErrUB -< ε] {α β} (reason : String) (f : α → ITree ε β) :
    raiseUB reason >>= f = raiseUB reason := by
  rw [raiseUB, bind_assoc]
  exact congrArg _ <| funext (·.elim)

@[simp, grind =]
theorem bind_raiseError [ErrUB -< ε] {α β} (reason : String) (f : α → ITree ε β) :
    raiseError reason >>= f = raiseError reason := by
  rw [raiseError, bind_assoc]
  exact congrArg _ <| funext (·.elim)

@[simp, grind =]
theorem interpLeft_raiseError [ErrUB -< δ] (f : ε ⤳ ITree δ) (reason : String) :
    ITree.interpLeft f (raiseError reason : ITree (ε ⊕ δ) α)
      = raiseError reason := by
  simp only [raiseError, ITree.interpLeft_bind, tau_bind, ITree.bind_ret,
    ITree.interpLeft_trigger_inr f (ErrUB.error reason), ITree.pure_eq_ret, bind_assoc]
  congr; grind

@[grind =]
theorem raiseError_eq_vis_iff [ErrUB -< ε] {reason : String} {j : ε}
    {k : κε j → ITree ε α} :
    (raiseError reason : ITree ε α) = ITree.vis j k ↔
    (map (ε₂:=ε) (.error reason : ErrUB)).fst = j ∧
    (fun x : κε (map (ε₂:=ε) (.error reason : ErrUB)).fst =>
      (Empty.elim ((map (ε₂:=ε) (.error reason : ErrUB)).snd x) : ITree ε α)) ≍ k := by
  simp [raiseError, trigger]

open Subeffect (mapEff mapCont) in
@[simp, grind =]
theorem map_raiseError [ErrUB -< ε] (reason : String) (fEff : ε → δ) (fCont : _) :
    (raiseError reason : ITree ε α).map fEff fCont =
      .vis (fEff <| mapEff <| ErrUB.error reason) (fun x => Empty.elim <| mapCont _ <| fCont _ x) := by
  suffices ∀ {α} (f g : κδ (fEff (map (ErrUB.error reason)).fst) → α),
    f = g
  by simpa [raiseError, trigger] using this _ _
  intros
  funext x
  have : Empty := mapCont _ <| fCont _ x
  contradiction

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
axiom SideEff.κ : SideEff → Type
instance : Effect SideEff SideEff.κ := ⟨⟩

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

section Lemmas
variable [LocalEff -< ε]
open Subeffect (map)

@[simp, grind =]
theorem hasEffect_pushVar {e : ε} :
    (pushVar (ε:=ε) var value).HasEffect e ↔ (Subeffect.map (.push var value : LocalEff)).fst = e := by
  simp [pushVar, Effect.trigger]

end Lemmas

/-! ### Interpretation -/

def interpLocalStackM [ErrUB -< ε] :
    (x : ITree (LocalEff ⊕ ε) α) → LocalStackT (ITree ε) α :=
  ITree.interpM fun
    | .inr e => liftM <| ITree.vis e .ret
    | .inl (.read x) => withErrorContext s!"Unknown variable: {x}" <|
        LocalStackT.read? x
    | .inl (.push x val) => LocalStackT.push x val


/-- Interpret local stack effects starting from an empty initial stack. -/
def interpLocalStack [ErrUB -< ε] (x : ITree (LocalEff ⊕ ε) α) : ITree ε α :=
  (interpLocalStackM x).run' { }

/-!
## Instruction Effect
--------------------------------------------------------------------------------
-/

/-!
We assume an arbitrary types of instructions, which we can cleanly "denote" by
considering each instructions as a unique effect without output. The result of
an instruction is added to the environment via the `LocalStack` push side effect.

N.B: Terminators are *not* considered effects, since we want to unroll the CFG
structure right away.
-/

/-- `Inst` is the type of instructions. -/
axiom Inst : Type

/-- In `InstEff`, each instruction is a unique effect. -/
abbrev InstEff := Inst

instance : Effect InstEff (fun _ => Unit) := ⟨⟩


/-!
## Effect Aliasses
--------------------------------------------------------------------------------
-/

/--
`BaseEff` gives the "base" effects, which is some opaque notion of side-effects
enhanced with errors and UB.
-/
abbrev BaseEff := SideEff ⊕ ErrUB

/--
`InterpEff` gives the effects into which instructions and terminators are
interpreted.
-/
noncomputable
abbrev InterpEff := LocalEff ⊕ BaseEff

/--
`OpaqueEff` is the totality of effects resulting from unrolling a (closed) CFG
(which includes interpreting terminators),
*before* interpreting individual instructions.

That is, each instruction is still an "opaque" effect.
-/
noncomputable
abbrev OpaqueEff := InstEff ⊕ InterpEff

/--
`OpaqueCtxEff` is the totality of effects resulting from unrolling a CFG with
holes (which includes interpreting terminators),
*before* interpreting individual instructions.

That is, each instruction is still an "opaque" effect.

See also `OpaqueEff`, which omits the holes.
-/
noncomputable
abbrev OpaqueCtxEff := HoleEff ⊕ OpaqueEff

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

abbrev Hole.fromId [ErrUB -< ε] (h : HoleId) : ITree ε (Hole n) :=
  withErrorContext s!"Unknown hole: {h}" <|
    (.ret <| Hole.fromId? h)

noncomputable
def interpAll
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : ITree BaseEff α :=
  t
  |> interpHoles (Hole.fromId · >>= fHole)
  |> interpInst
  |> interpLocalStack
