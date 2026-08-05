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

/-- Interpret local stack effects starting from a speciefied stack. -/
def interpLocalStackWith [ErrUB -< ε] (x : ITree (LocalEff ⊕ ε) α) : LocalStack → ITree ε α :=
  (interpLocalStackM x).run'

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
def interpAllM
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : StateT LocalStack (ITree BaseEff) α :=
  t
  |> interpHoles (Hole.fromId · >>= fHole)
  |> interpInst
  |> interpLocalStackM

noncomputable
abbrev interpAll
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : ITree BaseEff α :=
  (interpAllM fHole t).run' { }

/-! ### Lemmas -/
section Lemmas
open LawfulMonadIter (tau)

@[simp, grind =]
theorem interpAllM_ret (fHole : Hole n → ITree OpaqueEff Unit) (r : α) :
    interpAllM fHole (.ret r) = pure r := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM, ITree.interpLeft]

@[simp, grind =]
theorem interpAllM_tau (fHole : Hole n → ITree OpaqueEff Unit) (t : ITree OpaqueCtxEff α) :
    interpAllM fHole (.tau t) = tau (interpAllM fHole t) := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM, ITree.interpLeft]


/--
`ITree.map` with the identity effect and continuation maps is the identity.
-/
@[simp, grind =]
theorem _root_.ITree.map_id_id {ε} {κε : ε → Type} [Effect ε κε] {α}
    (t : ITree ε α) :
    t.map (fun i => i) (fun _ x => x) = t := by
  apply ITree.eq_of_bisim
  apply ITree.Bisim.coinduct (fun (x y : ITree ε α) =>
    x = y.map (fun i => i) (fun _ x => x))
  · rintro _ y rfl
    cases y with
    | ret r => exact .inl ⟨r, by simp, rfl⟩
    | tau u => exact .inr (.inl ⟨_, u, rfl, by simp, rfl⟩)
    | vis i k => exact .inr (.inr ⟨i, _, k, fun _ => rfl, by simp, rfl⟩)
  · rfl

/--
For the sum-based `Subeffect BaseEff BaseEff` instance, `Subeffect.map` at any
`i : BaseEff` still yields `⟨i, id⟩`, matching the reflexivity instance's map.
-/
@[simp, grind =]
theorem Subeffect.map_baseEff_eq_self (i : BaseEff) :
    (Subeffect.map (ε₁ := BaseEff) (ε₂ := BaseEff) i) = ⟨i, id⟩ := by
  rcases i with s | e <;> rfl

/--
The `ITree.lift` from `BaseEff` to itself is the identity, for the reflexivity
`Subeffect BaseEff BaseEff` instance.
-/
@[simp, grind =]
theorem _root_.ITree.lift_baseEff_self_refl (t : ITree BaseEff α) :
    @ITree.ITree.lift BaseEff _ _ BaseEff _ _ _ Subeffect.inst t = t := by
  -- With the reflexivity `Subeffect BaseEff BaseEff` instance, `lift` is
  -- literally `map id id`, so this follows from `ITree.map_id_id`.
  exact ITree.map_id_id t

/--
The `ITree.lift` from `BaseEff` to itself is the identity, for the sum-based
`Subeffect BaseEff BaseEff` instance (the one Lean picks by default when the
target `BaseEff = SideEff ⊕ ErrUB` is displayed as a sum).

See also `ITree.lift_baseEff_self_refl` for the reflexivity instance variant;
both are needed as `simp` lemmas since the two instances arise in different
elaboration contexts.
-/
@[simp, grind =]
theorem _root_.ITree.lift_baseEff_self (t : ITree BaseEff α) :
    ITree.lift (δ := BaseEff) t = t := by
  apply ITree.eq_of_bisim
  apply ITree.Bisim.coinduct (fun (x y : ITree BaseEff α) => x = y.lift)
  · rintro _ y rfl
    cases y with
    | ret r => exact .inl ⟨r, by simp, rfl⟩
    | tau u => exact .inr (.inl ⟨_, u, rfl, by simp, rfl⟩)
    | vis i k =>
      refine .inr (.inr ⟨i, fun o => (k o).lift, k, fun _ => rfl, ?_, rfl⟩)
      rw [ITree.lift_vis]
      congr 1
      · exact congrArg _ (Subeffect.map_baseEff_eq_self i)
      · rcases i with s | e <;> rfl
  · rfl

variable (fHole : Hole n → ITree OpaqueEff Unit)

/--
`vis`-case for a `HoleEff`.
Resolves the hole via `Hole.fromId` and `fHole`, then continues with `k ()`
after one `tau` step (introduced by `interpLocalStackM`).
-/
@[simp, grind =]
theorem interpAllM_vis_hole
    (h : HoleId) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inl h : OpaqueCtxEff) k) = (do
      interpLocalStackM (interpInst (Hole.fromId h >>= fHole).lift)
      tau (interpAllM fHole (k ()))) := by
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interpM_bind, ITree.interpM_tau]

/--
`vis`-case for an `InstEff`.
Delegates to `handleInst i`, then continues with `k ()` after two `tau` steps
(one from `interpHoles` passing the effect through, one from `interpLocalStackM`).
-/
@[simp, grind =]
theorem interpAllM_vis_inst
    (i : Inst) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inl i) : OpaqueCtxEff) k) = (do
      interpLocalStackM (handleInst i)
      tau (tau (interpAllM fHole (k ())))) := by
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interp_ret, ITree.interpM_bind, ITree.interpM_tau, ITree.interpM_ret,
    Effect.trigger, Subeffect.map_eq_self, ITree.tau_bind, bind_assoc,
    ITree.pure_eq_ret, id_eq, pure_bind]

/--
`vis`-case for a `LocalEff.read`.
Reads variable `x` from the local stack (raising an error if unbound), then
continues with `k` after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_local_read
    (x : VarId) (k : Val → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inl (.read x))) : OpaqueCtxEff) k) = (do
      let o ← (withErrorContext s!"Unknown variable: {x}" (LocalStackT.read? x)
                  : LocalStackT (ITree BaseEff) Val)
      tau (tau (tau (interpAllM fHole (k o))))) := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, Effect.trigger, ITree.pure_eq_ret]

/--
`vis`-case for a `LocalEff.push`.
Pushes `(x, val)` onto the local stack, then continues with `k ()`
after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_local_push
    (x : VarId) (val : Val) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inl (.push x val))) : OpaqueCtxEff) k) = (do
      (LocalStackT.push x val : LocalStackT (ITree BaseEff) Unit)
      tau (tau (tau (interpAllM fHole (k ()))))) := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, Effect.trigger, ITree.pure_eq_ret]

/--
`vis`-case for a `BaseEff`.
The effect is passed through unchanged to the base ITree, and the continuation
is invoked after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_base
    (b : BaseEff) (k : (Sum.rec SideEff.κ (fun _ : ErrUB => Empty) b)
                          → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inr b)) : OpaqueCtxEff) k) = (do
      let o ← (liftM (ITree.vis b ITree.ret) : LocalStackT (ITree BaseEff) _)
      tau (tau (tau (interpAllM fHole (k o))))) := by
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interp_ret, ITree.interpM_bind, ITree.interpM_tau, ITree.interpM_vis,
    ITree.interpM_ret, Effect.trigger, Subeffect.map_eq_self,
    ITree.pure_eq_ret, id_eq, pure_bind, ITree.tau_bind, bind_assoc,
    StateT.tau_bind, liftM, monadLift, MonadLift.monadLift,
    ITree.lift_baseEff_self, ITree.lift_baseEff_self_refl]

/--
`vis`-case for an arbitrary effect, split into the individual cases via `match`.
-/
@[grind =]
theorem interpAllM_vis
    (e : OpaqueCtxEff)
    (k :
      Sum.rec (fun (_ : HoleEff) => Unit)
        (Sum.rec (fun (_ : InstEff) => Unit)
          (Sum.rec
            (fun (l : LocalEff) => match l with | .read _ => Val | .push _ _ => Unit)
            (Sum.rec SideEff.κ (fun (_ : ErrUB) => Empty))))
        e
      → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis e k) =
      match e, k with
      | .inl h, k => (do
          interpLocalStackM (interpInst (Hole.fromId h >>= fHole).lift)
          tau (interpAllM fHole (k ())))
      | .inr (.inl i), k => (do
          interpLocalStackM (handleInst i)
          tau (tau (interpAllM fHole (k ()))))
      | .inr (.inr (.inl (.read x))), k => (do
          let o ← (withErrorContext s!"Unknown variable: {x}" (LocalStackT.read? x)
                      : LocalStackT (ITree BaseEff) Val)
          tau (tau (tau (interpAllM fHole (k o)))))
      | .inr (.inr (.inl (.push x val))), k => (do
          (LocalStackT.push x val : LocalStackT (ITree BaseEff) Unit)
          tau (tau (tau (interpAllM fHole (k ())))))
      | .inr (.inr (.inr b)), k => (do
          let o ← (liftM (ITree.vis b .ret : ITree BaseEff _)
                    : LocalStackT (ITree BaseEff) _)
          tau (tau (tau (interpAllM fHole (k o))))) := by
  rcases e with h | i | (⟨x⟩ | ⟨x, val⟩) | b
  · exact interpAllM_vis_hole fHole h k
  · exact interpAllM_vis_inst fHole i k
  · exact interpAllM_vis_local_read fHole x k
  · exact interpAllM_vis_local_push fHole x val k
  · exact interpAllM_vis_base fHole b k

end Lemmas
