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

/-! ### Interpretation -/
section Interp
universe u
variable {ρ : Type u} {m : Type u → Type u}

/--
`ExceptT ρ m` iterates by iterating in `m`, aborting the loop as soon as the
body throws.
-/
instance [Monad m] [MonadIter m] : MonadIter (ExceptT ρ m) where
  iter f a := ExceptT.mk <| iter (init := a) fun a => (f a).run >>= fun
    | .ok (.inl a) => pure (.inl a)
    | .ok (.inr b) => pure (.inr (.ok b))
    | .error e     => pure (.inr (.error e))

@[simp, grind =]
theorem _root_.ExceptT.run_iter [Monad m] [MonadIter m] {α β}
    (f : α → ExceptT ρ m (α ⊕ β)) (a : α) :
    ExceptT.run (iter (m := ExceptT ρ m) f a)
      = iter (fun a => (f a).run >>= fun
          | .ok (.inl a) => pure (.inl a)
          | .ok (.inr b) => pure (.inr (.ok b))
          | .error e     => pure (.inr (.error e))) a :=
  rfl

instance [Monad m] [LawfulMonad m] [MonadIter m] [im : LawfulMonadIter m] :
    LawfulMonadIter (ExceptT ρ m) where
  tau x := .mk (im.tau x.run)
  iter_eq f a := by
    ext
    rw [ExceptT.run_iter, im.iter_eq]
    simp only [ExceptT.run_bind, bind_assoc]
    congr 1
    funext x
    rcases x with e | (a | b) <;> simp

/--
Interpret `ErrUB` effects into `ExceptT ErrUB`: both errors and UB abort the
computation, with the thrown value recording which of the two occurred.
-/
def interpErrUB : ITree (ε ⊕ ErrUB) α → ExceptT ErrUB (ITree ε) α :=
  ITree.interpM fun
    | .inl e => liftM (ITree.vis e .ret)
    | .inr e => throw e

/-- `interpErrUB`, applied underneath a state layer. -/
def interpErrUBM {σ} (x : StateT σ (ITree (ε ⊕ ErrUB)) α) :
    StateT σ (ExceptT ErrUB (ITree ε)) α :=
  interpErrUB ∘ x.run

section Refinement

instance [Refinement α] : Refinement (Except ErrUB α) where
  IsRefinedBy
    -- An interpreter error is refined by anything
    | .error (.error _), _ => True
    -- UB is *not* refined by an interpreter error
    | .error (.ub _), .error (.error _) => False
    -- UB *is* refined by anuthing else
    | .error (.ub _), _ => True
    -- Values are not refined by UB nor interpreter errors
    | .ok _, .error _ => False
    | .ok x, .ok y => x ⊒ y

end Refinement

section Lemmas
open LawfulMonadIter (tau)
variable {σ : Type}

@[simp, grind =]
theorem interpErrUB_ret (r : α) :
    interpErrUB (.ret r : ITree (ε ⊕ ErrUB) α) = pure r := by
  simp [interpErrUB]

@[simp, grind =]
theorem interpErrUB_tau (t : ITree (ε ⊕ ErrUB) α) :
    interpErrUB (.tau t) = tau (interpErrUB t) := by
  simp [interpErrUB]

@[simp, grind =]
theorem interpErrUB_vis_inl (e : ε) (k : κε e → ITree (ε ⊕ ErrUB) α) :
    interpErrUB (.vis (.inl e) k) = (do
      let o ← (liftM (ITree.vis e .ret) : ExceptT ErrUB (ITree ε) _)
      tau (interpErrUB (k o))) := by
  simp [interpErrUB]

/-- Errors and UB abort the computation, discarding the continuation. -/
@[simp, grind =]
theorem interpErrUB_vis_inr (e : ErrUB) (k : Empty → ITree (ε ⊕ ErrUB) α) :
    interpErrUB (.vis (.inr e) k) = throw e := by
  simp [interpErrUB]

@[simp, grind =]
theorem interpErrUB_raiseUB (reason : String) :
    interpErrUB (raiseUB reason : ITree (ε ⊕ ErrUB) α) = throw (.ub reason) := by
  simp [raiseUB, Effect.trigger]

@[simp, grind =]
theorem interpErrUB_raiseError (reason : String) :
    interpErrUB (raiseError reason : ITree (ε ⊕ ErrUB) α) = throw (.error reason) := by
  simp [raiseError, Effect.trigger]

@[simp, grind =]
theorem interpErrUB_bind {β} (t : ITree (ε ⊕ ErrUB) α) (f : α → ITree (ε ⊕ ErrUB) β) :
    interpErrUB (t >>= f) = interpErrUB t >>= fun a => interpErrUB (f a) :=
  ITree.interpM_bind _ t f

@[simp, grind =]
theorem interpErrUBM_bind {β} (x : StateT σ (ITree (ε ⊕ ErrUB)) α)
    (f : α → StateT σ (ITree (ε ⊕ ErrUB)) β) :
    interpErrUBM (x >>= f) = interpErrUBM x >>= fun a => interpErrUBM (f a) := by
  funext s; exact interpErrUB_bind (x s) _

@[simp, grind =]
theorem interpErrUBM_tau (x : StateT σ (ITree (ε ⊕ ErrUB)) α) :
    interpErrUBM (ITree.tau ∘ x) = ITree.tau ∘ (interpErrUBM x) := by
  funext s; exact interpErrUB_tau (x s)

@[simp, grind =]
theorem _root_.StateT.run'_pure {m : Type → Type} [Monad m] [LawfulMonad m] (a : α) (s : σ) :
    (pure a : StateT σ m α).run' s = pure a := by
  show (fun x => x.fst) <$> (pure (a, s) : m (α × σ)) = pure a
  simp

/-- `pure` in `ExceptT E (ITree ε)` returns an `ok` value. -/
@[simp]
theorem _root_.ExceptT.pure_eq_ret {E : Type} (r : α) :
    (pure r : ExceptT E (ITree ε) α) = ITree.ret (.ok r) :=
  rfl

/--
`ExceptT.mk` and `ExceptT.run` are identities, so the `tau` of the
`LawfulMonadIter (ExceptT E (ITree ε))` instance is just `ITree.tau`.
-/
@[simp, grind =]
theorem _root_.ExceptT.mk_tau_run {E : Type} (x : ExceptT E (ITree ε) α) :
    ExceptT.mk (ITree.tau x.run) = ITree.tau x :=
  rfl

@[simp, grind =]
theorem _root_.ExceptT.map_tau {E β : Type} (f : α → β) (x : ExceptT E (ITree ε) α) :
    (f <$> (ITree.tau x) : ExceptT E (ITree ε) β)
      = ITree.tau (f <$> x : ExceptT E (ITree ε) β) := by
  simp [Functor.map, ExceptT.map, ExceptT.mk]

@[simp, grind =]
theorem _root_.ExceptT.map_ret_ok {E β : Type} (f : α → β) (a : α) :
    (f <$> (ITree.ret (.ok a) : ExceptT E (ITree ε) α) : ExceptT E (ITree ε) β)
      = ITree.ret (.ok (f a)) := by
  simp [Functor.map, ExceptT.map, ExceptT.mk]

@[simp, grind =]
theorem _root_.ExceptT.map_ret_error {E β : Type} (f : α → β) (e : E) :
    (f <$> (ITree.ret (.error e) : ExceptT E (ITree ε) α) : ExceptT E (ITree ε) β)
      = ITree.ret (.error e) := by
  simp [Functor.map, ExceptT.map, ExceptT.mk]

/-- `tau` in `StateT σ (ExceptT E (ITree ε))` is just a `tau` in the underlying `ITree`. -/
@[simp, grind =]
theorem _root_.StateT.exceptT_tau_eq {E : Type} (x : StateT σ (ExceptT E (ITree ε)) α) :
    tau x = ITree.tau ∘ x :=
  rfl

@[simp, grind =]
theorem _root_.StateT.run_tau_comp {E : Type} (x : StateT σ (ExceptT E (ITree ε)) α) (s : σ) :
    StateT.run (ITree.tau ∘ x : StateT σ (ExceptT E (ITree ε)) α) s
      = ITree.tau (StateT.run x s : ITree ε (Except E (α × σ))) :=
  rfl

/-- Lifting an `ErrUB`-only computation and interpreting it again throws. -/
@[simp, grind =]
theorem interpErrUB_lift_raiseError (reason : String) :
    interpErrUB ((raiseError reason : ITree ErrUB α).lift : ITree (ε ⊕ ErrUB) α)
      = throw (.error reason) := by
  simp [ITree.lift]

@[simp, grind =]
theorem interpErrUBM_pure (r : α) :
    interpErrUBM (pure r : StateT σ (ITree (ε ⊕ ErrUB)) α) = pure r := by
  funext s
  show interpErrUB (pure (r, s)) = (pure (r, s) : ExceptT ErrUB (ITree ε) (α × σ))
  simp

@[simp, grind =]
theorem interpErrUBM_get :
    interpErrUBM (get : StateT σ (ITree (ε ⊕ ErrUB)) σ) = get := by
  funext s
  show interpErrUB (pure (s, s)) = (pure (s, s) : ExceptT ErrUB (ITree ε) (σ × σ))
  simp

@[simp]
theorem _root_.StateT.run_throw_exceptT {σ ρ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α} (e : ρ) (s : σ) :
    (throw e : StateT σ (ExceptT ρ m) α) s = (throw e : ExceptT ρ m (α × σ)) := by
  show StateT.lift (throw e) s = (throw e : ExceptT ρ m (α × σ))
  simp [StateT.lift]

@[simp, grind =]
theorem _root_.StateT.throw_bind {σ ρ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β} (e : ρ) (f : α → StateT σ (ExceptT ρ m) β) :
    (throw e : StateT σ (ExceptT ρ m) α) >>= f = throw e := by
  funext s
  show (StateT.lift (throw e) s : ExceptT ρ m (α × σ)) >>= (fun p => f p.1 p.2)
      = (StateT.lift (throw e) s : ExceptT ρ m (β × σ))
  simp [StateT.lift]

@[simp, grind =]
theorem interpErrUBM_push (x : VarId) (val : Val) :
    interpErrUBM (LocalStackT.push x val : LocalStackT (ITree (ε ⊕ ErrUB)) Unit)
      = LocalStackT.push x val := by
  funext s
  show interpErrUB (pure ((), s.insert x val))
      = (pure ((), s.insert x val) : ExceptT ErrUB (ITree ε) (Unit × LocalStack))
  simp

end Lemmas
end Interp

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

/--
`interpAllM` interprets holes, instructions, local variables and `ErrUB` away,
leaving only the `SideEff` side-effects uninterpreted.
-/
noncomputable
def interpAllM
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : (StateT LocalStack <| ExceptT ErrUB <| ITree SideEff) α :=
  t
  |> interpHoles (Hole.fromId · >>= fHole)
  |> interpInst
  |> interpLocalStackM
  |> interpErrUBM

noncomputable
abbrev interpAll
    (fHole : Hole n → ITree OpaqueEff Unit)
    (t : ITree OpaqueCtxEff α) : ExceptT ErrUB (ITree SideEff) α :=
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
  simp only [interpAllM, interpLocalStackM, interpInst, ITree.interpLeft, interpHoles,
    ITree.lift_bind, ITree.interp_tau, ITree.interp_interp, ITree.interpM_tau, tau,
    interpErrUBM_tau, ExceptT.mk_tau_run]
  rfl

@[simp, grind =]
theorem interpAllM_run'_ret (r : α) (ρ : LocalStack) :
    (interpAllM fHole (.ret r)).run' ρ = .ret (.ok r) := by
  simp

@[simp, grind =]
theorem interpAllM_run'_tau (t : ITree OpaqueCtxEff α) (ρ : LocalStack) :
    (interpAllM fHole (.tau t)).run' ρ = .tau ((interpAllM fHole t).run' ρ) := by
  simp [StateT.run']


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

/-! #### Interpreting `BaseEff` into `ExceptT ErrUB` -/

@[simp, grind =]
theorem interpErrUBM_liftM_vis_inr {σ} (e : ErrUB) :
    interpErrUBM (liftM (ITree.vis (Sum.inr e : BaseEff) ITree.ret)
        : StateT σ (ITree BaseEff) Empty) = throw e := by
  funext s
  show interpErrUB ((ITree.vis (Sum.inr e : BaseEff) ITree.ret).lift >>= fun a => pure (a, s)) = _
  simp

@[simp, grind =]
theorem interpErrUBM_liftM_raiseError {σ} (reason : String) :
    interpErrUBM (liftM (raiseError reason : ITree ErrUB α)
        : StateT σ (ITree BaseEff) α) = throw (.error reason) := by
  funext s
  show interpErrUB ((raiseError reason : ITree ErrUB α).lift >>= fun a => pure (a, s)) = _
  simp

/-- Reading an unbound variable raises an error (rather than UB). -/
@[simp, grind =]
theorem interpErrUBM_withErrorContext_read? (reason : String) (x : VarId) :
    interpErrUBM (withErrorContext reason (LocalStackT.read? x) : LocalStackT (ITree BaseEff) Val)
      = (do
        let ρ ← get
        match ρ[x]? with
        | some v => pure v
        | none => throw (.error reason)) := by
  rw [withErrorContext, interpErrUBM_bind, LocalStackT.read?, interpErrUBM_bind,
    interpErrUBM_get]
  simp only [bind_assoc, interpErrUBM_pure, pure_bind]
  congr; funext ρ; cases ρ[x]? <;> simp

variable (fHole : Hole n → ITree OpaqueEff Unit)

/--
`vis`-case for a `HoleEff`.
Resolves the hole via `Hole.fromId` and `fHole`, then continues with `k ()`
after one `tau` step (introduced by `interpLocalStackM`).
-/
@[simp, grind =]
theorem interpAllM_vis_hole (h : HoleId) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inl h : OpaqueCtxEff) k) = (do
      interpErrUBM (interpLocalStackM (interpInst (Hole.fromId h >>= fHole).lift))
      tau (interpAllM fHole (k ())))  := by
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interpM_bind, ITree.interpM_tau, interpErrUBM_bind, interpErrUBM_tau,
    StateT.tau_eq, StateT.exceptT_tau_eq]

/--
`vis`-case for an `InstEff`.
Delegates to `handleInst i`, then continues with `k ()` after two `tau` steps
(one from `interpHoles` passing the effect through, one from `interpLocalStackM`).
-/
@[simp, grind =]
theorem interpAllM_vis_inst (i : Inst) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inl i) : OpaqueCtxEff) k) = (do
      interpErrUBM (interpLocalStackM (handleInst i))
      tau (tau (interpAllM fHole (k ())))) := by
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interp_ret, ITree.interpM_bind, ITree.interpM_tau, ITree.interpM_ret,
    Effect.trigger, Subeffect.map_eq_self, ITree.tau_bind, bind_assoc,
    ITree.pure_eq_ret, id_eq, pure_bind, interpErrUBM_bind, interpErrUBM_tau,
    StateT.tau_eq, StateT.exceptT_tau_eq]

/--
`vis`-case for a `LocalEff.read`.
Reads variable `x` from the local stack (raising an error if unbound), then
continues with `k` after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_local_read (x : VarId) (k : Val → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inl (.read x))) : OpaqueCtxEff) k) = (do
      let o ← interpErrUBM (withErrorContext s!"Unknown variable: {x}" (LocalStackT.read? x))
      tau (tau (tau (interpAllM fHole (k o))))) := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, Effect.trigger, ITree.pure_eq_ret, interpErrUBM, interpErrUB]
  sorry

/--
`vis`-case for a `LocalEff.push`.
Pushes `(x, val)` onto the local stack, then continues with `k ()`
after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_local_push (x : VarId) (val : Val) (k : Unit → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inl (.push x val))) : OpaqueCtxEff) k) = (do
      LocalStackT.push x val
      tau (tau (tau (interpAllM fHole (k ()))))) := by
  simp [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, Effect.trigger, ITree.pure_eq_ret]
  rfl

/--
`vis`-case for a `BaseEff`.
The effect is passed through unchanged to the base ITree, and the continuation
is invoked after three `tau` steps (one from each interpretation layer).
-/
@[simp, grind =]
theorem interpAllM_vis_base (b : BaseEff)
    (k : (Sum.rec SideEff.κ (fun _ : ErrUB => Empty) b) → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inr b)) : OpaqueCtxEff) k) = (do
      let o ← interpErrUB (ITree.vis b ITree.ret)
      tau (tau (tau (interpAllM fHole (k o))))) := by
  stop
  simp only [interpAllM, interpHoles, interpInst, interpLocalStackM,
    ITree.interpLeft, ITree.interp_vis, ITree.interp_bind, ITree.interp_tau,
    ITree.interp_ret, ITree.interpM_bind, ITree.interpM_tau, ITree.interpM_vis,
    ITree.interpM_ret, Effect.trigger, Subeffect.map_eq_self,
    ITree.pure_eq_ret, id_eq, pure_bind, ITree.tau_bind, bind_assoc,
    StateT.tau_eq, StateT.tau_bind, liftM, monadLift, MonadLift.monadLift,
    ITree.lift_baseEff_self, ITree.lift_baseEff_self_refl, interpErrUBM_bind,
    interpErrUBM_tau, StateT.exceptT_tau_eq]

/-- Raised errors and UB abort the computation, discarding the continuation. -/
@[simp, grind =]
theorem interpAllM_vis_errUB (e : ErrUB) (k : Empty → ITree OpaqueCtxEff α) :
    interpAllM fHole (.vis (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))) : OpaqueCtxEff) k)
      = throw e := by
  rw [interpAllM_vis_base (b := .inr e) (k := k), interpErrUBM_liftM_vis_inr,
    StateT.throw_bind]

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
          interpErrUBM (interpLocalStackM (interpInst (Hole.fromId h >>= fHole).lift))
          tau (interpAllM fHole (k ())))
      | .inr (.inl i), k => (do
          interpErrUBM (interpLocalStackM (handleInst i))
          tau (tau (interpAllM fHole (k ()))))
      | .inr (.inr (.inl (.read x))), k => (do
          let o ← interpErrUBM (withErrorContext s!"Unknown variable: {x}" (LocalStackT.read? x))
          tau (tau (tau (interpAllM fHole (k o)))))
      | .inr (.inr (.inl (.push x val))), k => (do
          LocalStackT.push x val
          tau (tau (tau (interpAllM fHole (k ())))))
      | .inr (.inr (.inr b)), k => (do
          let o ← interpErrUB (ITree.vis b .ret)
          tau (tau (tau (interpAllM fHole (k o))))) := by
  rcases e with h | i | (⟨x⟩ | ⟨x, val⟩) | b
  · exact interpAllM_vis_hole fHole h k
  · exact interpAllM_vis_inst fHole i k
  · exact interpAllM_vis_local_read fHole x k
  · exact interpAllM_vis_local_push fHole x val k
  · exact interpAllM_vis_base fHole b k

end Lemmas
