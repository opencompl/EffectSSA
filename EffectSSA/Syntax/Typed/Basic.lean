import EffectSSA.Syntax.Untyped
import EffectSSA.Types

/-!
# Intrinsically Well-typed syntax
We define typed variants of syntax datastructure, which bundle an untyped
datastructer with a proof of well-typedness
-/
namespace EffectSSA
variable {τ}

structure TInstruction (Γ : Context τ) (Δ : Context τ) where
  instruction : Instruction τ
  wt : instruction.WellTyped Γ Δ := by grind

structure TInstructionSeq (Γ : Context τ) (Δ : Context τ) where
  seq : InstructionSeq τ
  wt : seq.WellTypedWith Γ Δ := by grind

structure TProgram (Γ : Context τ) (ts : List τ.Typ) where
  program : Program τ
  wt : program.WellTyped Γ ts := by grind

/-!
## Coercions
--------------------------------------------------------------------------------
The typed structures can be implicitly coerced into the underlying
untyped variants
-/
variable {Γ : Context τ}

instance : CoeOut (TInstruction Γ Δ) (Instruction τ) where coe := TInstruction.instruction
instance : CoeOut (TInstructionSeq Γ Δ) (InstructionSeq τ) where coe := TInstructionSeq.seq
instance : CoeOut (TProgram Γ ts) (Program τ) where coe := TProgram.program

/-!
## Grind Attributes
--------------------------------------------------------------------------------
-/

attribute [grind! .] TInstruction.wt
attribute [grind! .] TInstructionSeq.wt
attribute [grind! .] TProgram.wt

/-!
## Definitions
--------------------------------------------------------------------------------
-/
variable {Γ : Context τ} {ts : List τ.Typ}

/-!
### Constructors
-/

/-! #### instructions -/
section TInstruction
open Ty.Typ (ptr eff data)

def TInstruction.loadI (t : τ.DType) (p : TVar Γ ptr)
    (hΓ : Γ.isUnrestricted) :
    TInstruction Γ (Γ <: t) where
  instruction := .loadI t p

def TInstruction.storeI (t : τ.DType) (p : TVar Γ ptr) (x : TVar Γ t)
    (hΓ : Γ.isUnrestricted) :
    TInstruction Γ Γ where
  instruction := .storeI t p x

def TInstruction.loadE (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr) :
    TInstruction Γ (Γ.eraseVar e <: eff <: t) where
  instruction := .loadE t e p
  wt := .loadE e.wt p.wt

def TInstruction.storeE (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr)
    (x : TVar Γ t) :
    TInstruction Γ (Γ.eraseVar e <: eff) where
  instruction := .storeE t e p x
  wt := .storeE e.wt p.wt x.wt

def TInstruction.createEff (hΓ : Γ.isUnrestricted) :
    TInstruction Γ (Γ <: eff) where
  instruction := .createEff
  wt := .createEff hΓ

def TInstruction.consumeEff (e : TVar Γ eff) (hΓ : (Γ.eraseVar e).isUnrestricted) :
    TInstruction Γ (Γ.eraseVar e) where
  instruction := .consumeEff e

end TInstruction

def TInstructionSeq.nil (Γ : Context τ) : TInstructionSeq Γ Γ where seq := .nil
def TInstructionSeq.cons (i : TInstruction Γ Δ) (is : TInstructionSeq Δ Ξ) :
    TInstructionSeq Γ Ξ where
  seq := i ;> is

def TProgram.mk' {Δ} (is : TInstructionSeq Γ Δ) (vs : TVarList Δ ts)
    (h : (Δ.eraseVars vs.toList).isUnrestricted) :
    TProgram Γ ts where
  program := ⟨is.seq, vs.toList⟩
  wt := by
    have (i : ℕ) (hi : i < vs.toList.length) : ∃ t,
        ts[i]? = some t ∧ Δ[vs.toList[i]]? = some t := by
      have := vs.wt ⟨i, by grind⟩
      grind
    grind

/-!
### Projections
-/

/-- The (internal) context after executing the instruction sequence of `p`. -/
@[grind =]
noncomputable def TProgram.returnContext (p : TProgram Γ ts) : Context τ :=
  p.wt.choose

@[grind =]
def TProgram.instructions (p : TProgram Γ ts) : TInstructionSeq Γ p.returnContext where
  seq := p.program.instructions
  wt := by grind

def TProgram.returnVars (p : TProgram Γ ts) : TVarList p.returnContext ts where
  toList := p.program.returnVars
  wt := by
    obtain ⟨Δ, wt_is, _, _, _⟩ := p.wt
    obtain rfl : Δ = p.returnContext := by grind
    grind

/-!
## Grind Lemmas
--------------------------------------------------------------------------------
-/

@[simp, grind =] theorem TInstructionSeq.seq_nil : (nil Γ).seq = .nil := by rfl
@[simp, grind =] theorem TInstructionSeq.seq_cons :
  (cons i is).seq = i.instruction ;> is.seq := by rfl

@[simp, grind =] theorem TProgram.instructions_program (p : TProgram Γ ts) :
    p.program.instructions = p.instructions := by rfl
@[simp, grind =] theorem TProgram.returnVars_program (p : TProgram Γ ts) :
    p.program.returnVars = p.returnVars.toList := by rfl

namespace TInstruction
open Ty.Typ (ptr eff data)

@[simp, grind =] theorem instruction_loadI (t : τ.DType) (p : TVar Γ ptr) :
    (TInstruction.loadI t p hΓ).instruction = .loadI t p := rfl

@[simp, grind =] theorem instruction_storeI (t : τ.DType) (p : TVar Γ ptr) (x : TVar Γ t) :
    (TInstruction.storeI t p x hΓ).instruction = .storeI t p x := rfl

@[simp, grind =] theorem instruction_loadE (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr) :
    (TInstruction.loadE t e p).instruction = .loadE t e p := rfl

@[simp, grind =] theorem instruction_storeE (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr)
    (x : TVar Γ t) :
    (TInstruction.storeE t e p x).instruction = .storeE t e p x := rfl

@[simp, grind =] theorem instruction_createEff (hΓ : Γ.isUnrestricted) :
    (TInstruction.createEff hΓ).instruction = .createEff := rfl

@[simp, grind =] theorem instruction_consumeEff (e : TVar Γ eff)
    (hΓ : (Γ.eraseVar e).isUnrestricted) :
    (TInstruction.consumeEff e hΓ).instruction = .consumeEff e := rfl

end TInstruction

namespace TProgram
variable {Γ Δ : Context τ} (is : TInstructionSeq Γ Δ) (vs : TVarList Δ ts)

@[simp, grind =] theorem program_mk' : (mk' is vs h).program = ⟨is.seq, vs.toList⟩ := by rfl
@[simp, grind =] theorem returnVars_mk' : (mk' is vs h).returnContext = Δ := by grind

end TProgram

/-!
## Induction Principles
--------------------------------------------------------------------------------
FIXME: For now, let's just do induction, no data-producing recursion yet!
-/

open Ty.Typ (ptr eff data) in
@[elab_as_elim, induction_eliminator, cases_eliminator]
def TInstruction.indOn {motive : ∀ {Γ Δ : Context τ}, TInstruction Γ Δ → Prop}
    {Γ Δ} (i : TInstruction Γ Δ)
    (hLoadI : ∀ {Γ} (t : τ.DType) (p : TVar Γ ptr) (hΓ : Γ.isUnrestricted),
      motive (.loadI t p hΓ))
    (hStoreI : ∀ {Γ} (t : τ.DType) (p : TVar Γ ptr) (x : TVar Γ (data t)) (hΓ : Γ.isUnrestricted),
      motive (.storeI t p x hΓ))
    (hLoadE : ∀ {Γ} (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr),
      motive (.loadE t e p))
    (hStoreE : ∀ {Γ} (t : τ.DType) (e : TVar Γ eff) (p : TVar Γ ptr)
      (x : TVar Γ (data t)),
      motive (.storeE t e p x))
    (hCreateEff : ∀ {Γ : Context τ} (hΓ : Γ.isUnrestricted),
      motive (.createEff hΓ))
    (hConsumeEff : ∀ {Γ} (e : TVar Γ eff) (hΓ : (Γ.eraseVar e).isUnrestricted),
      motive (.consumeEff e hΓ)) :
    motive i := by
  obtain ⟨i, wt⟩ := i
  match wt with
  | .loadI hΓ hp => exact hLoadI _ ⟨_, hp⟩ hΓ
  | .storeI hΓ hp hx => exact hStoreI _ ⟨_, hp⟩ ⟨_, hx⟩ hΓ
  | .loadE he hp => exact hLoadE _ ⟨_, he⟩ ⟨_, hp⟩
  | .storeE he hp hx => exact hStoreE _ ⟨_, he⟩ ⟨_, hp⟩ ⟨_, hx⟩
  | .createEff hΓ => exact hCreateEff hΓ
  | .consumeEff he hΓ => exact hConsumeEff ⟨_, he⟩ hΓ

@[elab_as_elim, induction_eliminator]
def TInstructionSeq.indOn {motive : ∀ {Γ Δ : Context τ}, TInstructionSeq Γ Δ → Prop}
    {Γ Δ} (is : TInstructionSeq Γ Δ)
    (nil : ∀ Γ, motive (.nil Γ))
    (cons : ∀ {Γ Δ Ξ} (i : TInstruction Γ Δ) (is : TInstructionSeq Δ Ξ),
      motive is → motive (.cons i is)) :
    motive is :=
  match is with
  | ⟨_, .nil h_eq⟩ => h_eq ▸ (nil _)
  | ⟨i ;> is, .cons wt_i wt_is⟩ =>
      let i : TInstruction Γ _ := ⟨i, wt_i⟩
      let is : TInstructionSeq _ Δ := ⟨is, wt_is⟩
      cons i is (indOn is nil cons)

@[elab_as_elim, cases_eliminator]
def TProgram.casesOn' {motive : ∀ {Γ : Context τ} {ts}, TProgram Γ ts → Prop}
    {Γ ts} (p : TProgram Γ ts)
    (mk' : ∀ {Γ Δ : Context τ} {ts} (is : TInstructionSeq Γ Δ) (vs : TVarList Δ ts)
      (h : (Δ.eraseVars vs.toList).isUnrestricted),
      motive (.mk' is vs h)) :
    motive p :=
  let ⟨⟨is, vs⟩, ⟨Δ, wt_is, h_un, length_eq, wt_vs⟩⟩ := p
  let is : TInstructionSeq Γ Δ := ⟨is, wt_is⟩
  let vs : TVarList Δ ts := { toList := vs }
  mk' is vs h_un

/-!
## Lemmas
--------------------------------------------------------------------------------
-/

@[simp, grind =] theorem TProgram.isUnrestricted_returnContext (p : TProgram Γ ts) :
    p.returnContext.isUnrestricted ↔ Context.isUnrestricted ⟨ts⟩ := by
  cases p with | @mk' _ Δ _ is vs h =>
  simp only [returnVars_mk', Context.isUnrestricted_iff_getElem?, Option.mem_def,
    Context.getElem?_ofList]
  constructor
  · intro hΔ v t ht
    let w := vs.toList[v.toNat]'(by grind)
    apply hΔ w _
    grind [vs.wt ⟨v.toNat, by grind⟩]
  · intro hts v t hvt
    rw [Context.isUnrestricted_iff_getElem?, Context.forall_getElem?_eraseVars] at h
    by_cases hv : v ∈ vs.toList
    · obtain ⟨i, hi⟩ : ∃ (i : Fin ts.length), vs.toList[i]'(by grind) = v := by
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hv
        use ⟨i, by grind⟩
        grind
      apply hts (.ofNat i)
      grind
    · grind
