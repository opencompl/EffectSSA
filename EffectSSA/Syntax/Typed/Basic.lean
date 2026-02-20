import EffectSSA.Syntax.Untyped
import EffectSSA.Syntax.Typed.TVar
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

def TInstructionSeq.nil (Γ : Context τ) : TInstructionSeq Γ Γ where seq := .nil
def TInstructionSeq.cons (i : TInstruction Γ Δ) (is : TInstructionSeq Δ Ξ) :
    TInstructionSeq Γ Ξ where
  seq := i ;> is

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

def TProgram.returnVars (p : TProgram Γ ts) : TVarList Γ ts where
  vs := ⟨p.program.returnVars, by grind⟩
  wt := by
    intro i;
    have ⟨_, _, _, len_eq, wt⟩ := p.wt
    specialize wt i.val (by grind)
    /-
    FIXME: proving this will likely be nicer with some theory around context
    "extensions". I.e., we likely want some API which allows us to conclude
    that context `Δ` "extends" `Γ` from `Γ ⊢ ... :: Δ`, which in turn will
    let us know that `Δ[v]? = some t` implies `Γ[v]? = some t`.
    If we had such API, the following sorry ought to be provable by grind.
    -/
    sorry

/-!
## Lemmas
--------------------------------------------------------------------------------
-/

@[simp, grind =] theorem TInstructionSeq.seq_nil : (nil Γ).seq = .nil := by rfl
@[simp, grind =] theorem TInstructionSeq.seq_cons :
  (cons i is).seq = i.instruction ;> is.seq := by rfl


/-!
## Induction Principles
--------------------------------------------------------------------------------
FIXME: For now, let's just do induction, no data-producing recursion yet!
-/

@[elab_as_elim, induction_eliminator]
def TInstructionSeq.indOn {motive : ∀ {Γ Δ : Context τ}, TInstructionSeq Γ Δ → Prop}
    {Γ Δ} (is : TInstructionSeq Γ Δ)
    (nil : ∀ Γ, motive (.nil Γ))
    (cons : ∀ {Γ Δ Ξ} (i : TInstruction Γ Δ) (is : TInstructionSeq Δ Ξ),
      motive is → motive (.cons i is)) :
    motive is :=
  match is with
  | ⟨.nil, .nil h_eq⟩ => h_eq ▸ (nil _)
  | ⟨i ;> is, .cons wt_i wt_is⟩ =>
      let i : TInstruction Γ _ := ⟨i, wt_i⟩
      let is : TInstructionSeq _ Δ := ⟨is, wt_is⟩
      cons i is (indOn is nil cons)
