import EffectSSA.Syntax.Typed
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas
import EffectSSA.Semantics.Typed.TEnvironment

/-!
# Semantics of Intrinsically Typed Programs
This file uses the untyped semantics to define semantics for intrinsically
well-typed programs. This is particularly useful, since the welltypedness
means these semantics can never return a type error.
-/
namespace EffectSSA
variable {τ} [MemoryModel τ] {Γ Δ : Context τ}

open Semantics (Environment TEnvironment)

/-!
## Instruction
--------------------------------------------------------------------------------
-/

@[grind <=]
theorem Instruction.isSome_exec {i : Instruction τ} {env : Environment τ}
    (wt_i : i.WellTyped Γ Δ) (wt_env : env.WellTyped Γ) :
    (i.exec env es).isSome := by
  obtain ⟨env, rfl⟩ : ∃ (env' : TEnvironment _), env = env' := ⟨⟨env, wt_env⟩, rfl⟩
  clear wt_env
  unfold exec execM
  cases wt_i <;> (simp; (repeat rw [TEnvironment.env_getAs_eq (by assumption)]); try grind)
  next => simp

def TInstruction.exec (i : TInstruction Γ Δ) (env : TEnvironment Γ) (es : Option (Trace τ)) :
    TEnvironment Δ × (Option (Trace τ)) :=
  let res := (i.instruction.exec env.env es).get <| Instruction.isSome_exec i.wt env.wt
  have wt := by
    subst res
    cases i
    <;> (simp [Instruction.exec, Instruction.execM]; grind)
    -- TODO: Surely, this (^^) should be do-able without needing `simp` before `grind`
  ⟨⟨res.1, wt⟩, res.2⟩

@[grind =>]
theorem Instruction.exec_eq_of_wellTyped {i : Instruction τ} {env : Environment τ}
    (wt_i : i.WellTyped Γ Δ) (wt_env : env.WellTyped Γ) (es?) :
    i.exec env es? = some (TInstruction.exec ⟨i, wt_i⟩ ⟨env, wt_env⟩ es?) := by
  simp [TInstruction.exec]

@[simp, grind =]
theorem TInstruction.exec_instruction_eq {i : TInstruction Γ Δ} {env : TEnvironment Γ} :
    i.instruction.exec env.env es? = some (i.exec env es?) := by
  rw [Instruction.exec_eq_of_wellTyped]

/-!
## InstructionSeq
-/

@[grind! <=]
theorem InstructionSeq.isSome_exec {is : InstructionSeq τ} {env : Environment τ}
    (wt_is : is.WellTypedWith Γ Δ) (wt_env : env.WellTyped Γ) :
    (is.exec env es).isSome := by
  obtain ⟨env, rfl⟩ : ∃ (env' : TEnvironment _), env = env' := ⟨⟨env, wt_env⟩, rfl⟩
  obtain ⟨is, rfl⟩ : ∃ (is' : TInstructionSeq _ _), is = is' := ⟨⟨is, wt_is⟩, rfl⟩
  clear wt_env wt_is
  induction is generalizing es <;> simp [*]

def TInstructionSeq.exec (is : TInstructionSeq Γ Δ) (env : TEnvironment Γ) (es? : Option (Trace τ)) :
    TEnvironment Δ × Option (Trace τ) :=
  let res := (is.seq.exec env es?).get <| InstructionSeq.isSome_exec is.wt env.wt
  have wt := by intro v t; induction is generalizing es? <;> grind
  ⟨⟨res.1, wt⟩, res.2⟩


@[grind =>]
theorem InstructionSeq.exec_eq_of_wellTyped {is : InstructionSeq τ} {env : Environment τ}
    (wt_i : is.WellTypedWith Γ Δ) (wt_env : env.WellTyped Γ) (es?) :
    is.exec env es? = some (TInstructionSeq.exec ⟨is, wt_i⟩ ⟨env, wt_env⟩ es?) := by
  simp [TInstructionSeq.exec]

@[simp, grind =]
theorem TInstructionSeq.exec_instruction {is : TInstructionSeq Γ Δ} {env : TEnvironment Γ} :
    is.seq.exec env.env es? = some (is.exec env es?) := by
  rw [InstructionSeq.exec_eq_of_wellTyped]

/-!
## Program
-/

@[grind <=] theorem Program.isSome_exec {p : Program τ} {env : Environment τ}
    (wt_p : p.WellTyped Γ ts) (wt_env : env.WellTyped Γ) :
    (p.exec env es).isSome := by
  obtain ⟨env, rfl⟩ : ∃ (env' : TEnvironment _), env = env' := ⟨⟨env, wt_env⟩, rfl⟩
  obtain ⟨p, rfl⟩ : ∃ (p' : TProgram _ _), p = p' := ⟨⟨p, wt_p⟩, rfl⟩
  simp [exec, execM]

def TProgram.exec (p : TProgram Γ ts) (env : TEnvironment Γ) (es? : Option (Trace τ)) :
    TEnvironment ⟨ts⟩ × Option (Trace τ) :=
  let res := (p.program.exec env es?).get <| Program.isSome_exec p.wt env.wt
  have wt := by
    simp [res, Environment.WellTyped, Program.exec, Program.execM]
  ⟨⟨res.1, wt⟩, res.2⟩

@[grind] def TProgram.execClosed (p : TProgram (τ:=τ) ∅ ts) :
    TEnvironment ⟨ts⟩ × Option (Trace τ) :=
  p.exec ∅ (some ∅)

section Lemmas

@[grind =>]
theorem Program.exec_eq_of_wellTyped {p : Program τ} {env : Environment τ}
    (wt_p : p.WellTyped Γ ts) (wt_env : env.WellTyped Γ) (es?) :
    p.exec env es? = some (TProgram.exec ⟨p, wt_p⟩ ⟨env, wt_env⟩ es? : Environment τ × _) := by
  simp [TProgram.exec]

@[simp, grind =]
theorem TProgram.exec_program {p : TProgram Γ ts} {env : TEnvironment Γ} :
    p.program.exec env.env es? = some (p.exec env es? : Environment τ × _) := by
  simp [Program.exec_eq_of_wellTyped p.wt env.wt]


@[simp, grind =] theorem TProgram.execClosed_program {p : TProgram (τ:=τ) ∅ ts} :
    p.program.execClosed = some (p.execClosed : Environment τ × _) := by
  have : (∅ : Environment τ) = (∅ : TEnvironment (τ:=τ) ∅) := rfl
  simp only [Program.execClosed, this, TProgram.exec_program]
  rfl

@[simp] theorem Program.execClosed_eq_of_wellTyped {p : Program τ}
    (wt : p.WellTyped ∅ ts):
    p.execClosed = some (TProgram.execClosed ⟨p, wt⟩ : Environment τ × _) := by
  generalize hp : TProgram.mk p wt = p'
  have : p = p'.program := by grind
  grind

end Lemmas
