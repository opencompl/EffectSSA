import EffectSSA.Syntax.Typed
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas
import EffectSSA.Semantics.Typed.TEnvironment
import EffectSSA.Semantics.Typed.TTrace

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

def TInstruction.exec (i : TInstruction Γ Δ) (env : TEnvironment Γ) (es : TTrace Γ) :
    TEnvironment Δ × (TTrace Δ) :=
  let res := (i.instruction.exec env.env es.get?).get <| Instruction.isSome_exec i.wt env.wt
  have env_wt := by
    subst res
    cases i
    <;> (simp [Instruction.exec, Instruction.execM]; grind)
    -- TODO: Surely, this (^^) should be do-able without needing `simp` before `grind`
  have trace_wt := by
    subst res
    cases i <;> (simp [Instruction.exec, Instruction.execM]; grind)
  ⟨⟨res.1, env_wt⟩, ⟨res.2, trace_wt⟩⟩

@[grind =>]
theorem Instruction.exec_eq_of_wellTyped {i : Instruction τ} {env : Environment τ} {es? : Option (Trace τ)}
    (wt_i : i.WellTyped Γ Δ) (wt_env : env.WellTyped Γ) (wt_es?) :
    i.exec env es? = some (
      let r := TInstruction.exec ⟨i, wt_i⟩ ⟨env, wt_env⟩ ⟨es?, wt_es?⟩
      (r.1.env, r.2.get?)
    ) := by
  simp [TInstruction.exec]

@[simp, grind =]
theorem TInstruction.exec_instruction_eq {i : TInstruction Γ Δ} {env : TEnvironment Γ} (es : TTrace Γ) :
    i.instruction.exec env.env es.get? = some (
      let r := i.exec env es
      (r.1.env, r.2.get?)
    ) := by
  rw [Instruction.exec_eq_of_wellTyped]

/-!
## InstructionSeq
-/

@[grind! <=]
theorem InstructionSeq.isSome_exec {is : InstructionSeq τ} {env : Environment τ}
    (wt_is : is.WellTypedWith Γ Δ) (wt_env : env.WellTyped Γ) (wt_es : Trace.WellTyped es Γ) :
    (is.exec env es).isSome := by
  obtain ⟨env, rfl⟩ : ∃ (env' : TEnvironment _), env = env'.env := ⟨⟨env, wt_env⟩, rfl⟩
  obtain ⟨is, rfl⟩ : ∃ (is' : TInstructionSeq _ _), is = is'.seq := ⟨⟨is, wt_is⟩, rfl⟩
  obtain ⟨es, rfl⟩ : ∃ (es' : TTrace Γ), es = es'.get? := ⟨⟨es, wt_es⟩, rfl⟩
  clear wt_env wt_is wt_es
  induction is <;> simp [*]

def TInstructionSeq.exec (is : TInstructionSeq Γ Δ) (env : TEnvironment Γ) (es? : TTrace Γ) :
    TEnvironment Δ × TTrace Δ :=
  let res := (is.seq.exec env es?).get <| InstructionSeq.isSome_exec is.wt env.wt es?.wt
  have wt₁ := by intro v t; induction is <;> grind
  have wt₂ := by induction is <;> grind
  ⟨⟨res.1, wt₁⟩, ⟨res.2, wt₂⟩⟩


@[grind =>]
theorem InstructionSeq.exec_eq_of_wellTyped (wt_i : is.WellTypedWith Γ Δ)
    (wt_env : env.WellTyped Γ) (wt_es? : Trace.WellTyped es? Γ) :
    is.exec env es? = some (
      let r := TInstructionSeq.exec ⟨is, wt_i⟩ ⟨env, wt_env⟩ ⟨es?, wt_es?⟩
      (r.1.env, r.2.get?)
    ) := by
  simp [TInstructionSeq.exec]

@[simp, grind =]
theorem TInstructionSeq.exec_instruction {is : TInstructionSeq Γ Δ} {env : TEnvironment Γ}
    {es? : TTrace Γ}:
    is.seq.exec env.env es?.get? = some (
      let r := is.exec env es?
      (r.1.env, r.2.get?)
    ) := by
  rw [InstructionSeq.exec_eq_of_wellTyped]

/-!
## Program
-/

@[grind <=] theorem Program.isSome_exec {p : Program τ} {env : Environment τ}
    (wt_p : p.WellTyped Γ ts) (wt_env : env.WellTyped Γ) (wt_es : Trace.WellTyped es Γ) :
    (p.exec env es).isSome := by
  obtain ⟨env, rfl⟩ : ∃ (env' : TEnvironment _), env = env' := ⟨⟨env, wt_env⟩, rfl⟩
  obtain ⟨p, rfl⟩ : ∃ (p' : TProgram _ _), p = p' := ⟨⟨p, wt_p⟩, rfl⟩
  obtain ⟨es, rfl⟩ : ∃ (es' : TTrace Γ), es = es'.get? := ⟨⟨es, wt_es⟩, rfl⟩
  simp [exec, execM]

def TProgram.exec (p : TProgram Γ ts) (env : TEnvironment Γ) (es? : TTrace Γ) :
    TEnvironment ⟨ts⟩ × TTrace ⟨ts⟩ :=
  let res := (p.program.exec env es?).get <| Program.isSome_exec p.wt env.wt es?.wt
  have wt₁ := by simp [res, Environment.WellTyped, Program.exec, Program.execM]
  have wt₂ := by simp [res, Trace.WellTyped, Program.exec, Program.execM]
  ⟨⟨res.1, wt₁⟩, ⟨res.2, wt₂⟩⟩

@[grind] def TProgram.execClosed (p : TProgram (τ:=τ) ∅ ts) :
    TEnvironment ⟨ts⟩ × TTrace ⟨ts⟩  :=
  p.exec ∅ ∅

section Lemmas

@[grind =>]
theorem Program.exec_eq_of_wellTyped {p : Program τ} {env : Environment τ}
    (wt_p : p.WellTyped Γ ts) (wt_env : env.WellTyped Γ) (wt_es? : Trace.WellTyped es? Γ) :
    p.exec env es? = some (
      let r := TProgram.exec ⟨p, wt_p⟩ ⟨env, wt_env⟩ ⟨es?, wt_es?⟩
      (r.1.env, r.2.get?)
    ) := by
  simp [TProgram.exec]

@[simp, grind =]
theorem TProgram.exec_program {p : TProgram Γ ts} {env : TEnvironment Γ}
    {es? : TTrace Γ}:
    p.program.exec env.env es?.get? = some (
      let r := p.exec env es?
      (r.1.env, r.2.get?)
    ) := by
  simp [Program.exec_eq_of_wellTyped p.wt env.wt es?.wt]


@[simp, grind =] theorem TProgram.execClosed_program {p : TProgram (τ:=τ) ∅ ts} :
    p.program.execClosed = some (
      let r := p.execClosed
      (r.1.env, r.2.get?)
    ) := by
  have : (∅ : Environment τ) = (∅ : TEnvironment (τ:=τ) ∅) := rfl
  have : (some ∅ : Option (Trace τ)) = (∅ : TTrace (τ:=τ) ∅) := rfl
  grind [Program.execClosed]

@[simp] theorem Program.execClosed_eq_of_wellTyped {p : Program τ}
    (wt : p.WellTyped ∅ ts):
    p.execClosed = some (
      let r := TProgram.execClosed ⟨p, wt⟩
      (r.1.env, r.2.get?)
    ) := by
  generalize hp : TProgram.mk p wt = p'
  have : p = p'.program := by grind
  grind

end Lemmas
