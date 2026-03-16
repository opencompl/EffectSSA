import EffectSSA.Syntax.Untyped
import EffectSSA.Semantics
import EffectSSA.Rewrites.Basic

import EffectSSA.Tactic

/-!
# Implicit to EffectSSA conversion rewrites
-/
namespace EffectSSA
open Semantics (TProgramContext TEnvironment)
namespace Rewrites

variable {τ} [LawfulMemoryModel τ]

def createEff_consumeEff : TRewrite (τ:=τ) ∅ [] where
  rSrc := {
    instructions := program!()
    returnVars := []
  }
  rTgt := {
    instructions := program!(
      e := createEff;
      consumeEff(e)
    )
    returnVars := []
  }

theorem createEff_consumeEff.correct : (@createEff_consumeEff τ).Correct := by
  intro C
  simp [TProgramContext.execProgram]
  have h_src (env) (es?) :
      (@createEff_consumeEff τ).src.exec env es? = ((∅ : TEnvironment ∅), es?) := by
    rfl
  have h_tgt (env) (es?) :
      (@createEff_consumeEff τ).tgt.exec env es? = ((∅ : TEnvironment ∅), es?) := by
    simp only [TProgram.exec, Program.exec, Program.execM, TRewrite.tgt, createEff_consumeEff,
      InstructionSeq.execM_cons, InstructionSeq.execM_nil, bind_pure,
      Semantics.Environment.limitTo?_nil, bind_assoc, ExecM.run_bind, Instruction.run_execM,
      ExecM.run_liftM, Option.bind_eq_bind, Option.bind_some, Option.get_bind, Option.get_some,
      Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    congr
    simp [Instruction.exec, Instruction.execM]
    grind
  rw [h_src, h_tgt]
