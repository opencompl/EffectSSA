import EffectSSA.Syntax.Untyped
import EffectSSA.Types

/-!
# Intrinsically Well-typed syntax
We define typed variants of syntax datastructure, which bundle an untyped
datastructer with a proof of well-typedness
-/
namespace EffectSSA
variable {τ} [MemorySignature τ]

structure TInstruction (Γ : Context τ) (Δ : Context τ) where
  instruction : Instruction τ
  wt : instruction.WellTyped Γ Δ

structure TInstructionSeq (Γ : Context τ) (Δ : Context τ) where
  seq : InstructionSeq τ
  wt : seq.WellTypedWith Γ Δ

structure TProgram (Γ : Context τ) (ts : List τ.Typ) where
  program : Program τ
  wt : program.WellTyped Γ ts

/-!
## Definitions
--------------------------------------------------------------------------------
-/
variable {Γ : Context τ} {ts : List τ.Typ}

/-- The (internal) context after executing the instruction sequence of `p`. -/
@[grind =]
noncomputable def TProgram.returnContext (p : TProgram Γ ts) : Context τ :=
  p.wt.choose

@[grind =]
def TProgram.instructions (p : TProgram Γ ts) : TInstructionSeq Γ p.returnContext where
  seq := p.program.instructions
  wt := by grind
