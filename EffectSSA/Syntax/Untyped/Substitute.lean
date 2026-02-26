import EffectSSA.Syntax.Untyped.Basic

/-!
# Variable Substitution in Programs
-/
namespace EffectSSA

/-!
## Definition of Substitution
--------------------------------------------------------------------------------
-/

structure Substitution where
  apply : Var → Var

/-- The trivial identity substitution. -/
def Substitution.id : Substitution where
  apply v := v

def Substitution.offset (σ : Substitution) (n : Nat) : Substitution where
  apply v := if v.toNat < n then v else (σ.apply <| v - n) + n

/--
`i.substitute σ` substitutes free variables in an instruction `i` along a
substitution `σ`, such that a free variable with index `j` is replaced with the
variable `σ j`.
-/
def Instruction.substitute (σ : Substitution) : Instruction τ → Instruction τ
  -- Basic memory ops with implicit effects
  | .loadI t p    => .loadI t (σ.apply p)
  | .storeI t p x => .storeI t (σ.apply p) x
  | .allocI t p   => .allocI t (σ.apply p)
  | .freeI t p    => .freeI t (σ.apply p)
  -- Basic memory ops in EffectSSA form
  | .loadE t eff p    => .loadE t (σ.apply eff) (σ.apply p)
  | .storeE t eff p x => .storeE t (σ.apply eff) (σ.apply p) x
  | .allocE t eff p   => .allocE t (σ.apply eff) (σ.apply p)
  | .freeE t eff p    => .freeE t (σ.apply eff) (σ.apply p)
  -- Effect Bookkeeping
  | .split eff        => .split (σ.apply eff)
  | .merge eff₁ eff₂  => .merge (σ.apply eff₁) (σ.apply eff₂)
  | .createEff        => .createEff
  | .consumeEff eff   => .consumeEff (σ.apply eff)

def Substitution.offsetFor (σ : Substitution) : Instruction τ → Substitution
  -- Basic memory ops with implicit effects
  | .loadI ..  => σ.offset 1
  | .storeI .. => σ
  | .allocI .. => σ
  | .freeI ..  => σ
  -- Basic memory ops in EffectSSA form
  | .loadE ..  => σ.offset 2
  | .storeE .. => σ.offset 1
  | .allocE .. => σ.offset 1
  | .freeE ..  => σ.offset 1
  -- Effect Bookkeeping
  | .split ..       => σ.offset 2
  | .merge ..       => σ.offset 1
  | .createEff ..   => σ.offset 1
  | .consumeEff ..  => σ

/--
`p.substitute σ` substitutes free variables in an instruction sequence `p` along
a substitution `σ`, such that a free variable with index `j` is replaced with
the variable `σ j`.
-/
def InstructionSeq.substitute (σ : Substitution) : InstructionSeq τ → InstructionSeq τ
  | .nil    => .nil
  | i ;> p  => i.substitute σ ;> p.substitute (σ.offsetFor i)

/-!
## Program Concatenation
--------------------------------------------------------------------------------
-/

-- TODO: we likely need something akin to the following to implement Program.append
-- def Program.shiftVars (p : Program τ) (n : Nat) : Program τ := sorry

/-!
Program concatenation, written `p ++ q`, is defined as concatenating the
instructions of `p` and `q`, where the return variables of `p` are substituted
for the respective free variable of `q`.

NOTE: The number of free variables in `p ++ q` is thus
  `fvars(p) + (fvars(q) - retvars(p))`
where the subtraction bottoms out at 0.

-/
def Program.append (p : Program τ) (q : Program τ) : Program τ :=
  -- TODO: implement
  sorry
instance : Append (Program τ) where append := Program.append

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
variable {σ δ : Substitution}

/-! ### Substitution -/
namespace Substitution

@[ext]
theorem ext (h : ∀ v, σ.apply v = δ.apply v) : σ = δ := by
  cases σ; cases δ; congr; funext v; apply h

@[simp, grind =]
theorem apply_id : id.apply v = v := rfl

@[simp, grind =]
theorem offset_id : id.offset n = id := by
  ext v; grind [offset]

@[simp, grind =]
theorem offsetFor_id : id.offsetFor i = id := by
  simp only [offsetFor, offset_id]; split <;> rfl

end Substitution

/-! ### Structural Program Lemmas -/
namespace InstructionSeq

@[simp, grind =]
theorem substitute_nil : (@nil τ).substitute σ = nil := rfl

end InstructionSeq

/-! ### substitute_id -/

@[simp, grind =]
theorem Instruction.substitute_id (i : Instruction τ) : i.substitute .id = i := by
  cases i <;> simp [substitute]

@[simp, grind =]
theorem InstructionSeq.substitute_id (p : InstructionSeq τ) : p.substitute .id = p := by
  induction p <;> simp [substitute, *]
