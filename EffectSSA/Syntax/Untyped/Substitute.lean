import EffectSSA.Syntax.Untyped.Basic
import EffectSSA.Syntax.Untyped.Lemmas

/-!
# Variable Substitution in Programs
-/
namespace EffectSSA

/-!
## Definition of Substitution
--------------------------------------------------------------------------------
-/

/--
A `Substitution` is a function `Var → Var`
-/
structure Substitution where
  apply : Var → Var
instance : CoeFun Substitution (fun _ => Var → Var) where
  coe σ := σ.apply

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
  | .storeI t p x => .storeI t (σ.apply p) (σ.apply x)
  | .allocI t p   => .allocI t (σ.apply p)
  | .freeI t p    => .freeI t (σ.apply p)
  -- Basic memory ops in EffectSSA form
  | .loadE t eff p    => .loadE t (σ.apply eff) (σ.apply p)
  | .storeE t eff p x => .storeE t (σ.apply eff) (σ.apply p) (σ.apply x)
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

/--
`σ.offsetForSeq p` is the substitution obtained by advancing `σ` past all
instructions in `p`, i.e., the substitution under which code *after* `p`
should be evaluated.
-/
def Substitution.offsetForSeq (σ : Substitution) : InstructionSeq τ → Substitution
  | .nil    => σ
  | i ;> p  => (σ.offsetFor i).offsetForSeq p


-- TODO: We might need a Program.substitute eventually

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
theorem offset_apply_lt (σ : Substitution) {v : Var} {n : Nat} (h : v.toNat < n) :
    (σ.offset n).apply v = v := by simp [offset, h]

@[simp, grind =]
theorem offset_apply_ge (σ : Substitution) {v : Var} {n : Nat} (h : ¬v.toNat < n) :
    (σ.offset n).apply v = (σ.apply (v - n)) + n := by simp [offset, h]

@[simp, grind =]
theorem offsetFor_id : id.offsetFor i = id := by
  simp only [offsetFor, offset_id]; split <;> rfl

end Substitution

/-! ### Instruction.substitute -/
namespace Instruction
variable {τ : Ty}

@[simp, grind =] theorem substitute_loadI  : (loadI t p).substitute σ = loadI t (σ p) := rfl
@[simp, grind =] theorem substitute_storeI : (storeI t p x).substitute σ = storeI t (σ p) (σ x) := rfl
@[simp, grind =] theorem substitute_allocI : (allocI t p).substitute σ = allocI t (σ p) := rfl
@[simp, grind =] theorem substitute_freeI  : (freeI t p).substitute σ = freeI t (σ p) := rfl
@[simp, grind =] theorem substitute_loadE  : (loadE t e p).substitute σ = loadE t (σ e) (σ p) := rfl
@[simp, grind =] theorem substitute_storeE : (storeE t e p x).substitute σ = storeE t (σ e) (σ p) (σ x) := rfl
@[simp, grind =] theorem substitute_allocE : (allocE t e p).substitute σ = allocE t (σ e) (σ p) := rfl
@[simp, grind =] theorem substitute_freeE  : (freeE t e p).substitute σ = freeE t (σ e) (σ p) := rfl
@[simp, grind =] theorem substitute_split  : (split (τ := τ) e).substitute σ = split (σ e) := rfl
@[simp, grind =] theorem substitute_merge  : (merge (τ := τ) e₁ e₂).substitute σ = merge (σ e₁) (σ e₂) := rfl
@[simp, grind =] theorem substitute_createEff  : (createEff (τ := τ)).substitute σ = createEff := rfl
@[simp, grind =] theorem substitute_consumeEff : (consumeEff (τ := τ) e).substitute σ = consumeEff (σ e) := rfl

end Instruction

/-! ### Substitution.offsetFor -/
namespace Substitution
variable {τ : Ty}

@[simp, grind =] theorem offsetFor_loadI  : σ.offsetFor (.loadI t p)      = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_storeI : σ.offsetFor (.storeI t p x)   = σ := rfl
@[simp, grind =] theorem offsetFor_allocI : σ.offsetFor (.allocI t p)     = σ := rfl
@[simp, grind =] theorem offsetFor_freeI  : σ.offsetFor (.freeI t p)      = σ := rfl
@[simp, grind =] theorem offsetFor_loadE  : σ.offsetFor (.loadE t e p)    = σ.offset 2 := rfl
@[simp, grind =] theorem offsetFor_storeE : σ.offsetFor (.storeE t e p x) = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_allocE : σ.offsetFor (.allocE t e p)   = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_freeE  : σ.offsetFor (.freeE t e p)    = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_split      : σ.offsetFor (.split (τ := τ) e)      = σ.offset 2 := rfl
@[simp, grind =] theorem offsetFor_merge      : σ.offsetFor (.merge (τ := τ) e₁ e₂) = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_createEff  : σ.offsetFor (.createEff (τ := τ))    = σ.offset 1 := rfl
@[simp, grind =] theorem offsetFor_consumeEff : σ.offsetFor (.consumeEff (τ := τ) e) = σ := rfl

@[simp, grind =] theorem offsetForSeq_nil  : σ.offsetForSeq (.nil (τ := τ)) = σ := rfl
@[simp, grind =] theorem offsetForSeq_cons (i : Instruction τ) (p : InstructionSeq τ) :
    σ.offsetForSeq (i ;> p) = (σ.offsetFor i).offsetForSeq p := rfl

@[simp, grind =] theorem offsetForSeq_id (p : InstructionSeq τ) : id.offsetForSeq p = id := by
  induction p <;> grind

end Substitution

/-! ### Structural InstructionSeq Lemmas -/
namespace InstructionSeq

@[simp, grind =]
theorem substitute_nil : (@nil τ).substitute σ = nil := rfl

@[simp, grind =]
theorem substitute_cons : (i ;> p).substitute σ = i.substitute σ ;> p.substitute (σ.offsetFor i) := rfl

@[simp, grind =]
theorem substitute_append (p q : InstructionSeq τ) :
    (p ++ q).substitute σ = p.substitute σ ++ q.substitute (σ.offsetForSeq p) := by
  induction p generalizing σ <;> grind [substitute]

end InstructionSeq

/-! ### substitute_id -/

@[simp, grind =]
theorem Instruction.substitute_id (i : Instruction τ) : i.substitute .id = i := by
  cases i <;> simp [substitute]

@[simp, grind =]
theorem InstructionSeq.substitute_id (p : InstructionSeq τ) : p.substitute .id = p := by
  induction p <;> simp [substitute, *]
