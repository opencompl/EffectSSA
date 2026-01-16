import EffectSSA.Types.WellTyped

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-! ### `grind` annotation of the constructors -/

open Instruction in attribute [grind ←]
  WellTyped.loadI
  WellTyped.storeI
  WellTyped.loadE
  WellTyped.storeE
  WellTyped.createEff
  WellTyped.consumeEff

open Program in attribute [grind →]
  -- WellTypedWith.nil
  WellTypedWith.cons
