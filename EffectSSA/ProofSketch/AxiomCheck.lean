import EffectSSA.ProofSketch.ProofSketch

/-!
We can't use `#print axioms` in a module, so we have moved the axiom check
to this separate file.
-/
namespace EffectSSA.ProofSketch


/--
info: 'EffectSSA.ProofSketch.Pattern.ctxRefine_of_denoteRefine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Inst,
 State,
 Val,
 Inst.args,
 Inst.decideEq,
 Inst.denote,
 Inst.denote_isRefinedBy_congr,
 Inst.results,
 State.Refine,
 State.initial,
 Val.Refine]
-/
#guard_msgs in #print axioms Pattern.ctxRefine_of_denoteRefine
