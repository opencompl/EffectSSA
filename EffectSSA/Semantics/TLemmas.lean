import EffectSSA.Semantics.TProgram

/-!
# Lemmas About Typed Semantics
-/
namespace EffectSSA
variable {τ} [MemoryModel τ] {ts : List τ.Typ}

/--
NOTE: the invariant is that a program expects the trace to be present iff its
context is unrestricted, and that it will return a trace iff the returnTypes are
unrestricted. We could consider defining an `TTrace Γ` which encodeds this
invariant intrinsically, just like we have `TEnvironment` et al.
-/

@[simp, grind =] theorem TProgram.isSome_snd_exec_some_of (p : TProgram Γ ts)
    (hΓ : Γ.isUnrestricted) :
    (p.exec env (some es)).2.isSome ↔ Context.isUnrestricted ⟨ts⟩ := by
  sorry

@[simp, grind =] theorem TProgram.isSome_snd_none_some_of (p : TProgram Γ ts)
    (hΓ : ¬Γ.isUnrestricted) :
    (p.exec env none).2.isSome ↔ Context.isUnrestricted ⟨ts⟩ := by
  sorry

@[simp, grind =] theorem TProgram.isSome_snd_execClosed_of (p : TProgram ∅ ts) :
    p.execClosed.2.isSome ↔ Context.isUnrestricted ⟨ts⟩ := by
  simp [execClosed]
