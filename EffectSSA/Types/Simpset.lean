import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Typecheck Simpset

This file defines the `typecheck` simpset, used for simplifying type checking goals.
-/

namespace EffectSSA

register_simp_attr typecheck
