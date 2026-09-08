module

/-!
# Dominance

This file defines dominance for a generic graph structure.
Based on CompcertSSA [1]

[1] https://compcertssa.gitlabpages.inria.fr/html/compcert.midend.Dom.html
-/
@[expose] public section
namespace EffectSSA.ProofSketch

/--
`HasDominance α` shows that `α` is a type of nodes in some generic graph
structure.
-/
class HasDominance α where
  entry : α
  isExit : α → Prop
  cfg : α → α → Prop

variable {α : Type} [HasDominance α]

open HasDominance

/-!
## Reachability

A node is reachable if there is a path of CFG edges from `entry`.

> **Mathlib note**: `Reached pc` is exactly `Relation.ReflTransGen cfg entry pc`.
> Using Mathlib would give `head`, `tail`, transitivity, etc. for free.
-/

/-- A node is reachable from `entry` via a finite chain of CFG edges. -/
inductive Reached : α → Prop where
  | entry : Reached HasDominance.entry
  | step  {pc pc' : α} : Reached pc → cfg pc pc' → Reached pc'

/-!
## Paths

Paths follow the CompCert SSA convention: each step *emits* its source node,
so the collected list records the sequence of nodes departed from.
-/

/-- A path state: either located at some active node, or stopped past an exit. -/
inductive PState (α : Type) where
  | active  : α → PState α
  | stopped : PState α

/-- A single step along the CFG: advance to a successor, or halt at an exit. -/
inductive PathStep : PState α → α → PState α → Prop where
  | cont {pc pc' : α} : cfg pc pc'  → PathStep (.active pc) pc (.active pc')
  | stop {pc : α}     : isExit pc   → PathStep (.active pc) pc .stopped

/-- A path is a sequence of steps; the node list records the *source* of each step. -/
inductive Path : PState α → List α → PState α → Prop where
  | nil  (s : PState α) : Path s [] s
  | cons {s₁ s₂ s₃ : PState α} {pc : α} {t : List α} :
      PathStep s₁ pc s₂ → Path s₂ t s₃ → Path s₁ (pc :: t) s₃

/-! ### Path lemmas -/

/-- There is no path from a stopped state to an active state. -/
theorem Path.not_from_stopped {pc' : α} {p : List α}
    (h : Path (.stopped : PState α) p (.active pc')) : False := by
  cases h with
  | cons hstep _ => cases hstep

/-- Paths can be concatenated. -/
theorem Path.append {s₁ s₂ s₃ : PState α} {p q : List α} :
    Path s₁ p s₂ → Path s₂ q s₃ → Path s₁ (p ++ q) s₃ := by
  intro hp hq
  induction hp with
  | nil       => exact hq
  | cons hs _ ih => exact Path.cons hs (ih hq)

/-- Every reachable node has an explicit path from `entry`. -/
theorem reached_has_path {pc : α} (h : Reached pc) :
    ∃ p, Path (.active entry) p (.active pc) :=
  -- Avoid naming this `Reached.has_path`: the `Reached.` prefix causes Lean to
  -- resolve `entry` in the type as the `Reached.entry` constructor (Prop) rather
  -- than `HasDominance.entry` (α).
  match h with
  | .entry => ⟨[], .nil _⟩
  | .step hpc hcfg =>
    let ⟨p, hp⟩ := reached_has_path hpc
    ⟨p ++ [_], hp.append (.cons (.cont hcfg) (.nil _))⟩

/-!
## Dominance

Node `pc` *dominates* `pc'` if every path from `entry` to `pc'` passes through `pc`.
This matches the CompCert SSA definition exactly.
-/

/-- `Dom pc pc'`: `pc` dominates `pc'`. -/
inductive Dom : α → α → Prop where
  | refl (pc : α) : Dom pc pc
  | path {pc pc' : α} :
      Reached pc' →
      (∀ p, Path (.active entry) p (.active pc') → pc ∈ p) →
      Dom pc pc'

/-- `SDom pc pc'`: `pc` *strictly* dominates `pc'` (dominates but is distinct). -/
structure SDom (pc pc' : α) : Prop where
  dom : Dom pc pc'
  ne  : pc ≠ pc'

/-! ### Order properties -/

@[simp] theorem dom_refl (pc : α) : Dom pc pc := Dom.refl pc

/-- Transitivity: split any path to `pc₃` at `pc₂`, then apply dominance at `pc₂`.
    Requires `in_path_split`; left as `sorry`. -/
theorem dom_trans {pc₁ pc₂ pc₃ : α} :
    Dom pc₁ pc₂ → Dom pc₂ pc₃ → Dom pc₁ pc₃ := by
  sorry

/-- Antisymmetry: follows from a well-founded path-length argument via `in_path_split`.
    Left as `sorry`. -/
theorem dom_antisymm {pc pc' : α} :
    Dom pc pc' → Dom pc' pc → pc = pc' := by
  sorry

/-! ### Entry node -/

/-- Any path from `entry` to a distinct node must have `entry` as its first element,
    since `PathStep` records the source node. -/
private theorem path_mem_entry {p : List α} {pc' : α}
    (hne : pc' ≠ entry) (hp : Path (.active entry) p (.active pc')) : entry ∈ p := by
  cases hp with
  | nil => contradiction
  | cons hstep hrest =>
    cases hstep with
    | cont _ => exact .head _
    | stop _ => exact absurd hrest Path.not_from_stopped

/-- `entry` dominates every reachable node. -/
theorem entry_dom {pc : α} (h : Reached pc) : Dom entry pc := by
  rcases Classical.em (pc = entry) with rfl | hne
  · exact Dom.refl entry
  · exact Dom.path h (fun p hp => path_mem_entry hne hp)

/-- No node strictly dominates `entry`.

    The `Dom.path` case would require `pc ∈ []` (from the empty reflexive path
    `entry → entry`), which is vacuously false. -/
theorem not_sdom_entry (pc : α) : ¬SDom pc entry := by
  intro ⟨hdom, hne⟩
  cases hdom with
  | refl => exact hne rfl
  | path _ hpaths => exact List.not_mem_nil (hpaths [] (Path.nil _))

/-! ### Strict dominance -/

theorem sdom_trans {pc₁ pc₂ pc₃ : α} :
    SDom pc₁ pc₂ → SDom pc₂ pc₃ → SDom pc₁ pc₃ :=
  fun ⟨hd₁₂, hne₁₂⟩ ⟨hd₂₃, _⟩ =>
    ⟨dom_trans hd₁₂ hd₂₃,
     fun h => hne₁₂ (by subst h; exact dom_antisymm hd₁₂ hd₂₃)⟩

theorem dom_sdom_trans {pc₁ pc₂ pc₃ : α} :
    Dom pc₁ pc₂ → SDom pc₂ pc₃ → SDom pc₁ pc₃ :=
  fun h₁₂ ⟨h₂₃, hne₂₃⟩ =>
    ⟨dom_trans h₁₂ h₂₃,
     fun h => hne₂₃ (by subst h; exact dom_antisymm h₂₃ h₁₂)⟩

/-!
## Path splitting

The key auxiliary for `dom_trans` and `dom_antisymm`: if a node appears in a path,
the path can be split at that occurrence.

-/

/-- If `pc''` appears in path `p`, then `p` splits into a prefix that reaches
    `pc''`, a step departing `pc''`, and a suffix. -/
theorem in_path_split {s₁ s₃ : PState α} {p : List α} {pc'' : α}
    (hmem : pc'' ∈ p) (hp : Path s₁ p s₃) :
    ∃ p₁ p₂ s₂,
      Path s₁ p₁ (.active pc'') ∧
      PathStep (.active pc'') pc'' s₂ ∧
      Path s₂ p₂ s₃ ∧
      p = p₁ ++ pc'' :: p₂ := by
  sorry

end EffectSSA.ProofSketch
