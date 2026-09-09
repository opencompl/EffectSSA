module

public import EffectSSA.ProofSketch.Pattern
public import EffectSSA.ProofSketch.Prec
public import EffectSSA.ProofSketch.Rewrite
public import Lean.Elab.Tactic.Simp
public import Lean.Meta.LitValues
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.Meta.Tactic.Simp.Rewrite
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Elab.Tactic.Basic

public section

/-!
## List.idxOf? Simplification

We register two simp-lemmas for the pattern:
  `List.idxOf? x [y, z, ...] = some $n`
Where the rhs is a constant
-/
section ListIdxOf

/-- Peel off a matching head. -/
@[simp, grind =]
theorem List.idxOf?_cons_eq_some_zero [BEq α] [LawfulBEq α] {a b : α} {xs : List α} :
    (b :: xs).idxOf? a = some 0 ↔ b = a := by
  simp [List.idxOf?_cons]

/-- Peel off a non-matching head. -/
@[simp, grind =]
theorem List.idxOf?_cons_eq_some_succ [BEq α] [LawfulBEq α] {a b : α} {xs : List α} {n : Nat} :
    (b :: xs).idxOf? a = some (n + 1) ↔ b ≠ a ∧ xs.idxOf? a = some n := by
  simp only [idxOf?_cons, beq_iff_eq, ne_eq]
  split <;> (simp; grind)

end ListIdxOf

namespace EffectSSA.ProofSketch
open Lean Meta Simp

/-!
## `Pattern` `getElem` Reduction

Simproc that reduces `(P : Pattern _ _)[k]` to a spelled-out chain of
`List.cons` / `InstSeq.cons` applications, whenever the index `k` is a concrete
natural number literal and the reduction succeeds under default transparency.
-/
section PatternGetElem

/--
Assuming that `e` is already in whnf, recursively reduce the rest of the spine
of the list (leaving each `cons`-head untouched).

`u` has to be be such that `e` is of type `List α` for some `α : Type u`;
this is passed in rather than re-computed since it remains constant for the
whole list.
-/
private meta partial def reduceInstSeqSpine (u : Level) (e : Expr) : MetaM Expr := do
  match_expr e with
  | List.cons α head tail =>
      let tail ← whnf tail
      let tail ← reduceInstSeqSpine u tail
      return mkApp3 (mkConst ``List.cons [u]) α head tail
  | _ => return e

/--
`dsimp`-procedure that rewrites `(P : Pattern _ _)[k]` — with `k` a concrete
`Nat` literal — into a spelled-out chain of `List.cons` / `InstSeq.cons`
applications, using default transparency.

If the initial reduction does not produce a `List.cons` or `List.nil`, the
expression is left untouched.  When it succeeds, the rest of the sequence is
reduced recursively, but each individual instruction (the `cons`-heads) is
left as-is.
-/
dsimproc reducePatternGetElem
    (@GetElem.getElem (EffectSSA.ProofSketch.Pattern _ _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ _ idx _ ← e | return .continue
  let some _ ← getNatValue? idx | return .continue
  let e ← withDefault <| whnf e
  match_expr e with
  | List.cons α _ _ =>
      let u ← getDecLevel α
      let e ← withDefault <| reduceInstSeqSpine u e
      return .done <| e
  | List.nil _ => return .done e
  | _ => return .continue

end PatternGetElem

/-!
## `MultiContext.Complete` of `InstSeq.toContext`

Simproc that matches `(InstSeq.toContext xs is).Complete`, whenever `xs`
is a list literal (as recognised by `getListLit?`),
and rewrites the goal along `InstSeq.complete_toContext_iff`.
The resulting `List.Pairwise (· ≠ ·) xs` and `∀ x ∈ xs, ∃ i ∈ is, i.results = x`
conjuncts are then simplified into the concrete conjunctions of dis-equalities
and per-element `∃`-goals.
-/
section CompleteToContext

/--
Combine two iff-shaped steps with `and_congr`, collapsing any `True`
conjunct via `true_and` / `and_true` so the resulting expression is free
of trivial `True`s.

Given `hl : L ↔ l` and `hr : R ↔ r`, returns `(t, h : L ∧ R ↔ t)` where
`t` is `l ∧ r` (or one of the two, or `True`, if either side is `True`).
-/
private meta def andCongrCollapseTrue
    (l r : Expr) (hl hr : Expr) : MetaM (Expr × Expr) := do
  let step ← mkAppM ``and_congr #[hl, hr]
  if l.isConstOf ``True && r.isConstOf ``True then
    let simp ← mkAppM ``Iff.of_eq #[← mkAppM ``and_true #[mkConst ``True]]
    return (mkConst ``True, ← mkAppM ``Iff.trans #[step, simp])
  else if l.isConstOf ``True then
    let simp ← mkAppM ``Iff.of_eq #[← mkAppM ``true_and #[r]]
    return (r, ← mkAppM ``Iff.trans #[step, simp])
  else if r.isConstOf ``True then
    let simp ← mkAppM ``Iff.of_eq #[← mkAppM ``and_true #[l]]
    return (l, ← mkAppM ``Iff.trans #[step, simp])
  else
    return (mkApp2 (mkConst ``And) l r, step)

/--
Given element type `α`, predicate `φ : α → Prop`, and elements
`[e₀, …, eₙ₋₁]`, produce `(t, h)` where:
* `t` is the right-nested conjunction of the `φ eᵢ`
  (or `True` when the list is empty),
* `h : (∀ x ∈ [e₀, …, eₙ₋₁], φ x) ↔ t`.
-/
private meta partial def buildForallMemIff
    (α φ : Expr) : List Expr → MetaM (Expr × Expr)
  | [] => do
    let prf ← mkAppOptM ``List.forall_mem_nil #[some α, some φ]
    return (mkConst ``True, ← mkAppM ``iff_true_intro #[prf])
  | [e] => do
    let iff ← mkAppOptM ``List.forall_mem_singleton #[some α, some φ, some e]
    return (φ.beta #[e], iff)
  | e :: es => do
    let esLit ← mkListLit α es
    let step ← mkAppOptM ``List.forall_mem_cons
      #[some α, some φ, some e, some esLit]
    let (tgtRest, iffRest) ← buildForallMemIff α φ es
    let φe := φ.beta #[e]
    let (t, andIff) ←
      andCongrCollapseTrue φe tgtRest (← mkAppM ``Iff.refl #[φe]) iffRest
    return (t, ← mkAppM ``Iff.trans #[step, andIff])

/--
Given element type `α`, relation `R : α → α → Prop`, and elements
`[e₀, …, eₙ₋₁]`, produce `(t, h)` where:
* `t` is the conjunction of the `R eᵢ eⱼ` for `i < j` (nested in the shape
  produced by iterating `List.pairwise_cons`; `True` when the list has
  fewer than two elements),
* `h : List.Pairwise R [e₀, …, eₙ₋₁] ↔ t`.
-/
private meta partial def buildPairwiseIff
    (α R : Expr) : List Expr → MetaM (Expr × Expr)
  | [] => do
    let prf ← mkAppOptM ``List.Pairwise.nil #[some α, some R]
    return (mkConst ``True, ← mkAppM ``iff_true_intro #[prf])
  | [e] => do
    let prf ← mkAppM ``List.pairwise_singleton #[R, e]
    return (mkConst ``True, ← mkAppM ``iff_true_intro #[prf])
  | e :: es => do
    let esLit ← mkListLit α es
    let step ← mkAppOptM ``List.pairwise_cons
      #[some α, some R, some e, some esLit]
    -- Head predicate is `R e : α → Prop`. Since `R` is a hard-coded
    -- (partial) constant application, no lambda is introduced.
    let (tgtHead, iffHead) ← buildForallMemIff α (mkApp R e) es
    let (tgtTail, iffTail) ← buildPairwiseIff α R es
    let (t, andIff) ← andCongrCollapseTrue tgtHead tgtTail iffHead iffTail
    return (t, ← mkAppM ``Iff.trans #[step, andIff])

/--
`simp`-procedure that fires on `(InstSeq.toContext xs is).Complete` whenever
`xs` is a concrete list literal.  It applies `InstSeq.complete_toContext_iff`
and then, using the elements returned by `getListLit?`, directly builds the
target expression and a proof term — no nested `simp` call is required.
-/
simproc reduceCompleteToContext
    (MultiContext.Complete (@InstSeq.toContext _ _ sorry _)) := fun e => do
  let_expr MultiContext.Complete _ _ ctx ← e | return .continue
  let ctx ← whnf ctx
  let_expr InstSeq.toContext _ xs _ is ← ctx | return .continue
  let some elts ← getListLit? xs | return .continue
  let elts := elts.toList
  -- Apply the top-level equivalence.
  let iffProof ← mkAppM ``InstSeq.complete_toContext_iff #[xs, is]
  let_expr Iff _ rhs ← ← inferType iffProof | return .continue
  let_expr And rhs₁ rhs₂ ← rhs | return .continue
  -- Recover the element type from the pairwise conjunct.  The relation
  -- there is `fun x1 x2 => x1 ≠ x2` — we hard-code it as `@Ne α` to avoid
  -- carrying an anonymous function into the target.
  let_expr List.Pairwise α _ _ ← rhs₁ | return .continue
  let u ← getLevel α
  let neRel := mkApp (mkConst ``Ne [u]) α
  -- Descend under the `∀ x` binder of the forall-mem conjunct to recover
  -- the predicate `x ↦ ∃ i ∈ is, i.results = x`.
  let existsPred ← withLocalDeclD `x α fun x => do
    let body ← whnf (← Meta.instantiateForall rhs₂ #[x])
    let some (_, φx) := body.arrow? | throwError
      "unexpected shape for forall-mem body:{indentExpr body}"
    mkLambdaFVars #[x] φx
  -- Directly build the pairwise and forall-mem targets and their proofs.
  let (pairTgt, pairIff) ← buildPairwiseIff α neRel elts
  let (existsTgt, existsIff) ← buildForallMemIff α existsPred elts
  let (finalTgt, andIff) ←
    andCongrCollapseTrue pairTgt existsTgt pairIff existsIff
  let combinedIff ← mkAppM ``Iff.trans #[iffProof, andIff]
  let eqProof ← mkAppM ``propext #[combinedIff]
  return .done { expr := finalTgt, proof? := some eqProof }

end CompleteToContext

/-!
## `decide_prec` — Proof Automation for `Pattern.Prec`

Given a concrete pattern `P` (that is, one whose contents reduce under default
transparency to concrete `List` literals of `Inst` structure literals), and
concrete hole indices `k, l`, the `decide_prec` tactic discharges goals of the
form `P.Prec k l` by
1. reducing `P[k]` and `P[l]` to instruction-list literals,
2. searching for a variable appearing both in `P[k].results` and `P[l].args`,
3. applying the `Pattern.Prec.prec` constructor with that variable as witness,
4. discharging the resulting membership subgoals with `simp` (and `grind` as
   a fallback).
-/
section PrecTactic
open Lean Meta Elab Tactic

/--
Reduce an expression `e` of type `InstSeq ι` (under default transparency)
to a concrete list literal `[i₀, i₁, …]`, returning the array of
instruction expressions.
Returns `none` if the reduction does not produce a `List.nil`/`List.cons` chain.
-/
private meta partial def reducePatternToInstList (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← withDefault <| whnf e
  match_expr e with
  | List.nil _ => return some #[]
  | List.cons _ head tail =>
      let some rest ← reducePatternToInstList tail | return none
      return some (#[head] ++ rest)
  | _ => return none

/--
Reduce the given `Inst`-projection (`Inst.results` or `Inst.args`) at
instruction expression `i` to a concrete list literal of `VarId` expressions.
-/
private meta def reduceInstListField (fieldName : Name) (i : Expr) : MetaM (Option (Array Expr)) := do
  let field ← mkAppM fieldName #[i]
  let field ← withDefault <| whnf field
  getListLit? field

/--
Given a list of `Inst`-expressions, concatenate the given field (e.g.
`Inst.results`) across all instructions, returning the resulting flat array
of `VarId` expressions.
-/
private meta def collectInstField (fieldName : Name) (is : Array Expr) :
    MetaM (Option (Array Expr)) := do
  let mut acc : Array Expr := #[]
  for i in is do
    let some vs ← reduceInstListField fieldName i | return none
    acc := acc ++ vs
  return some acc

/--
Find the first `x ∈ xs` that is definitionally equal to some `y ∈ ys`,
returning `some x` (the element from `xs`) or `none` if no such pair exists.
-/
private meta def findDefEqIn (xs ys : Array Expr) : MetaM (Option Expr) := do
  for x in xs do
    for y in ys do
      if ← isDefEq x y then
        return some x
  return none

/--
Build the expression `P[k] : InstSeq ι` using the `Hole n` `GetElem`
instance for `Pattern ι n`.

`mkAppM ``getElem #[P, k, True.intro]` would fail because the `dom` outParam
isn't reduced to `fun _ _ => True` before the last argument is type-checked;
we work around this by providing the domain function explicitly.
-/
private meta def mkPatternHoleGetElem (P k : Expr) : MetaM Expr := do
  let PType ← inferType P
  let_expr Pattern ι n := PType
    | throwError "decide_prec: expected `Pattern _ _`, got:{indentExpr PType}"
  let HoleType := mkApp (mkConst ``Hole) n
  let InstSeqType := mkApp (mkConst ``InstSeq) ι
  let domFn ← withLocalDeclD `_ PType fun x =>
    withLocalDeclD `_ HoleType fun h =>
      mkLambdaFVars #[x, h] (mkConst ``True)
  mkAppOptM ``getElem
    #[some PType, some HoleType, some InstSeqType, some domFn,
      none, some P, some k, some (mkConst ``True.intro)]

/--
`decide_prec` proves goals of the form `P.Prec k l`, where `P` is a concrete
pattern and `k`, `l` are concrete `Hole` indices.

The tactic reduces `P[k]` and `P[l]` under default transparency to concrete
lists of instructions, searches for a variable that appears both in
`P[k].results` and `P[l].args`, and applies the `Pattern.Prec.prec`
constructor with that variable as witness. The resulting membership subgoals
are discharged with `simp` (falling back to `grind`).

NOTE: This only decides instances of `P.Prec k l` which hold in a *single*
step, it does *not* account for the transitivity of `Prec`.
-/
elab "decide_prec" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let tgt ← withDefault <| whnf tgt
  let_expr Pattern.Prec ι n P k l := tgt
    | throwError "decide_prec: expected goal of form `_.Prec _ _`, got:{indentExpr tgt}"
  -- `P[k]`, `P[l]` at type `InstSeq ι` (using the `Hole n` GetElem instance)
  let Pk ← mkPatternHoleGetElem P k
  let Pl ← mkPatternHoleGetElem P l
  let some Pks ← reducePatternToInstList Pk | throwError
    "decide_prec: failed to reduce P[k] to a concrete instruction list:{indentExpr Pk}"
  let some Pls ← reducePatternToInstList Pl | throwError
    "decide_prec: failed to reduce P[l] to a concrete instruction list:{indentExpr Pl}"
  let some rs ← collectInstField ``Inst.results Pks | throwError
    "decide_prec: failed to reduce the `.results` of an instruction in P[k]"
  let some as ← collectInstField ``Inst.args Pls | throwError
    "decide_prec: failed to reduce the `.args` of an instruction in P[l]"
  let some x ← findDefEqIn rs as | throwError
    "decide_prec: no common variable between P[k].results{indentD (MessageData.ofArray <| rs.map MessageData.ofExpr)}\
     \nand P[l].args{indentD (MessageData.ofArray <| as.map MessageData.ofExpr)}"
  -- Build the types of the two membership subgoals.
  let PkResults ← mkAppM ``InstSeq.results #[Pk]
  let PlArgs ← mkAppM ``InstSeq.args #[Pl]
  let memResultsTy ← mkAppM ``Membership.mem #[PkResults, x]
  let memArgsTy ← mkAppM ``Membership.mem #[PlArgs, x]
  let memResultsMVar ← mkFreshExprSyntheticOpaqueMVar memResultsTy `decide_prec.results
  let memArgsMVar ← mkFreshExprSyntheticOpaqueMVar memArgsTy `decide_prec.args
  -- Assemble the proof `Pattern.Prec.prec (x := x) ?_ ?_`.
  let proof := mkAppN (mkConst ``Pattern.Prec.prec)
    #[ι, n, P, k, x, l, memResultsMVar, memArgsMVar]
  goal.assign proof
  setGoals [memResultsMVar.mvarId!, memArgsMVar.mvarId!]
  -- Discharge the two membership subgoals.
  evalTactic <| ← `(tactic| all_goals first | (simp; done) | grind)

end PrecTactic
end EffectSSA.ProofSketch
