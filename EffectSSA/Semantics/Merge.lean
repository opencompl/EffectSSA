import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Trace.Compat

/-!
# Merge Semantics

This file defines the semantics for the `merge` operation.
This operation reconciles previously split traces back into a single trace,
such that all events become linearly ordered.
-/
namespace EffectSSA
namespace Semantics
variable {τ : Ty} [MemoryModel τ]

/--
Identifies the most recent `.split` event in a trace `es`.
Returns `some (new_events, old_history)` where:
* `new_events` are the events that occurred *after* the most recent split.
* `old_history` are the events that occurred *before* the most recent split.

Note that the `.split` event itself is excluded from both lists.
Returns `none` if no `.split` event is found, and when the trace is `.ub`.
-/
def findSplit : Trace τ → Option (Trace τ × Trace τ)
  | .ub => none
  | .seq es => go es
where
  go : List (Event τ) → Option (Trace τ × Trace τ)
  | [] => none
  | .split :: es => some (.seq [], es)
  | e :: es =>
    (go es).map fun (pre, post) => (e :> pre, post)

/--
The `merge` semantics reconciles two divergent traces `es` and `ds` into a single linear order.
It succeeds if and only if:
1. Both traces contain a `.split` event (checked via `findSplit`).
2. Both traces share the exact same history prior to the split.
3. The new events in both traces (since the split) are compatible (`es_new ⌣ ds_new`).

If successful, the result is `es_new ++ ds_new ++ shared_history`.
Otherwise, returns `.ub`.
-/
def merge (es ds : Trace τ) : Trace τ := Id.run do
  let some (es_new, es_old) := findSplit es | return .ub
  let some (ds_new, ds_old) := findSplit ds | return .ub

  if es_old = ds_old ∧ es_new ⌣ ds_new then
    es_new ++ ds_new ++ es_old
  else
    .ub
