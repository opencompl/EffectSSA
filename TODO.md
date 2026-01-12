
# Todo

- [X] Formalize lawfulness requirements (Assumptions/LawfulMemoryModel.lean)
  - [x] Write `Trace.events` (Trace/Defs.lean)
  - Note that these turned out to be quite different from how I wrote them down
    in the draft, because I'm phrasing things in terms of single event
    compatibility!

- [ ] Prove equivalence between the `LawfulMemoryModel` as formalized in Lean
        and the lawfulness assumptions as written in the draft

- [ ] Define semantics
  - [ ] load/store operations
  - [ ] merge/split operations

- [ ] Define syntax
  - [X] Basic syntax setup
    - Note: I would like to do *extrinsic* typing, rather than the intrinsically
      well-typed thing we did in Lean-MLIR. However, I *did* choose to intrinsically
      track a bound on the DeBruijn index, meaning my program still is not just a
      list. It remains to be seen if that was the right choice, or whether I should
      just use plain `Nat`s for variables.
  - [X] Type system
    - For now, I just have a `WellTyped` predicate. We could expand this to
      an intrinsically well-typed type of programs `TProgram`, but I'm not yet
      sure if we want to do so
