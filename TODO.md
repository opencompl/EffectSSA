
# Todo

- [X] Formalize lawfulness requirements (Assumptions/LawfulMemoryModel.lean)
  - [x] Write `Trace.events` (Trace/Defs.lean)
  - Note that these turned out to be quite different from how I wrote them down
    in the draft, because I'm phrasing things in terms of single event
    compatibility!

- [X] Define semantics
  - [X] load/store operations
  - [X] merge/split operations

- [X] Define syntax
  - [X] Basic syntax setup
    - Note: I would like to do *extrinsic* typing, rather than the intrinsically
      well-typed thing we did in Lean-MLIR. However, I *did* choose to intrinsically
      track a bound on the DeBruijn index, meaning my program still is not just a
      list. It remains to be seen if that was the right choice, or whether I should
      just use plain `Nat`s for variables.
  - [X] Custom embedded program syntax
    - [X] Initial notation elaboration setup
    - [X] Fix the issue with variable counts not being propagated properly
    - [X] Print the syntax
    - [X] Have at least some test cases
    - [X] Refactor the printer to print correct variable names

- [X] Type system
  - For now, I just have a `WellTyped` predicate. We could expand this to
    an intrinsically well-typed type of programs `TProgram`, but I'm not yet
    sure if we want to do so

- [X] Figure out how to compose the semantics functions into semantics of a particular program
  - [X] On the whiteboard
  - [X] Rough outline the markdown draft
  - [X] In Lean  
  - [ ] Write this idiomatically in the markdown draft

- [ ] Define a notion of program equivalence
  - [ ] First, define an equivalence on traces
    - This could be useful in the phrasing of compatibility also
  - [ ] Equivalence on *closed* programs `P` and `Q`
    - This will be defined as `P.exec` and `Q.exec` with an empty environment
      and trace returns *equivalent* results (referring to trace equivalence)
  - [ ] Equivalence on programs with free variables
    - I'm leaning towards a contextual equivalence, although a straightforward
      quantification will be easier to implement. I have an intuition that
      quantification will be a problem, since I remember it being a problem in
      LeanMLIR, but I can't remember exactly what that problem is (and if it
      might not be an issue now that we've abstracted away from LLVM's provenance)
    - On second thought: my understanding of contextual equivalence does not cleanly
      translate to a compositional semantics with environments (as opposed to
      operational semantics), so having program fragments with designated "return"
      variables is likely the way to go.
      - These approaches might not be as mutually exclusive as I originally thought:
          perhaps such program fragments might lead to a natural notion of a program
          context, and thus contextual equivalence after all!
      - However, contextual equivalence as I originally wrote in the draft is
          not likely viable.

## Bonus Objectives

- [ ] Prove equivalence between the `LawfulMemoryModel` as formalized in Lean
        and the lawfulness assumptions as written in the draft
