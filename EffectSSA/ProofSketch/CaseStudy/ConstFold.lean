module

import EffectSSA.ProofSketch.ProofSketch

namespace EffectSSA.ProofSketch

namespace CaseStudy.ConstFold

inductive OpCode
  /-- `$n` -/
  | const (n : Nat)
  | add
  deriving DecidableEq

instance : SSA OpCode Unit Nat where
  instDenote := {
    denote i _ xs := ((), match i, xs with
      | .const n, [] => [n]
      | .add, [x, y] => [x + y]
      | _, _ => []
    )
  }
