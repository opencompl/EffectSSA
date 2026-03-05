
structure NonZeroNat where
  raw : Nat
  h : raw ≠ 0 := by grind

namespace NonZeroNat

instance : OfNat NonZeroNat (n + 1) where
  ofNat := { raw := n + 1 }

@[simp, grind =] theorem raw_ofNat (m : Nat) : raw (OfNat.ofNat (m + 1)) = m + 1 := by rfl

@[ext, grind ext] theorem ext {n m : NonZeroNat} (h : n.raw = m.raw) : n = m := by
  cases n; cases m; grind

/-- info: NonZeroNat.ext_iff {n m : NonZeroNat} : n = m ↔ n.raw = m.raw -/
#guard_msgs in #check NonZeroNat.ext_iff

attribute [simp, grind =_] NonZeroNat.ext_iff
-- -------------------^^^
-- I would like this to be just `grind =`, to make the rewrite work the same in
-- `grind` as in `simp`, but that gives the following error:
-- ```
--   invalid pattern, (non-forbidden) application expected
--     #1
-- ```

@[simp]
theorem eq_one_iff : (1 : NonZeroNat) ≠ 2 := by
  simp; grind
  -- ^^ This proof does not go through with just `grind`
