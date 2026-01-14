import EffectSSA.Syntax

namespace EffectSSA.Tests

/-!
## Setup
--------------------------------------------------------------------------------
-/

inductive MyDType
  | u8
  deriving DecidableEq, Repr
open MyDType

def TestTy : Ty := { DType := MyDType }

/-!
## `#check` Tests
--------------------------------------------------------------------------------
At first, we have a few tests using `#check`, to have a baseline check for the
parser in isolation from the printing code.
-/

/-- info: Program.nil : Program ?m.1 0 -/
#guard_msgs in #check program!()
/-- info: Program.nil : Program ?m.1 0 -/
#guard_msgs in #check program!{}()
/-- info: Program.nil : Program ?m.1 3 -/
#guard_msgs in #check program!{x, y, z}()

-- set_option trace.EffectSSA true

/--
info: have this :=
  Program.cons (Instruction.loadI u8 (Var.ofFin 0)) (Program.cons (Instruction.loadI u8 (Var.ofFin 1)) Program.nil);
this : Program TestTy 1
-/
#guard_msgs in
#check show Program TestTy _ from program!{p}(
  x := loadI[u8](p);
  y := loadI[u8](p)
)

/--
info: have this := Program.cons (Instruction.split (Var.ofFin 0)) Program.nil;
this : Program TestTy 1
-/
#guard_msgs in
#check show Program TestTy _ from program!{e}(
  e1, e2 := split(e)
)


/-!
## `#eval` Tests
--------------------------------------------------------------------------------
Now comes the main body of tests, using `#eval`, thus relying on the `Repr`
instance, for increased legibility of the test output.
-/

/--
info: program{x_0}(
x_0 := loadI[EffectSSA.Tests.MyDType.u8](x_0)
 x_0 := loadI[EffectSSA.Tests.MyDType.u8](x_1)
 ⏎
)
-/
#guard_msgs in
#eval show Program TestTy _ from program!{p}(
  x := loadI[u8](p);
  y := loadI[u8](p)
)

#exit

/--
info: ["storeI EffectSSA.Tests.u8 0 1"]
-/
#guard_msgs in
#eval show Program TestTy 2 from program! [p, v] (
  storeI[u8](p, v)
)

-- Test implicit side effect op
/--
info: ["allocI EffectSSA.Tests.u8 0"]
-/
#guard_msgs in
#eval show Program TestTy 1 from program! [p] (
  x := allocI[u8](p)
)

-- Test explicit side effect op
/--
info: ["loadE EffectSSA.Tests.u8 0 1"]
-/
#guard_msgs in
#eval show Program TestTy 2 from program! [e, p] (
  e', x := loadE[u8](e, p)
)

-- Test complex program
/--
info: ["allocI EffectSSA.Tests.u8 0", "storeI EffectSSA.Tests.u8 0 1", "freeI EffectSSA.Tests.u8 0"]
-/
#guard_msgs in
#eval show Program TestTy 1 from program! [p] (
  x := allocI[u8](p);
  storeI[u8](p, x);
  freeI[u8](p)
)

-- Test effect bookkeeping
/--
info: ["createEff", "consumeEff 0"]
-/
#guard_msgs in
#eval show Program TestTy 0 from program! [] (
  e := createEff;
  consumeEff(e)
)

end EffectSSA.Tests
