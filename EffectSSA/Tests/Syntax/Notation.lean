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

/-- info: Program.nil : Program ?m.1 -/
#guard_msgs in #check program!()
/-- info: Program.nil : Program ?m.1 -/
#guard_msgs in #check program!{}()
/-- info: Program.nil : Program ?m.1 -/
#guard_msgs in #check program!{x, y, z}()

-- set_option trace.EffectSSA true

/--
info: have this := Instruction.loadI u8 (Var.ofNat 0) ;> (Instruction.storeI u8 (Var.ofNat 1) (Var.ofNat 0) ;> Program.nil);
this : Program TestTy
-/
#guard_msgs in
#check show Program TestTy from program!{p}(
  x := loadI[u8](p);
  storeI[u8](p, x)
)

/--
info: have this := Instruction.split (Var.ofNat 0) ;> Program.nil;
this : Program TestTy
-/
#guard_msgs in
#check show Program TestTy from program!{e}(
  e1, e2 := split(e)
)


/-!
## `#eval` Tests
--------------------------------------------------------------------------------
Now comes the main body of tests, using `#eval`, thus relying on the `Repr`
instance, for increased legibility of the test output.
-/

-- FIXME: the indentation of these test results is wrong:
--        all instructions should start printing on the same line, and there
--        is currently an extra newline at the end that should not be there.

/--
info: program{x_0}(
x_1 := loadI[EffectSSA.Tests.MyDType.u8](x_0)
  x_2 := loadI[EffectSSA.Tests.MyDType.u8](x_0)
  storeI[EffectSSA.Tests.MyDType.u8](x_0, x_2)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{p}(
  x := loadI[u8](p);
  y := loadI[u8](p);
  storeI[u8](p, y)
)


/--
info: program{x_0,x_1}(
storeI[EffectSSA.Tests.MyDType.u8](x_0, x_1)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{p, v}(
  storeI[u8](p, v)
)

-- Test implicit side effect op
/--
info: program{x_0}(
allocI[EffectSSA.Tests.MyDType.u8](x_0)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{p}(
  allocI[u8](p)
)

-- Test explicit side effect op
/--
info: program{x_0,x_1}(
x_2,x_3 := loadE[EffectSSA.Tests.MyDType.u8](x_0, x_1)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{e, p}(
  e', x := loadE[u8](e, p)
)

-- Test complex program
/--
info: program{x_0,x_1}(
allocI[EffectSSA.Tests.MyDType.u8](x_0)
  storeI[EffectSSA.Tests.MyDType.u8](x_0, x_1)
  freeI[EffectSSA.Tests.MyDType.u8](x_0)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{p, x}(
  allocI[u8](p);
  storeI[u8](p, x);
  freeI[u8](p)
)

-- Test effect bookkeeping
/--
info: program{}(
x_0 := createEff
  consumeEff(x_0)
  ⏎
)
-/
#guard_msgs in
#eval show Program TestTy from program!{}(
  e := createEff;
  consumeEff(e)
)

end EffectSSA.Tests
