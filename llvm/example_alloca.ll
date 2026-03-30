; Example with alloca to demonstrate MemorySSA
define void @example(i8 %y) {
entry:
  %p = alloca ptr
  %q = alloca i8
  store ptr %q, ptr %p
  store i8 %y, ptr %q
  %q_prime = load ptr, ptr %p
  %y_prime = load i8, ptr %q_prime
  ret void
}
