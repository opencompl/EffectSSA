; Example with noalias pointers to demonstrate MemorySSA
define void @example(ptr noalias %p, ptr noalias %q, i8 %y) {
entry:
  store ptr %q, ptr %p
  store i8 %y, ptr %q
  %q_prime = load ptr, ptr %p
  %y_prime = load i8, ptr %q_prime
  ret void
}
