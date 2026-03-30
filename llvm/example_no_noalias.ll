; Same example without noalias annotations
define void @example_no_noalias(ptr %p, ptr %q, i8 %y) {
entry:
  store ptr %q, ptr %p
  store i8 %y, ptr %q
  %q_prime = load ptr, ptr %p
  %y_prime = load i8, ptr %q_prime
  ret void
}
