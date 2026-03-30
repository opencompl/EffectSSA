MemorySSA for function: example_no_noalias
define void @example_no_noalias(ptr %p, ptr %q, i8 %y) {
entry:
; 1 = MemoryDef(liveOnEntry)
  store ptr %q, ptr %p, align 8
; 2 = MemoryDef(1)
  store i8 %y, ptr %q, align 1
; MemoryUse(2)
  %q_prime = load ptr, ptr %p, align 8
; MemoryUse(2)
  %y_prime = load i8, ptr %q_prime, align 1
  ret void
}
