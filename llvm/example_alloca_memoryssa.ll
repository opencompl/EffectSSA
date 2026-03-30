MemorySSA for function: example
define void @example(i8 %y) {
entry:
  %p = alloca ptr, align 8
  %q = alloca i8, align 1
; 1 = MemoryDef(liveOnEntry)
  store ptr %q, ptr %p, align 8
; 2 = MemoryDef(1)
  store i8 %y, ptr %q, align 1
; MemoryUse(1)
  %q_prime = load ptr, ptr %p, align 8
; MemoryUse(2)
  %y_prime = load i8, ptr %q_prime, align 1
  ret void
}
