; obtained via nix-shell -p llvm --run "opt -passes='print<memoryssa>' -disable-output example.ll 2>&1" > example_memoryssa.ll

MemorySSA for function: example
define void @example(ptr noalias %p, ptr noalias %q, i8 %y) {
entry:
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
