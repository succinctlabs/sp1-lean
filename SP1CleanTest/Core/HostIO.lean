import SP1Clean.Model.Core.HostIO

/-! # Executable regressions for the native host I/O contract

These exercise observable bytes and rejected calls, including SP1's final-word behavior at the
eight-byte boundary. They do not substitute for syscall AIR grounding or Rust conformance.
-/

namespace SP1CleanTest.Core

open SP1Clean.Model.Core

private def policy : HostMemoryPolicy := ⟨fun _ => false, NativeLayout.guestMemory⟩

private def bytes (length : ℕ) : Bytes :=
  (List.range length).map (fun index => BitVec.ofNat 8 (index + 1))

private def hintCase (length : ℕ) : Bool :=
  let host : HostIO := ⟨[bytes length, [99]], [42]⟩
  let old : ByteMemory := ⟨[(65535, 77), (65536 + 8 * (length / 8 + 1), 88)]⟩
  match host.readHint old policy 65536 length with
  | none => false
  | some (next, memory) =>
      next.hints == [[99]] && next.publicOutput == [42] &&
      memory.readBytes 65536 length == bytes length &&
      memory.readBytes (65536 + length) (8 - length % 8) ==
        List.replicate (8 - length % 8) 0 &&
      memory.read 65535 == 77 && memory.read (65536 + 8 * (length / 8 + 1)) == 88

example : [0, 7, 8, 9].all hintCase = true := by native_decide

example : (HostIO.mk [] []).hintLength = BitVec.allOnes 64 := by native_decide

example : (HostIO.mk [[1, 2], [3]] []).hintLength = 2 := by native_decide

example : (HostIO.mk [] []).readHint ⟨[]⟩ policy 65536 0 = none := by native_decide

example : (HostIO.mk [[1]] []).readHint ⟨[]⟩ policy 65536 2 = none := by native_decide

example : (HostIO.mk [[1]] []).readHint ⟨[]⟩ policy 65537 1 = none := by native_decide

-- Padding alone would overlap the instruction byte, so even an empty hint is rejected.
example : (HostIO.mk [[]] []).readHint ⟨[]⟩
    ⟨fun address => address == 65543, NativeLayout.guestMemory⟩ 65536 0 = none := by native_decide

example : (HostIO.mk [[]] []).readHint ⟨[]⟩ policy (2 ^ 48 - 4) 0 = none := by native_decide

example : ((HostIO.mk [[9]] []).writeHint [1, 2]).hints = [[1, 2], [9]] := by native_decide

example : (((HostIO.mk [] []).writePublic [1, 2]).writePublic [3]).publicOutput = [1, 2, 3] := by
  native_decide

example : (HostIO.mk [[9]] [42]).applyHook ⟨15, [1]⟩ [⟨⟨15, [1]⟩, [[2], [3]]⟩] =
    some (⟨[[2], [3], [9]], [42]⟩, []) := by native_decide

example : (HostIO.mk [] []).applyHook ⟨15, [2]⟩ [⟨⟨15, [1]⟩, [[3]]⟩] = none := by
  native_decide

example : (HostIO.mk [] []).applyHook ⟨16, [1]⟩ [⟨⟨15, [1]⟩, [[3]]⟩] = none := by
  native_decide

end SP1CleanTest.Core
