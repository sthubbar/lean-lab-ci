/-
Kernel Goldbach windows MV81 to MV90, width 990000, even n in [402940002, 412840000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV81: every even n in [402940002, 403930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v81 : wem 402938190 402940002 403930000 &&& gm (wpm2 402938190 991810) (P10k.take 278) =
    wem 402938190 402940002 403930000 := by
  decide +kernel

/-- Window MV82: every even n in [403930002, 404920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v82 : wem 403928190 403930002 404920000 &&& gm (wpm2 403928190 991810) (P10k.take 278) =
    wem 403928190 403930002 404920000 := by
  decide +kernel

/-- Window MV83: every even n in [404920002, 405910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v83 : wem 404918190 404920002 405910000 &&& gm (wpm2 404918190 991810) (P10k.take 278) =
    wem 404918190 404920002 405910000 := by
  decide +kernel

/-- Window MV84: every even n in [405910002, 406900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v84 : wem 405908190 405910002 406900000 &&& gm (wpm2 405908190 991810) (P10k.take 278) =
    wem 405908190 405910002 406900000 := by
  decide +kernel

/-- Window MV85: every even n in [406900002, 407890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v85 : wem 406898190 406900002 407890000 &&& gm (wpm2 406898190 991810) (P10k.take 278) =
    wem 406898190 406900002 407890000 := by
  decide +kernel

/-- Window MV86: every even n in [407890002, 408880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v86 : wem 407888190 407890002 408880000 &&& gm (wpm2 407888190 991810) (P10k.take 278) =
    wem 407888190 407890002 408880000 := by
  decide +kernel

/-- Window MV87: every even n in [408880002, 409870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v87 : wem 408878190 408880002 409870000 &&& gm (wpm2 408878190 991810) (P10k.take 278) =
    wem 408878190 408880002 409870000 := by
  decide +kernel

/-- Window MV88: every even n in [409870002, 410860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v88 : wem 409868190 409870002 410860000 &&& gm (wpm2 409868190 991810) (P10k.take 278) =
    wem 409868190 409870002 410860000 := by
  decide +kernel

/-- Window MV89: every even n in [410860002, 411850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v89 : wem 410858190 410860002 411850000 &&& gm (wpm2 410858190 991810) (P10k.take 278) =
    wem 410858190 410860002 411850000 := by
  decide +kernel

/-- Window MV90: every even n in [411850002, 412840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v90 : wem 411848190 411850002 412840000 &&& gm (wpm2 411848190 991810) (P10k.take 278) =
    wem 411848190 411850002 412840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
