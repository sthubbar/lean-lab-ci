/-
Kernel Goldbach windows V81 to V90, width 990000, covering even n in [402940002, 412840000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V81: every even n in [402940002, 403930000] is p + q, q among the first 280 primes. -/
theorem window_v81 : wem 402938190 402940002 403930000 &&& gm (wpm2 402938190 991810) (P10k.take 280) =
    wem 402938190 402940002 403930000 := by
  decide +kernel

/-- Window V82: every even n in [403930002, 404920000] is p + q, q among the first 280 primes. -/
theorem window_v82 : wem 403928190 403930002 404920000 &&& gm (wpm2 403928190 991810) (P10k.take 280) =
    wem 403928190 403930002 404920000 := by
  decide +kernel

/-- Window V83: every even n in [404920002, 405910000] is p + q, q among the first 280 primes. -/
theorem window_v83 : wem 404918190 404920002 405910000 &&& gm (wpm2 404918190 991810) (P10k.take 280) =
    wem 404918190 404920002 405910000 := by
  decide +kernel

/-- Window V84: every even n in [405910002, 406900000] is p + q, q among the first 280 primes. -/
theorem window_v84 : wem 405908190 405910002 406900000 &&& gm (wpm2 405908190 991810) (P10k.take 280) =
    wem 405908190 405910002 406900000 := by
  decide +kernel

/-- Window V85: every even n in [406900002, 407890000] is p + q, q among the first 280 primes. -/
theorem window_v85 : wem 406898190 406900002 407890000 &&& gm (wpm2 406898190 991810) (P10k.take 280) =
    wem 406898190 406900002 407890000 := by
  decide +kernel

/-- Window V86: every even n in [407890002, 408880000] is p + q, q among the first 280 primes. -/
theorem window_v86 : wem 407888190 407890002 408880000 &&& gm (wpm2 407888190 991810) (P10k.take 280) =
    wem 407888190 407890002 408880000 := by
  decide +kernel

/-- Window V87: every even n in [408880002, 409870000] is p + q, q among the first 280 primes. -/
theorem window_v87 : wem 408878190 408880002 409870000 &&& gm (wpm2 408878190 991810) (P10k.take 280) =
    wem 408878190 408880002 409870000 := by
  decide +kernel

/-- Window V88: every even n in [409870002, 410860000] is p + q, q among the first 280 primes. -/
theorem window_v88 : wem 409868190 409870002 410860000 &&& gm (wpm2 409868190 991810) (P10k.take 280) =
    wem 409868190 409870002 410860000 := by
  decide +kernel

/-- Window V89: every even n in [410860002, 411850000] is p + q, q among the first 280 primes. -/
theorem window_v89 : wem 410858190 410860002 411850000 &&& gm (wpm2 410858190 991810) (P10k.take 280) =
    wem 410858190 410860002 411850000 := by
  decide +kernel

/-- Window V90: every even n in [411850002, 412840000] is p + q, q among the first 280 primes. -/
theorem window_v90 : wem 411848190 411850002 412840000 &&& gm (wpm2 411848190 991810) (P10k.take 280) =
    wem 411848190 411850002 412840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
