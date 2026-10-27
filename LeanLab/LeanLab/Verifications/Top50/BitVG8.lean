/-
Kernel Goldbach windows V71 to V80, width 990000, covering even n in [393040002, 402940000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V71: every even n in [393040002, 394030000] is p + q, q among the first 280 primes. -/
theorem window_v71 : wem 393038190 393040002 394030000 &&& gm (wpm2 393038190 991810) (P10k.take 280) =
    wem 393038190 393040002 394030000 := by
  decide +kernel

/-- Window V72: every even n in [394030002, 395020000] is p + q, q among the first 280 primes. -/
theorem window_v72 : wem 394028190 394030002 395020000 &&& gm (wpm2 394028190 991810) (P10k.take 280) =
    wem 394028190 394030002 395020000 := by
  decide +kernel

/-- Window V73: every even n in [395020002, 396010000] is p + q, q among the first 280 primes. -/
theorem window_v73 : wem 395018190 395020002 396010000 &&& gm (wpm2 395018190 991810) (P10k.take 280) =
    wem 395018190 395020002 396010000 := by
  decide +kernel

/-- Window V74: every even n in [396010002, 397000000] is p + q, q among the first 280 primes. -/
theorem window_v74 : wem 396008190 396010002 397000000 &&& gm (wpm2 396008190 991810) (P10k.take 280) =
    wem 396008190 396010002 397000000 := by
  decide +kernel

/-- Window V75: every even n in [397000002, 397990000] is p + q, q among the first 280 primes. -/
theorem window_v75 : wem 396998190 397000002 397990000 &&& gm (wpm2 396998190 991810) (P10k.take 280) =
    wem 396998190 397000002 397990000 := by
  decide +kernel

/-- Window V76: every even n in [397990002, 398980000] is p + q, q among the first 280 primes. -/
theorem window_v76 : wem 397988190 397990002 398980000 &&& gm (wpm2 397988190 991810) (P10k.take 280) =
    wem 397988190 397990002 398980000 := by
  decide +kernel

/-- Window V77: every even n in [398980002, 399970000] is p + q, q among the first 280 primes. -/
theorem window_v77 : wem 398978190 398980002 399970000 &&& gm (wpm2 398978190 991810) (P10k.take 280) =
    wem 398978190 398980002 399970000 := by
  decide +kernel

/-- Window V78: every even n in [399970002, 400960000] is p + q, q among the first 280 primes. -/
theorem window_v78 : wem 399968190 399970002 400960000 &&& gm (wpm2 399968190 991810) (P10k.take 280) =
    wem 399968190 399970002 400960000 := by
  decide +kernel

/-- Window V79: every even n in [400960002, 401950000] is p + q, q among the first 280 primes. -/
theorem window_v79 : wem 400958190 400960002 401950000 &&& gm (wpm2 400958190 991810) (P10k.take 280) =
    wem 400958190 400960002 401950000 := by
  decide +kernel

/-- Window V80: every even n in [401950002, 402940000] is p + q, q among the first 280 primes. -/
theorem window_v80 : wem 401948190 401950002 402940000 &&& gm (wpm2 401948190 991810) (P10k.take 280) =
    wem 401948190 401950002 402940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
