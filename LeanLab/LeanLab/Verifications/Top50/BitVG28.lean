/-
Kernel Goldbach windows V271 to V280, width 990000, covering even n in [591040002, 600940000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V271: every even n in [591040002, 592030000] is p + q, q among the first 280 primes. -/
theorem window_v271 : wem 591038190 591040002 592030000 &&& gm (wpm2 591038190 991810) (P10k.take 280) =
    wem 591038190 591040002 592030000 := by
  decide +kernel

/-- Window V272: every even n in [592030002, 593020000] is p + q, q among the first 280 primes. -/
theorem window_v272 : wem 592028190 592030002 593020000 &&& gm (wpm2 592028190 991810) (P10k.take 280) =
    wem 592028190 592030002 593020000 := by
  decide +kernel

/-- Window V273: every even n in [593020002, 594010000] is p + q, q among the first 280 primes. -/
theorem window_v273 : wem 593018190 593020002 594010000 &&& gm (wpm2 593018190 991810) (P10k.take 280) =
    wem 593018190 593020002 594010000 := by
  decide +kernel

/-- Window V274: every even n in [594010002, 595000000] is p + q, q among the first 280 primes. -/
theorem window_v274 : wem 594008190 594010002 595000000 &&& gm (wpm2 594008190 991810) (P10k.take 280) =
    wem 594008190 594010002 595000000 := by
  decide +kernel

/-- Window V275: every even n in [595000002, 595990000] is p + q, q among the first 280 primes. -/
theorem window_v275 : wem 594998190 595000002 595990000 &&& gm (wpm2 594998190 991810) (P10k.take 280) =
    wem 594998190 595000002 595990000 := by
  decide +kernel

/-- Window V276: every even n in [595990002, 596980000] is p + q, q among the first 280 primes. -/
theorem window_v276 : wem 595988190 595990002 596980000 &&& gm (wpm2 595988190 991810) (P10k.take 280) =
    wem 595988190 595990002 596980000 := by
  decide +kernel

/-- Window V277: every even n in [596980002, 597970000] is p + q, q among the first 280 primes. -/
theorem window_v277 : wem 596978190 596980002 597970000 &&& gm (wpm2 596978190 991810) (P10k.take 280) =
    wem 596978190 596980002 597970000 := by
  decide +kernel

/-- Window V278: every even n in [597970002, 598960000] is p + q, q among the first 280 primes. -/
theorem window_v278 : wem 597968190 597970002 598960000 &&& gm (wpm2 597968190 991810) (P10k.take 280) =
    wem 597968190 597970002 598960000 := by
  decide +kernel

/-- Window V279: every even n in [598960002, 599950000] is p + q, q among the first 280 primes. -/
theorem window_v279 : wem 598958190 598960002 599950000 &&& gm (wpm2 598958190 991810) (P10k.take 280) =
    wem 598958190 598960002 599950000 := by
  decide +kernel

/-- Window V280: every even n in [599950002, 600940000] is p + q, q among the first 280 primes. -/
theorem window_v280 : wem 599948190 599950002 600940000 &&& gm (wpm2 599948190 991810) (P10k.take 280) =
    wem 599948190 599950002 600940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
