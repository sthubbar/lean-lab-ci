/-
Kernel Goldbach windows MV271 to MV280, width 990000, even n in [591040002, 600940000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV271: every even n in [591040002, 592030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v271 : wem 591038190 591040002 592030000 &&& gm (wpm2 591038190 991810) (P10k.take 278) =
    wem 591038190 591040002 592030000 := by
  decide +kernel

/-- Window MV272: every even n in [592030002, 593020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v272 : wem 592028190 592030002 593020000 &&& gm (wpm2 592028190 991810) (P10k.take 278) =
    wem 592028190 592030002 593020000 := by
  decide +kernel

/-- Window MV273: every even n in [593020002, 594010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v273 : wem 593018190 593020002 594010000 &&& gm (wpm2 593018190 991810) (P10k.take 278) =
    wem 593018190 593020002 594010000 := by
  decide +kernel

/-- Window MV274: every even n in [594010002, 595000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v274 : wem 594008190 594010002 595000000 &&& gm (wpm2 594008190 991810) (P10k.take 278) =
    wem 594008190 594010002 595000000 := by
  decide +kernel

/-- Window MV275: every even n in [595000002, 595990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v275 : wem 594998190 595000002 595990000 &&& gm (wpm2 594998190 991810) (P10k.take 278) =
    wem 594998190 595000002 595990000 := by
  decide +kernel

/-- Window MV276: every even n in [595990002, 596980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v276 : wem 595988190 595990002 596980000 &&& gm (wpm2 595988190 991810) (P10k.take 278) =
    wem 595988190 595990002 596980000 := by
  decide +kernel

/-- Window MV277: every even n in [596980002, 597970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v277 : wem 596978190 596980002 597970000 &&& gm (wpm2 596978190 991810) (P10k.take 278) =
    wem 596978190 596980002 597970000 := by
  decide +kernel

/-- Window MV278: every even n in [597970002, 598960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v278 : wem 597968190 597970002 598960000 &&& gm (wpm2 597968190 991810) (P10k.take 278) =
    wem 597968190 597970002 598960000 := by
  decide +kernel

/-- Window MV279: every even n in [598960002, 599950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v279 : wem 598958190 598960002 599950000 &&& gm (wpm2 598958190 991810) (P10k.take 278) =
    wem 598958190 598960002 599950000 := by
  decide +kernel

/-- Window MV280: every even n in [599950002, 600940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v280 : wem 599948190 599950002 600940000 &&& gm (wpm2 599948190 991810) (P10k.take 278) =
    wem 599948190 599950002 600940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
