/-
Kernel Goldbach windows MV121 to MV130, width 990000, even n in [442540002, 452440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV121: every even n in [442540002, 443530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v121 : wem 442538190 442540002 443530000 &&& gm (wpm2 442538190 991810) (P10k.take 278) =
    wem 442538190 442540002 443530000 := by
  decide +kernel

/-- Window MV122: every even n in [443530002, 444520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v122 : wem 443528190 443530002 444520000 &&& gm (wpm2 443528190 991810) (P10k.take 278) =
    wem 443528190 443530002 444520000 := by
  decide +kernel

/-- Window MV123: every even n in [444520002, 445510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v123 : wem 444518190 444520002 445510000 &&& gm (wpm2 444518190 991810) (P10k.take 278) =
    wem 444518190 444520002 445510000 := by
  decide +kernel

/-- Window MV124: every even n in [445510002, 446500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v124 : wem 445508190 445510002 446500000 &&& gm (wpm2 445508190 991810) (P10k.take 278) =
    wem 445508190 445510002 446500000 := by
  decide +kernel

/-- Window MV125: every even n in [446500002, 447490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v125 : wem 446498190 446500002 447490000 &&& gm (wpm2 446498190 991810) (P10k.take 278) =
    wem 446498190 446500002 447490000 := by
  decide +kernel

/-- Window MV126: every even n in [447490002, 448480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v126 : wem 447488190 447490002 448480000 &&& gm (wpm2 447488190 991810) (P10k.take 278) =
    wem 447488190 447490002 448480000 := by
  decide +kernel

/-- Window MV127: every even n in [448480002, 449470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v127 : wem 448478190 448480002 449470000 &&& gm (wpm2 448478190 991810) (P10k.take 278) =
    wem 448478190 448480002 449470000 := by
  decide +kernel

/-- Window MV128: every even n in [449470002, 450460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v128 : wem 449468190 449470002 450460000 &&& gm (wpm2 449468190 991810) (P10k.take 278) =
    wem 449468190 449470002 450460000 := by
  decide +kernel

/-- Window MV129: every even n in [450460002, 451450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v129 : wem 450458190 450460002 451450000 &&& gm (wpm2 450458190 991810) (P10k.take 278) =
    wem 450458190 450460002 451450000 := by
  decide +kernel

/-- Window MV130: every even n in [451450002, 452440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v130 : wem 451448190 451450002 452440000 &&& gm (wpm2 451448190 991810) (P10k.take 278) =
    wem 451448190 451450002 452440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
