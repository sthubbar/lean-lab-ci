/-
Kernel Goldbach windows MV421 to MV430, width 990000, even n in [739540002, 749440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV421: every even n in [739540002, 740530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v421 : wem 739538190 739540002 740530000 &&& gm (wpm2 739538190 991810) (P10k.take 278) =
    wem 739538190 739540002 740530000 := by
  decide +kernel

/-- Window MV422: every even n in [740530002, 741520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v422 : wem 740528190 740530002 741520000 &&& gm (wpm2 740528190 991810) (P10k.take 278) =
    wem 740528190 740530002 741520000 := by
  decide +kernel

/-- Window MV423: every even n in [741520002, 742510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v423 : wem 741518190 741520002 742510000 &&& gm (wpm2 741518190 991810) (P10k.take 278) =
    wem 741518190 741520002 742510000 := by
  decide +kernel

/-- Window MV424: every even n in [742510002, 743500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v424 : wem 742508190 742510002 743500000 &&& gm (wpm2 742508190 991810) (P10k.take 278) =
    wem 742508190 742510002 743500000 := by
  decide +kernel

/-- Window MV425: every even n in [743500002, 744490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v425 : wem 743498190 743500002 744490000 &&& gm (wpm2 743498190 991810) (P10k.take 278) =
    wem 743498190 743500002 744490000 := by
  decide +kernel

/-- Window MV426: every even n in [744490002, 745480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v426 : wem 744488190 744490002 745480000 &&& gm (wpm2 744488190 991810) (P10k.take 278) =
    wem 744488190 744490002 745480000 := by
  decide +kernel

/-- Window MV427: every even n in [745480002, 746470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v427 : wem 745478190 745480002 746470000 &&& gm (wpm2 745478190 991810) (P10k.take 278) =
    wem 745478190 745480002 746470000 := by
  decide +kernel

/-- Window MV428: every even n in [746470002, 747460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v428 : wem 746468190 746470002 747460000 &&& gm (wpm2 746468190 991810) (P10k.take 278) =
    wem 746468190 746470002 747460000 := by
  decide +kernel

/-- Window MV429: every even n in [747460002, 748450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v429 : wem 747458190 747460002 748450000 &&& gm (wpm2 747458190 991810) (P10k.take 278) =
    wem 747458190 747460002 748450000 := by
  decide +kernel

/-- Window MV430: every even n in [748450002, 749440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v430 : wem 748448190 748450002 749440000 &&& gm (wpm2 748448190 991810) (P10k.take 278) =
    wem 748448190 748450002 749440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
