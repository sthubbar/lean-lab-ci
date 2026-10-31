/-
Kernel Goldbach windows MV221 to MV230, width 990000, even n in [541540002, 551440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV221: every even n in [541540002, 542530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v221 : wem 541538190 541540002 542530000 &&& gm (wpm2 541538190 991810) (P10k.take 278) =
    wem 541538190 541540002 542530000 := by
  decide +kernel

/-- Window MV222: every even n in [542530002, 543520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v222 : wem 542528190 542530002 543520000 &&& gm (wpm2 542528190 991810) (P10k.take 278) =
    wem 542528190 542530002 543520000 := by
  decide +kernel

/-- Window MV223: every even n in [543520002, 544510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v223 : wem 543518190 543520002 544510000 &&& gm (wpm2 543518190 991810) (P10k.take 278) =
    wem 543518190 543520002 544510000 := by
  decide +kernel

/-- Window MV224: every even n in [544510002, 545500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v224 : wem 544508190 544510002 545500000 &&& gm (wpm2 544508190 991810) (P10k.take 278) =
    wem 544508190 544510002 545500000 := by
  decide +kernel

/-- Window MV225: every even n in [545500002, 546490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v225 : wem 545498190 545500002 546490000 &&& gm (wpm2 545498190 991810) (P10k.take 278) =
    wem 545498190 545500002 546490000 := by
  decide +kernel

/-- Window MV226: every even n in [546490002, 547480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v226 : wem 546488190 546490002 547480000 &&& gm (wpm2 546488190 991810) (P10k.take 278) =
    wem 546488190 546490002 547480000 := by
  decide +kernel

/-- Window MV227: every even n in [547480002, 548470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v227 : wem 547478190 547480002 548470000 &&& gm (wpm2 547478190 991810) (P10k.take 278) =
    wem 547478190 547480002 548470000 := by
  decide +kernel

/-- Window MV228: every even n in [548470002, 549460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v228 : wem 548468190 548470002 549460000 &&& gm (wpm2 548468190 991810) (P10k.take 278) =
    wem 548468190 548470002 549460000 := by
  decide +kernel

/-- Window MV229: every even n in [549460002, 550450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v229 : wem 549458190 549460002 550450000 &&& gm (wpm2 549458190 991810) (P10k.take 278) =
    wem 549458190 549460002 550450000 := by
  decide +kernel

/-- Window MV230: every even n in [550450002, 551440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v230 : wem 550448190 550450002 551440000 &&& gm (wpm2 550448190 991810) (P10k.take 278) =
    wem 550448190 550450002 551440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
