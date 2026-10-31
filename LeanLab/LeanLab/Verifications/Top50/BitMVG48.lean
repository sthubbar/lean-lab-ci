/-
Kernel Goldbach windows MV471 to MV480, width 990000, even n in [789040002, 798940000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV471: every even n in [789040002, 790030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v471 : wem 789038190 789040002 790030000 &&& gm (wpm2 789038190 991810) (P10k.take 278) =
    wem 789038190 789040002 790030000 := by
  decide +kernel

/-- Window MV472: every even n in [790030002, 791020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v472 : wem 790028190 790030002 791020000 &&& gm (wpm2 790028190 991810) (P10k.take 278) =
    wem 790028190 790030002 791020000 := by
  decide +kernel

/-- Window MV473: every even n in [791020002, 792010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v473 : wem 791018190 791020002 792010000 &&& gm (wpm2 791018190 991810) (P10k.take 278) =
    wem 791018190 791020002 792010000 := by
  decide +kernel

/-- Window MV474: every even n in [792010002, 793000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v474 : wem 792008190 792010002 793000000 &&& gm (wpm2 792008190 991810) (P10k.take 278) =
    wem 792008190 792010002 793000000 := by
  decide +kernel

/-- Window MV475: every even n in [793000002, 793990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v475 : wem 792998190 793000002 793990000 &&& gm (wpm2 792998190 991810) (P10k.take 278) =
    wem 792998190 793000002 793990000 := by
  decide +kernel

/-- Window MV476: every even n in [793990002, 794980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v476 : wem 793988190 793990002 794980000 &&& gm (wpm2 793988190 991810) (P10k.take 278) =
    wem 793988190 793990002 794980000 := by
  decide +kernel

/-- Window MV477: every even n in [794980002, 795970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v477 : wem 794978190 794980002 795970000 &&& gm (wpm2 794978190 991810) (P10k.take 278) =
    wem 794978190 794980002 795970000 := by
  decide +kernel

/-- Window MV478: every even n in [795970002, 796960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v478 : wem 795968190 795970002 796960000 &&& gm (wpm2 795968190 991810) (P10k.take 278) =
    wem 795968190 795970002 796960000 := by
  decide +kernel

/-- Window MV479: every even n in [796960002, 797950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v479 : wem 796958190 796960002 797950000 &&& gm (wpm2 796958190 991810) (P10k.take 278) =
    wem 796958190 796960002 797950000 := by
  decide +kernel

/-- Window MV480: every even n in [797950002, 798940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v480 : wem 797948190 797950002 798940000 &&& gm (wpm2 797948190 991810) (P10k.take 278) =
    wem 797948190 797950002 798940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
