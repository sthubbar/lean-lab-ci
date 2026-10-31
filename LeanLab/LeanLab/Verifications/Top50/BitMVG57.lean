/-
Kernel Goldbach windows MV561 to MV570, width 990000, even n in [878140002, 888040000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV561: every even n in [878140002, 879130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v561 : wem 878138190 878140002 879130000 &&& gm (wpm2 878138190 991810) (P10k.take 278) =
    wem 878138190 878140002 879130000 := by
  decide +kernel

/-- Window MV562: every even n in [879130002, 880120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v562 : wem 879128190 879130002 880120000 &&& gm (wpm2 879128190 991810) (P10k.take 278) =
    wem 879128190 879130002 880120000 := by
  decide +kernel

/-- Window MV563: every even n in [880120002, 881110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v563 : wem 880118190 880120002 881110000 &&& gm (wpm2 880118190 991810) (P10k.take 278) =
    wem 880118190 880120002 881110000 := by
  decide +kernel

/-- Window MV564: every even n in [881110002, 882100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v564 : wem 881108190 881110002 882100000 &&& gm (wpm2 881108190 991810) (P10k.take 278) =
    wem 881108190 881110002 882100000 := by
  decide +kernel

/-- Window MV565: every even n in [882100002, 883090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v565 : wem 882098190 882100002 883090000 &&& gm (wpm2 882098190 991810) (P10k.take 278) =
    wem 882098190 882100002 883090000 := by
  decide +kernel

/-- Window MV566: every even n in [883090002, 884080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v566 : wem 883088190 883090002 884080000 &&& gm (wpm2 883088190 991810) (P10k.take 278) =
    wem 883088190 883090002 884080000 := by
  decide +kernel

/-- Window MV567: every even n in [884080002, 885070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v567 : wem 884078190 884080002 885070000 &&& gm (wpm2 884078190 991810) (P10k.take 278) =
    wem 884078190 884080002 885070000 := by
  decide +kernel

/-- Window MV568: every even n in [885070002, 886060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v568 : wem 885068190 885070002 886060000 &&& gm (wpm2 885068190 991810) (P10k.take 278) =
    wem 885068190 885070002 886060000 := by
  decide +kernel

/-- Window MV569: every even n in [886060002, 887050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v569 : wem 886058190 886060002 887050000 &&& gm (wpm2 886058190 991810) (P10k.take 278) =
    wem 886058190 886060002 887050000 := by
  decide +kernel

/-- Window MV570: every even n in [887050002, 888040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v570 : wem 887048190 887050002 888040000 &&& gm (wpm2 887048190 991810) (P10k.take 278) =
    wem 887048190 887050002 888040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
