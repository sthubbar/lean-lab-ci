/-
Kernel Goldbach windows MV371 to MV380, width 990000, even n in [690040002, 699940000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV371: every even n in [690040002, 691030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v371 : wem 690038190 690040002 691030000 &&& gm (wpm2 690038190 991810) (P10k.take 278) =
    wem 690038190 690040002 691030000 := by
  decide +kernel

/-- Window MV372: every even n in [691030002, 692020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v372 : wem 691028190 691030002 692020000 &&& gm (wpm2 691028190 991810) (P10k.take 278) =
    wem 691028190 691030002 692020000 := by
  decide +kernel

/-- Window MV373: every even n in [692020002, 693010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v373 : wem 692018190 692020002 693010000 &&& gm (wpm2 692018190 991810) (P10k.take 278) =
    wem 692018190 692020002 693010000 := by
  decide +kernel

/-- Window MV374: every even n in [693010002, 694000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v374 : wem 693008190 693010002 694000000 &&& gm (wpm2 693008190 991810) (P10k.take 278) =
    wem 693008190 693010002 694000000 := by
  decide +kernel

/-- Window MV375: every even n in [694000002, 694990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v375 : wem 693998190 694000002 694990000 &&& gm (wpm2 693998190 991810) (P10k.take 278) =
    wem 693998190 694000002 694990000 := by
  decide +kernel

/-- Window MV376: every even n in [694990002, 695980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v376 : wem 694988190 694990002 695980000 &&& gm (wpm2 694988190 991810) (P10k.take 278) =
    wem 694988190 694990002 695980000 := by
  decide +kernel

/-- Window MV377: every even n in [695980002, 696970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v377 : wem 695978190 695980002 696970000 &&& gm (wpm2 695978190 991810) (P10k.take 278) =
    wem 695978190 695980002 696970000 := by
  decide +kernel

/-- Window MV378: every even n in [696970002, 697960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v378 : wem 696968190 696970002 697960000 &&& gm (wpm2 696968190 991810) (P10k.take 278) =
    wem 696968190 696970002 697960000 := by
  decide +kernel

/-- Window MV379: every even n in [697960002, 698950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v379 : wem 697958190 697960002 698950000 &&& gm (wpm2 697958190 991810) (P10k.take 278) =
    wem 697958190 697960002 698950000 := by
  decide +kernel

/-- Window MV380: every even n in [698950002, 699940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v380 : wem 698948190 698950002 699940000 &&& gm (wpm2 698948190 991810) (P10k.take 278) =
    wem 698948190 698950002 699940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
