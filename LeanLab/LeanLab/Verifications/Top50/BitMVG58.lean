/-
Kernel Goldbach windows MV571 to MV580, width 990000, even n in [888040002, 897940000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV571: every even n in [888040002, 889030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v571 : wem 888038190 888040002 889030000 &&& gm (wpm2 888038190 991810) (P10k.take 278) =
    wem 888038190 888040002 889030000 := by
  decide +kernel

/-- Window MV572: every even n in [889030002, 890020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v572 : wem 889028190 889030002 890020000 &&& gm (wpm2 889028190 991810) (P10k.take 278) =
    wem 889028190 889030002 890020000 := by
  decide +kernel

/-- Window MV573: every even n in [890020002, 891010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v573 : wem 890018190 890020002 891010000 &&& gm (wpm2 890018190 991810) (P10k.take 278) =
    wem 890018190 890020002 891010000 := by
  decide +kernel

/-- Window MV574: every even n in [891010002, 892000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v574 : wem 891008190 891010002 892000000 &&& gm (wpm2 891008190 991810) (P10k.take 278) =
    wem 891008190 891010002 892000000 := by
  decide +kernel

/-- Window MV575: every even n in [892000002, 892990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v575 : wem 891998190 892000002 892990000 &&& gm (wpm2 891998190 991810) (P10k.take 278) =
    wem 891998190 892000002 892990000 := by
  decide +kernel

/-- Window MV576: every even n in [892990002, 893980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v576 : wem 892988190 892990002 893980000 &&& gm (wpm2 892988190 991810) (P10k.take 278) =
    wem 892988190 892990002 893980000 := by
  decide +kernel

/-- Window MV577: every even n in [893980002, 894970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v577 : wem 893978190 893980002 894970000 &&& gm (wpm2 893978190 991810) (P10k.take 278) =
    wem 893978190 893980002 894970000 := by
  decide +kernel

/-- Window MV578: every even n in [894970002, 895960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v578 : wem 894968190 894970002 895960000 &&& gm (wpm2 894968190 991810) (P10k.take 278) =
    wem 894968190 894970002 895960000 := by
  decide +kernel

/-- Window MV579: every even n in [895960002, 896950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v579 : wem 895958190 895960002 896950000 &&& gm (wpm2 895958190 991810) (P10k.take 278) =
    wem 895958190 895960002 896950000 := by
  decide +kernel

/-- Window MV580: every even n in [896950002, 897940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v580 : wem 896948190 896950002 897940000 &&& gm (wpm2 896948190 991810) (P10k.take 278) =
    wem 896948190 896950002 897940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
