/-
Kernel Goldbach windows MV581 to MV590, width 990000, even n in [897940002, 907840000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV581: every even n in [897940002, 898930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v581 : wem 897938190 897940002 898930000 &&& gm (wpm2 897938190 991810) (P10k.take 278) =
    wem 897938190 897940002 898930000 := by
  decide +kernel

/-- Window MV582: every even n in [898930002, 899920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v582 : wem 898928190 898930002 899920000 &&& gm (wpm2 898928190 991810) (P10k.take 278) =
    wem 898928190 898930002 899920000 := by
  decide +kernel

/-- Window MV583: every even n in [899920002, 900910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v583 : wem 899918190 899920002 900910000 &&& gm (wpm2 899918190 991810) (P10k.take 278) =
    wem 899918190 899920002 900910000 := by
  decide +kernel

/-- Window MV584: every even n in [900910002, 901900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v584 : wem 900908190 900910002 901900000 &&& gm (wpm2 900908190 991810) (P10k.take 278) =
    wem 900908190 900910002 901900000 := by
  decide +kernel

/-- Window MV585: every even n in [901900002, 902890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v585 : wem 901898190 901900002 902890000 &&& gm (wpm2 901898190 991810) (P10k.take 278) =
    wem 901898190 901900002 902890000 := by
  decide +kernel

/-- Window MV586: every even n in [902890002, 903880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v586 : wem 902888190 902890002 903880000 &&& gm (wpm2 902888190 991810) (P10k.take 278) =
    wem 902888190 902890002 903880000 := by
  decide +kernel

/-- Window MV587: every even n in [903880002, 904870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v587 : wem 903878190 903880002 904870000 &&& gm (wpm2 903878190 991810) (P10k.take 278) =
    wem 903878190 903880002 904870000 := by
  decide +kernel

/-- Window MV588: every even n in [904870002, 905860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v588 : wem 904868190 904870002 905860000 &&& gm (wpm2 904868190 991810) (P10k.take 278) =
    wem 904868190 904870002 905860000 := by
  decide +kernel

/-- Window MV589: every even n in [905860002, 906850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v589 : wem 905858190 905860002 906850000 &&& gm (wpm2 905858190 991810) (P10k.take 278) =
    wem 905858190 905860002 906850000 := by
  decide +kernel

/-- Window MV590: every even n in [906850002, 907840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v590 : wem 906848190 906850002 907840000 &&& gm (wpm2 906848190 991810) (P10k.take 278) =
    wem 906848190 906850002 907840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
