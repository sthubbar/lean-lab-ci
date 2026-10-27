/-
Kernel Goldbach windows MV381 to MV390, width 990000, even n in [699940002, 709840000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV381: every even n in [699940002, 700930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v381 : wem 699938190 699940002 700930000 &&& gm (wpm2 699938190 991810) (P10k.take 278) =
    wem 699938190 699940002 700930000 := by
  decide +kernel

/-- Window MV382: every even n in [700930002, 701920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v382 : wem 700928190 700930002 701920000 &&& gm (wpm2 700928190 991810) (P10k.take 278) =
    wem 700928190 700930002 701920000 := by
  decide +kernel

/-- Window MV383: every even n in [701920002, 702910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v383 : wem 701918190 701920002 702910000 &&& gm (wpm2 701918190 991810) (P10k.take 278) =
    wem 701918190 701920002 702910000 := by
  decide +kernel

/-- Window MV384: every even n in [702910002, 703900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v384 : wem 702908190 702910002 703900000 &&& gm (wpm2 702908190 991810) (P10k.take 278) =
    wem 702908190 702910002 703900000 := by
  decide +kernel

/-- Window MV385: every even n in [703900002, 704890000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v385 : wem 703898190 703900002 704890000 &&& gm (wpm2 703898190 991810) (P10k.take 278) =
    wem 703898190 703900002 704890000 := by
  decide +kernel

/-- Window MV386: every even n in [704890002, 705880000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v386 : wem 704888190 704890002 705880000 &&& gm (wpm2 704888190 991810) (P10k.take 278) =
    wem 704888190 704890002 705880000 := by
  decide +kernel

/-- Window MV387: every even n in [705880002, 706870000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v387 : wem 705878190 705880002 706870000 &&& gm (wpm2 705878190 991810) (P10k.take 278) =
    wem 705878190 705880002 706870000 := by
  decide +kernel

/-- Window MV388: every even n in [706870002, 707860000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v388 : wem 706868190 706870002 707860000 &&& gm (wpm2 706868190 991810) (P10k.take 278) =
    wem 706868190 706870002 707860000 := by
  decide +kernel

/-- Window MV389: every even n in [707860002, 708850000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v389 : wem 707858190 707860002 708850000 &&& gm (wpm2 707858190 991810) (P10k.take 278) =
    wem 707858190 707860002 708850000 := by
  decide +kernel

/-- Window MV390: every even n in [708850002, 709840000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v390 : wem 708848190 708850002 709840000 &&& gm (wpm2 708848190 991810) (P10k.take 278) =
    wem 708848190 708850002 709840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
