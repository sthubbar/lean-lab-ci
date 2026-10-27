/-
Kernel Goldbach windows MU51 to MU60, width 990000, even n in [50500002, 60400000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU51: every even n in [50500002, 51490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u51 : wem 50498190 50500002 51490000 &&& gm (wpm2 50498190 991810) (P10k.take 278) =
    wem 50498190 50500002 51490000 := by
  decide +kernel

/-- Window MU52: every even n in [51490002, 52480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u52 : wem 51488190 51490002 52480000 &&& gm (wpm2 51488190 991810) (P10k.take 278) =
    wem 51488190 51490002 52480000 := by
  decide +kernel

/-- Window MU53: every even n in [52480002, 53470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u53 : wem 52478190 52480002 53470000 &&& gm (wpm2 52478190 991810) (P10k.take 278) =
    wem 52478190 52480002 53470000 := by
  decide +kernel

/-- Window MU54: every even n in [53470002, 54460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u54 : wem 53468190 53470002 54460000 &&& gm (wpm2 53468190 991810) (P10k.take 278) =
    wem 53468190 53470002 54460000 := by
  decide +kernel

/-- Window MU55: every even n in [54460002, 55450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u55 : wem 54458190 54460002 55450000 &&& gm (wpm2 54458190 991810) (P10k.take 278) =
    wem 54458190 54460002 55450000 := by
  decide +kernel

/-- Window MU56: every even n in [55450002, 56440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u56 : wem 55448190 55450002 56440000 &&& gm (wpm2 55448190 991810) (P10k.take 278) =
    wem 55448190 55450002 56440000 := by
  decide +kernel

/-- Window MU57: every even n in [56440002, 57430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u57 : wem 56438190 56440002 57430000 &&& gm (wpm2 56438190 991810) (P10k.take 278) =
    wem 56438190 56440002 57430000 := by
  decide +kernel

/-- Window MU58: every even n in [57430002, 58420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u58 : wem 57428190 57430002 58420000 &&& gm (wpm2 57428190 991810) (P10k.take 278) =
    wem 57428190 57430002 58420000 := by
  decide +kernel

/-- Window MU59: every even n in [58420002, 59410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u59 : wem 58418190 58420002 59410000 &&& gm (wpm2 58418190 991810) (P10k.take 278) =
    wem 58418190 58420002 59410000 := by
  decide +kernel

/-- Window MU60: every even n in [59410002, 60400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u60 : wem 59408190 59410002 60400000 &&& gm (wpm2 59408190 991810) (P10k.take 278) =
    wem 59408190 59410002 60400000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
