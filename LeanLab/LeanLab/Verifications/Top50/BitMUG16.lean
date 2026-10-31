/-
Kernel Goldbach windows MU151 to MU160, width 990000, even n in [149500002, 159400000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU151: every even n in [149500002, 150490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u151 : wem 149498190 149500002 150490000 &&& gm (wpm2 149498190 991810) (P10k.take 278) =
    wem 149498190 149500002 150490000 := by
  decide +kernel

/-- Window MU152: every even n in [150490002, 151480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u152 : wem 150488190 150490002 151480000 &&& gm (wpm2 150488190 991810) (P10k.take 278) =
    wem 150488190 150490002 151480000 := by
  decide +kernel

/-- Window MU153: every even n in [151480002, 152470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u153 : wem 151478190 151480002 152470000 &&& gm (wpm2 151478190 991810) (P10k.take 278) =
    wem 151478190 151480002 152470000 := by
  decide +kernel

/-- Window MU154: every even n in [152470002, 153460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u154 : wem 152468190 152470002 153460000 &&& gm (wpm2 152468190 991810) (P10k.take 278) =
    wem 152468190 152470002 153460000 := by
  decide +kernel

/-- Window MU155: every even n in [153460002, 154450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u155 : wem 153458190 153460002 154450000 &&& gm (wpm2 153458190 991810) (P10k.take 278) =
    wem 153458190 153460002 154450000 := by
  decide +kernel

/-- Window MU156: every even n in [154450002, 155440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u156 : wem 154448190 154450002 155440000 &&& gm (wpm2 154448190 991810) (P10k.take 278) =
    wem 154448190 154450002 155440000 := by
  decide +kernel

/-- Window MU157: every even n in [155440002, 156430000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u157 : wem 155438190 155440002 156430000 &&& gm (wpm2 155438190 991810) (P10k.take 278) =
    wem 155438190 155440002 156430000 := by
  decide +kernel

/-- Window MU158: every even n in [156430002, 157420000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u158 : wem 156428190 156430002 157420000 &&& gm (wpm2 156428190 991810) (P10k.take 278) =
    wem 156428190 156430002 157420000 := by
  decide +kernel

/-- Window MU159: every even n in [157420002, 158410000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u159 : wem 157418190 157420002 158410000 &&& gm (wpm2 157418190 991810) (P10k.take 278) =
    wem 157418190 157420002 158410000 := by
  decide +kernel

/-- Window MU160: every even n in [158410002, 159400000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u160 : wem 158408190 158410002 159400000 &&& gm (wpm2 158408190 991810) (P10k.take 278) =
    wem 158408190 158410002 159400000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
