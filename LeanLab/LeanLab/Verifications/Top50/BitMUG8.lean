/-
Kernel Goldbach windows MU71 to MU80, width 990000, even n in [70300002, 80200000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU71: every even n in [70300002, 71290000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u71 : wem 70298190 70300002 71290000 &&& gm (wpm2 70298190 991810) (P10k.take 278) =
    wem 70298190 70300002 71290000 := by
  decide +kernel

/-- Window MU72: every even n in [71290002, 72280000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u72 : wem 71288190 71290002 72280000 &&& gm (wpm2 71288190 991810) (P10k.take 278) =
    wem 71288190 71290002 72280000 := by
  decide +kernel

/-- Window MU73: every even n in [72280002, 73270000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u73 : wem 72278190 72280002 73270000 &&& gm (wpm2 72278190 991810) (P10k.take 278) =
    wem 72278190 72280002 73270000 := by
  decide +kernel

/-- Window MU74: every even n in [73270002, 74260000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u74 : wem 73268190 73270002 74260000 &&& gm (wpm2 73268190 991810) (P10k.take 278) =
    wem 73268190 73270002 74260000 := by
  decide +kernel

/-- Window MU75: every even n in [74260002, 75250000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u75 : wem 74258190 74260002 75250000 &&& gm (wpm2 74258190 991810) (P10k.take 278) =
    wem 74258190 74260002 75250000 := by
  decide +kernel

/-- Window MU76: every even n in [75250002, 76240000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u76 : wem 75248190 75250002 76240000 &&& gm (wpm2 75248190 991810) (P10k.take 278) =
    wem 75248190 75250002 76240000 := by
  decide +kernel

/-- Window MU77: every even n in [76240002, 77230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u77 : wem 76238190 76240002 77230000 &&& gm (wpm2 76238190 991810) (P10k.take 278) =
    wem 76238190 76240002 77230000 := by
  decide +kernel

/-- Window MU78: every even n in [77230002, 78220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u78 : wem 77228190 77230002 78220000 &&& gm (wpm2 77228190 991810) (P10k.take 278) =
    wem 77228190 77230002 78220000 := by
  decide +kernel

/-- Window MU79: every even n in [78220002, 79210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u79 : wem 78218190 78220002 79210000 &&& gm (wpm2 78218190 991810) (P10k.take 278) =
    wem 78218190 78220002 79210000 := by
  decide +kernel

/-- Window MU80: every even n in [79210002, 80200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u80 : wem 79208190 79210002 80200000 &&& gm (wpm2 79208190 991810) (P10k.take 278) =
    wem 79208190 79210002 80200000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
