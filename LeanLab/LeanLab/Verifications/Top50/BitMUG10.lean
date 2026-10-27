/-
Kernel Goldbach windows MU91 to MU100, width 990000, even n in [90100002, 100000000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU91: every even n in [90100002, 91090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u91 : wem 90098190 90100002 91090000 &&& gm (wpm2 90098190 991810) (P10k.take 278) =
    wem 90098190 90100002 91090000 := by
  decide +kernel

/-- Window MU92: every even n in [91090002, 92080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u92 : wem 91088190 91090002 92080000 &&& gm (wpm2 91088190 991810) (P10k.take 278) =
    wem 91088190 91090002 92080000 := by
  decide +kernel

/-- Window MU93: every even n in [92080002, 93070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u93 : wem 92078190 92080002 93070000 &&& gm (wpm2 92078190 991810) (P10k.take 278) =
    wem 92078190 92080002 93070000 := by
  decide +kernel

/-- Window MU94: every even n in [93070002, 94060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u94 : wem 93068190 93070002 94060000 &&& gm (wpm2 93068190 991810) (P10k.take 278) =
    wem 93068190 93070002 94060000 := by
  decide +kernel

/-- Window MU95: every even n in [94060002, 95050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u95 : wem 94058190 94060002 95050000 &&& gm (wpm2 94058190 991810) (P10k.take 278) =
    wem 94058190 94060002 95050000 := by
  decide +kernel

/-- Window MU96: every even n in [95050002, 96040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u96 : wem 95048190 95050002 96040000 &&& gm (wpm2 95048190 991810) (P10k.take 278) =
    wem 95048190 95050002 96040000 := by
  decide +kernel

/-- Window MU97: every even n in [96040002, 97030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u97 : wem 96038190 96040002 97030000 &&& gm (wpm2 96038190 991810) (P10k.take 278) =
    wem 96038190 96040002 97030000 := by
  decide +kernel

/-- Window MU98: every even n in [97030002, 98020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u98 : wem 97028190 97030002 98020000 &&& gm (wpm2 97028190 991810) (P10k.take 278) =
    wem 97028190 97030002 98020000 := by
  decide +kernel

/-- Window MU99: every even n in [98020002, 99010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u99 : wem 98018190 98020002 99010000 &&& gm (wpm2 98018190 991810) (P10k.take 278) =
    wem 98018190 98020002 99010000 := by
  decide +kernel

/-- Window MU100: every even n in [99010002, 100000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u100 : wem 99008190 99010002 100000000 &&& gm (wpm2 99008190 991810) (P10k.take 278) =
    wem 99008190 99010002 100000000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
