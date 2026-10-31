/-
Kernel Goldbach windows MU31 to MU40, width 990000, even n in [30700002, 40600000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU31: every even n in [30700002, 31690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u31 : wem 30698190 30700002 31690000 &&& gm (wpm2 30698190 991810) (P10k.take 278) =
    wem 30698190 30700002 31690000 := by
  decide +kernel

/-- Window MU32: every even n in [31690002, 32680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u32 : wem 31688190 31690002 32680000 &&& gm (wpm2 31688190 991810) (P10k.take 278) =
    wem 31688190 31690002 32680000 := by
  decide +kernel

/-- Window MU33: every even n in [32680002, 33670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u33 : wem 32678190 32680002 33670000 &&& gm (wpm2 32678190 991810) (P10k.take 278) =
    wem 32678190 32680002 33670000 := by
  decide +kernel

/-- Window MU34: every even n in [33670002, 34660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u34 : wem 33668190 33670002 34660000 &&& gm (wpm2 33668190 991810) (P10k.take 278) =
    wem 33668190 33670002 34660000 := by
  decide +kernel

/-- Window MU35: every even n in [34660002, 35650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u35 : wem 34658190 34660002 35650000 &&& gm (wpm2 34658190 991810) (P10k.take 278) =
    wem 34658190 34660002 35650000 := by
  decide +kernel

/-- Window MU36: every even n in [35650002, 36640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u36 : wem 35648190 35650002 36640000 &&& gm (wpm2 35648190 991810) (P10k.take 278) =
    wem 35648190 35650002 36640000 := by
  decide +kernel

/-- Window MU37: every even n in [36640002, 37630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u37 : wem 36638190 36640002 37630000 &&& gm (wpm2 36638190 991810) (P10k.take 278) =
    wem 36638190 36640002 37630000 := by
  decide +kernel

/-- Window MU38: every even n in [37630002, 38620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u38 : wem 37628190 37630002 38620000 &&& gm (wpm2 37628190 991810) (P10k.take 278) =
    wem 37628190 37630002 38620000 := by
  decide +kernel

/-- Window MU39: every even n in [38620002, 39610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u39 : wem 38618190 38620002 39610000 &&& gm (wpm2 38618190 991810) (P10k.take 278) =
    wem 38618190 38620002 39610000 := by
  decide +kernel

/-- Window MU40: every even n in [39610002, 40600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u40 : wem 39608190 39610002 40600000 &&& gm (wpm2 39608190 991810) (P10k.take 278) =
    wem 39608190 39610002 40600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
