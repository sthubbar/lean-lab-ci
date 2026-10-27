/-
Kernel Goldbach windows MU131 to MU140, width 990000, even n in [129700002, 139600000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU131: every even n in [129700002, 130690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u131 : wem 129698190 129700002 130690000 &&& gm (wpm2 129698190 991810) (P10k.take 278) =
    wem 129698190 129700002 130690000 := by
  decide +kernel

/-- Window MU132: every even n in [130690002, 131680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u132 : wem 130688190 130690002 131680000 &&& gm (wpm2 130688190 991810) (P10k.take 278) =
    wem 130688190 130690002 131680000 := by
  decide +kernel

/-- Window MU133: every even n in [131680002, 132670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u133 : wem 131678190 131680002 132670000 &&& gm (wpm2 131678190 991810) (P10k.take 278) =
    wem 131678190 131680002 132670000 := by
  decide +kernel

/-- Window MU134: every even n in [132670002, 133660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u134 : wem 132668190 132670002 133660000 &&& gm (wpm2 132668190 991810) (P10k.take 278) =
    wem 132668190 132670002 133660000 := by
  decide +kernel

/-- Window MU135: every even n in [133660002, 134650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u135 : wem 133658190 133660002 134650000 &&& gm (wpm2 133658190 991810) (P10k.take 278) =
    wem 133658190 133660002 134650000 := by
  decide +kernel

/-- Window MU136: every even n in [134650002, 135640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u136 : wem 134648190 134650002 135640000 &&& gm (wpm2 134648190 991810) (P10k.take 278) =
    wem 134648190 134650002 135640000 := by
  decide +kernel

/-- Window MU137: every even n in [135640002, 136630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u137 : wem 135638190 135640002 136630000 &&& gm (wpm2 135638190 991810) (P10k.take 278) =
    wem 135638190 135640002 136630000 := by
  decide +kernel

/-- Window MU138: every even n in [136630002, 137620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u138 : wem 136628190 136630002 137620000 &&& gm (wpm2 136628190 991810) (P10k.take 278) =
    wem 136628190 136630002 137620000 := by
  decide +kernel

/-- Window MU139: every even n in [137620002, 138610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u139 : wem 137618190 137620002 138610000 &&& gm (wpm2 137618190 991810) (P10k.take 278) =
    wem 137618190 137620002 138610000 := by
  decide +kernel

/-- Window MU140: every even n in [138610002, 139600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u140 : wem 138608190 138610002 139600000 &&& gm (wpm2 138608190 991810) (P10k.take 278) =
    wem 138608190 138610002 139600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
