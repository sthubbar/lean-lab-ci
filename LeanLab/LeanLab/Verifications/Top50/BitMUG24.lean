/-
Kernel Goldbach windows MU231 to MU240, width 990000, even n in [228700002, 238600000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU231: every even n in [228700002, 229690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u231 : wem 228698190 228700002 229690000 &&& gm (wpm2 228698190 991810) (P10k.take 278) =
    wem 228698190 228700002 229690000 := by
  decide +kernel

/-- Window MU232: every even n in [229690002, 230680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u232 : wem 229688190 229690002 230680000 &&& gm (wpm2 229688190 991810) (P10k.take 278) =
    wem 229688190 229690002 230680000 := by
  decide +kernel

/-- Window MU233: every even n in [230680002, 231670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u233 : wem 230678190 230680002 231670000 &&& gm (wpm2 230678190 991810) (P10k.take 278) =
    wem 230678190 230680002 231670000 := by
  decide +kernel

/-- Window MU234: every even n in [231670002, 232660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u234 : wem 231668190 231670002 232660000 &&& gm (wpm2 231668190 991810) (P10k.take 278) =
    wem 231668190 231670002 232660000 := by
  decide +kernel

/-- Window MU235: every even n in [232660002, 233650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u235 : wem 232658190 232660002 233650000 &&& gm (wpm2 232658190 991810) (P10k.take 278) =
    wem 232658190 232660002 233650000 := by
  decide +kernel

/-- Window MU236: every even n in [233650002, 234640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u236 : wem 233648190 233650002 234640000 &&& gm (wpm2 233648190 991810) (P10k.take 278) =
    wem 233648190 233650002 234640000 := by
  decide +kernel

/-- Window MU237: every even n in [234640002, 235630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u237 : wem 234638190 234640002 235630000 &&& gm (wpm2 234638190 991810) (P10k.take 278) =
    wem 234638190 234640002 235630000 := by
  decide +kernel

/-- Window MU238: every even n in [235630002, 236620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u238 : wem 235628190 235630002 236620000 &&& gm (wpm2 235628190 991810) (P10k.take 278) =
    wem 235628190 235630002 236620000 := by
  decide +kernel

/-- Window MU239: every even n in [236620002, 237610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u239 : wem 236618190 236620002 237610000 &&& gm (wpm2 236618190 991810) (P10k.take 278) =
    wem 236618190 236620002 237610000 := by
  decide +kernel

/-- Window MU240: every even n in [237610002, 238600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u240 : wem 237608190 237610002 238600000 &&& gm (wpm2 237608190 991810) (P10k.take 278) =
    wem 237608190 237610002 238600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
