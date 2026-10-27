/-
Kernel Goldbach windows U231 to V240, width 990000, covering even n in [228700002, 238600000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U231: every even n in [228700002, 229690000] is p + q, q among the first 280 primes. -/
theorem window_u231 : wem 228698190 228700002 229690000 &&& gm (wpm2 228698190 991810) (P10k.take 280) =
    wem 228698190 228700002 229690000 := by
  decide +kernel

/-- Window U232: every even n in [229690002, 230680000] is p + q, q among the first 280 primes. -/
theorem window_u232 : wem 229688190 229690002 230680000 &&& gm (wpm2 229688190 991810) (P10k.take 280) =
    wem 229688190 229690002 230680000 := by
  decide +kernel

/-- Window U233: every even n in [230680002, 231670000] is p + q, q among the first 280 primes. -/
theorem window_u233 : wem 230678190 230680002 231670000 &&& gm (wpm2 230678190 991810) (P10k.take 280) =
    wem 230678190 230680002 231670000 := by
  decide +kernel

/-- Window U234: every even n in [231670002, 232660000] is p + q, q among the first 280 primes. -/
theorem window_u234 : wem 231668190 231670002 232660000 &&& gm (wpm2 231668190 991810) (P10k.take 280) =
    wem 231668190 231670002 232660000 := by
  decide +kernel

/-- Window U235: every even n in [232660002, 233650000] is p + q, q among the first 280 primes. -/
theorem window_u235 : wem 232658190 232660002 233650000 &&& gm (wpm2 232658190 991810) (P10k.take 280) =
    wem 232658190 232660002 233650000 := by
  decide +kernel

/-- Window U236: every even n in [233650002, 234640000] is p + q, q among the first 280 primes. -/
theorem window_u236 : wem 233648190 233650002 234640000 &&& gm (wpm2 233648190 991810) (P10k.take 280) =
    wem 233648190 233650002 234640000 := by
  decide +kernel

/-- Window U237: every even n in [234640002, 235630000] is p + q, q among the first 280 primes. -/
theorem window_u237 : wem 234638190 234640002 235630000 &&& gm (wpm2 234638190 991810) (P10k.take 280) =
    wem 234638190 234640002 235630000 := by
  decide +kernel

/-- Window U238: every even n in [235630002, 236620000] is p + q, q among the first 280 primes. -/
theorem window_u238 : wem 235628190 235630002 236620000 &&& gm (wpm2 235628190 991810) (P10k.take 280) =
    wem 235628190 235630002 236620000 := by
  decide +kernel

/-- Window U239: every even n in [236620002, 237610000] is p + q, q among the first 280 primes. -/
theorem window_u239 : wem 236618190 236620002 237610000 &&& gm (wpm2 236618190 991810) (P10k.take 280) =
    wem 236618190 236620002 237610000 := by
  decide +kernel

/-- Window U240: every even n in [237610002, 238600000] is p + q, q among the first 280 primes. -/
theorem window_u240 : wem 237608190 237610002 238600000 &&& gm (wpm2 237608190 991810) (P10k.take 280) =
    wem 237608190 237610002 238600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
