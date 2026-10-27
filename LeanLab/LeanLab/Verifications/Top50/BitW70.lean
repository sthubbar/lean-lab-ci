/-
Kernel Goldbach window 70: every even n in [137620002, 139600000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_70 : wem 137618190 137620002 139600000 &&& gm (wpm2 137618190 1981810) (P10k.take 280) =
    wem 137618190 137620002 139600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
