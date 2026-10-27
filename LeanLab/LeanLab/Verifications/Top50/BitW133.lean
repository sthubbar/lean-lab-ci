/-
Kernel Goldbach window 133: every even n in [262360002, 264340000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_133 : wem 262358190 262360002 264340000 &&& gm (wpm2 262358190 1981810) (P10k.take 280) =
    wem 262358190 262360002 264340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
