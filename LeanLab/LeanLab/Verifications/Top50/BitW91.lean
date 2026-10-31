/-
Kernel Goldbach window 91: every even n in [179200002, 181180000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_91 : wem 179198190 179200002 181180000 &&& gm (wpm2 179198190 1981810) (P10k.take 280) =
    wem 179198190 179200002 181180000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
