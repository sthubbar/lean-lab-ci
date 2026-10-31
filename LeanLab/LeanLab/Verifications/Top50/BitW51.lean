/-
Kernel Goldbach window 51: every even n in [100000002, 101980000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_51 : wem 99998190 100000002 101980000 &&& gm (wpm2 99998190 1981810) (P10k.take 280) =
    wem 99998190 100000002 101980000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
