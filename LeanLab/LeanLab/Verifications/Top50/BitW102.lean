/-
Kernel Goldbach window 102: every even n in [200980002, 202960000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_102 : wem 200978190 200980002 202960000 &&& gm (wpm2 200978190 1981810) (P10k.take 280) =
    wem 200978190 200980002 202960000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
