/-
Kernel Goldbach window 17: every even n in [32680002, 34660000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_17 : wem 32678902 32680002 34660000 &&& gm (wpm 32678902 1981098) (P10k.take 183) =
    wem 32678902 32680002 34660000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
