/-
Kernel Goldbach window 14: every even n in [26740002, 28720000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_14 : wem 26738902 26740002 28720000 &&& gm (wpm 26738902 1981098) (P10k.take 183) =
    wem 26738902 26740002 28720000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
