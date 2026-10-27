/-
Kernel Goldbach window 29: every even n in [56440002, 58420000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_29 : wem 56438902 56440002 58420000 &&& gm (wpm 56438902 1981098) (P10k.take 183) =
    wem 56438902 56440002 58420000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
