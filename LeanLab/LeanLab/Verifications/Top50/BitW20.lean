/-
Kernel Goldbach window 20: every even n in [38620002, 40600000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_20 : wem 38618902 38620002 40600000 &&& gm (wpm 38618902 1981098) (P10k.take 183) =
    wem 38618902 38620002 40600000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
