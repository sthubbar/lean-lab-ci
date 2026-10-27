/-
Kernel Goldbach window 48: every even n in [94060002, 96040000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_48 : wem 94058902 94060002 96040000 &&& gm (wpm 94058902 1981098) (P10k.take 183) =
    wem 94058902 94060002 96040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
