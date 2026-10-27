/-
Kernel Goldbach window 4: every even n in [6940002, 8920000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_4 : wem 6938902 6940002 8920000 &&& gm (wpm 6938902 1981098) (P10k.take 183) =
    wem 6938902 6940002 8920000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
