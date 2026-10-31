/-
Kernel Goldbach window 145: every even n in [286120002, 288100000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_145 : wem 286118190 286120002 288100000 &&& gm (wpm2 286118190 1981810) (P10k.take 280) =
    wem 286118190 286120002 288100000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
