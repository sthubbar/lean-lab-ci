/-
Kernel Goldbach window 139: every even n in [274240002, 276220000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_139 : wem 274238190 274240002 276220000 &&& gm (wpm2 274238190 1981810) (P10k.take 280) =
    wem 274238190 274240002 276220000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
