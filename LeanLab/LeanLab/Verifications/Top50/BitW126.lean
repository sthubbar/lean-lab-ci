/-
Kernel Goldbach window 126: every even n in [248500002, 250480000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_126 : wem 248498190 248500002 250480000 &&& gm (wpm2 248498190 1981810) (P10k.take 280) =
    wem 248498190 248500002 250480000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
