/-
Kernel Goldbach window 60: every even n in [117820002, 119800000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_60 : wem 117818190 117820002 119800000 &&& gm (wpm2 117818190 1981810) (P10k.take 280) =
    wem 117818190 117820002 119800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
