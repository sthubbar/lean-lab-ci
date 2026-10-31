/-
Kernel Goldbach window 127: every even n in [250480002, 252460000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_127 : wem 250478190 250480002 252460000 &&& gm (wpm2 250478190 1981810) (P10k.take 280) =
    wem 250478190 250480002 252460000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
