/-
Kernel Goldbach window 112: every even n in [220780002, 222760000] is p + q with q among the first 280 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1903Z-8357. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

namespace LeanLab.Verifications.Top50.Bits

theorem window_112 : wem 220778190 220780002 222760000 &&& gm (wpm2 220778190 1981810) (P10k.take 280) =
    wem 220778190 220780002 222760000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
