/-
Kernel Goldbach window 27: every even n in [52480002, 54460000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_27 : wem 52478902 52480002 54460000 &&& gm (wpm 52478902 1981098) (P10k.take 183) =
    wem 52478902 52480002 54460000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
