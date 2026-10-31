/-
Kernel Goldbach window 8: every even n in [14860002, 16840000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_8 : wem 14858902 14860002 16840000 &&& gm (wpm 14858902 1981098) (P10k.take 183) =
    wem 14858902 14860002 16840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
