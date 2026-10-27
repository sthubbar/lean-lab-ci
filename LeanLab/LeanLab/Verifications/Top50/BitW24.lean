/-
Kernel Goldbach window 24: every even n in [46540002, 48520000] is p + q with q among the first 183 primes.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1704Z-8485. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve

namespace LeanLab.Verifications.Top50.Bits

theorem window_24 : wem 46538902 46540002 48520000 &&& gm (wpm 46538902 1981098) (P10k.take 183) =
    wem 46538902 46540002 48520000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
