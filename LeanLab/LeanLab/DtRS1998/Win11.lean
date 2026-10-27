/-
P0037 Theorem 2 at i = 3, windows 101 to 101.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1002Z-987, unit U-0936. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.DtRS1998.Certs

set_option Elab.async false

namespace LeanLab.DtRS1998

open LeanLab.Verifications.Top50.Bits

/-- Window 101: every even n in [10^15 + 100000000, 10^15 + 100000000] is q + p, q among 1 certified primes 10^15 - d. -/
theorem w101 : GoldbachOn (Bq + 100000000) (Bq + 100000000) :=
  win_sound (lo := 100002271) (W := 1) (Ds := [2271])
    (by decide) (by decide) (by norm_num) (by norm_num [B2]) (by decide +kernel)
    (sub_Dall (by decide +kernel)) (by decide +kernel)

end LeanLab.DtRS1998
