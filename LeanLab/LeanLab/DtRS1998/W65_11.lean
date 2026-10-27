/-
P0037 Theorem 2 at B = 10^65, windows 101 to 101.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1303Z-6675, unit U-0943. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.DtRS1998.Certs65

set_option Elab.async false

namespace LeanLab.DtRS1998.I65

open LeanLab.DtRS1998 LeanLab.Verifications.Top50.Bits

theorem w101 : GoldbachOn (Bq + 100000000) (Bq + 100000000) :=
  win_sound (lo := 100001809) (W := 1) (Ds := [1809])
    (by decide) (by decide) (by norm_num) (by norm_num [B2]) (by decide +kernel)
    (sub_Dall (by decide +kernel)) (by decide +kernel)

end LeanLab.DtRS1998.I65
