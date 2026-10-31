/-
P0042 GvLtR 1989 ratio check, window 119, even n in [234640002, 236620000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_132 : wem 234639095 234640002 236620000 &&& gm (wpm2 234639095 1980905) (P10k.take 155) = wem 234639095 234640002 236620000 := by
  decide +kernel

theorem bnd_132 : MinGBBound 234640002 236620000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_132

theorem lr_132 : (19 + 273561/1000000 : ℝ) ≤ Real.log ((234640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((234640002 : ℕ) : ℝ)) 19 (f := (273561/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_132 : (2 + 958733/1000000 : ℝ) ≤ Real.log (19 + 273561/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 273561/1000000 : ℝ)) 2 (f := (958733/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_132 : ∀ n, Even n → 234640002 ≤ n → n ≤ 236620000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_132 ls_132 (by norm_num) (by norm_num) bnd_132

theorem r2_132 : ∀ n, Even n → 234640002 ≤ n → n ≤ 236620000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_132 ls_132 (by norm_num) (by norm_num) bnd_132

end LeanLab.GvLtR1989
