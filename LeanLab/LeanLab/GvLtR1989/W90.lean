/-
P0042 GvLtR 1989 ratio check, window 90, even n in [177220002, 179200000], least Goldbach prime at most 1087.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_103 : wem 177218915 177220002 179200000 &&& gm (wpm2 177218915 1981085) (P10k.take 181) = wem 177218915 177220002 179200000 := by
  decide +kernel

theorem bnd_103 : MinGBBound 177220002 179200000 1087 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 181 1087 (by decide)) chk_103

theorem lr_103 : (18 + 992901/1000000 : ℝ) ≤ Real.log ((177220002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((177220002 : ℕ) : ℝ)) 18 (f := (992901/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_103 : (2 + 14751/15625 : ℝ) ≤ Real.log (18 + 992901/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 992901/1000000 : ℝ)) 2 (f := (14751/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_103 : ∀ n, Even n → 177220002 ≤ n → n ≤ 179200000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_103 ls_103 (by norm_num) (by norm_num) bnd_103

theorem r2_103 : ∀ n, Even n → 177220002 ≤ n → n ≤ 179200000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_103 ls_103 (by norm_num) (by norm_num) bnd_103

end LeanLab.GvLtR1989
