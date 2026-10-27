/-
P0042 GvLtR 1989 ratio check, window 20, even n in [38620002, 40600000], least Goldbach prime at most 787.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_33 : wem 38619215 38620002 40600000 &&& gm (wpm 38619215 1980785) (P10k.take 138) = wem 38619215 38620002 40600000 := by
  decide +kernel

theorem bnd_33 : MinGBBound 38620002 40600000 787 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 138 787 (by decide)) chk_33

theorem lr_33 : (17 + 469279/1000000 : ℝ) ≤ Real.log ((38620002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((38620002 : ℕ) : ℝ)) 17 (f := (469279/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_33 : (2 + 430221/500000 : ℝ) ≤ Real.log (17 + 469279/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 469279/1000000 : ℝ)) 2 (f := (430221/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_33 : ∀ n, Even n → 38620002 ≤ n → n ≤ 40600000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_33 ls_33 (by norm_num) (by norm_num) bnd_33

theorem r2_33 : ∀ n, Even n → 38620002 ≤ n → n ≤ 40600000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_33 ls_33 (by norm_num) (by norm_num) bnd_33

end LeanLab.GvLtR1989
