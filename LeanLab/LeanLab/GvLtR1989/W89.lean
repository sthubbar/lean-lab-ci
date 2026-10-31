/-
P0042 GvLtR 1989 ratio check, window 89, even n in [175240002, 177220000], least Goldbach prime at most 967.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_102 : wem 175239035 175240002 177220000 &&& gm (wpm2 175239035 1980965) (P10k.take 163) = wem 175239035 175240002 177220000 := by
  decide +kernel

theorem bnd_102 : MinGBBound 175240002 177220000 967 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 163 967 (by decide)) chk_102

theorem lr_102 : (18 + 490833/500000 : ℝ) ≤ Real.log ((175240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((175240002 : ℕ) : ℝ)) 18 (f := (490833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_102 : (2 + 58967/62500 : ℝ) ≤ Real.log (18 + 490833/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 490833/500000 : ℝ)) 2 (f := (58967/62500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_102 : ∀ n, Even n → 175240002 ≤ n → n ≤ 177220000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_102 ls_102 (by norm_num) (by norm_num) bnd_102

theorem r2_102 : ∀ n, Even n → 175240002 ≤ n → n ≤ 177220000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_102 ls_102 (by norm_num) (by norm_num) bnd_102

end LeanLab.GvLtR1989
