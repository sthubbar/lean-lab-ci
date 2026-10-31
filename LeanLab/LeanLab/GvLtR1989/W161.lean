/-
P0042 GvLtR 1989 ratio check, window 161, even n in [317800002, 319780000], least Goldbach prime at most 977.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_174 : wem 317799025 317800002 319780000 &&& gm (wpm2 317799025 1980975) (P10k.take 165) = wem 317799025 317800002 319780000 := by
  decide +kernel

theorem bnd_174 : MinGBBound 317800002 319780000 977 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 165 977 (by decide)) chk_174

theorem lr_174 : (19 + 576931/1000000 : ℝ) ≤ Real.log ((317800002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((317800002 : ℕ) : ℝ)) 19 (f := (576931/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_174 : (2 + 19487/20000 : ℝ) ≤ Real.log (19 + 576931/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 576931/1000000 : ℝ)) 2 (f := (19487/20000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_174 : ∀ n, Even n → 317800002 ≤ n → n ≤ 319780000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_174 ls_174 (by norm_num) (by norm_num) bnd_174

theorem r2_174 : ∀ n, Even n → 317800002 ≤ n → n ≤ 319780000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_174 ls_174 (by norm_num) (by norm_num) bnd_174

end LeanLab.GvLtR1989
