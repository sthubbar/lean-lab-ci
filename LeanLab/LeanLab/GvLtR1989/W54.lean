/-
P0042 GvLtR 1989 ratio check, window 54, even n in [105940002, 107920000], least Goldbach prime at most 863.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_67 : wem 105939139 105940002 107920000 &&& gm (wpm2 105939139 1980861) (P10k.take 150) = wem 105939139 105940002 107920000 := by
  decide +kernel

theorem bnd_67 : MinGBBound 105940002 107920000 863 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 150 863 (by decide)) chk_67

theorem lr_67 : (18 + 239191/500000 : ℝ) ≤ Real.log ((105940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((105940002 : ℕ) : ℝ)) 18 (f := (239191/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_67 : (2 + 4583/5000 : ℝ) ≤ Real.log (18 + 239191/500000 : ℝ) := by
  have h := le_log_of (x := (18 + 239191/500000 : ℝ)) 2 (f := (4583/5000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_67 : ∀ n, Even n → 105940002 ≤ n → n ≤ 107920000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_67 ls_67 (by norm_num) (by norm_num) bnd_67

theorem r2_67 : ∀ n, Even n → 105940002 ≤ n → n ≤ 107920000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_67 ls_67 (by norm_num) (by norm_num) bnd_67

end LeanLab.GvLtR1989
