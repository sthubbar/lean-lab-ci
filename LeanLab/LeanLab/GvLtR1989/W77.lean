/-
P0042 GvLtR 1989 ratio check, window 77, even n in [151480002, 153460000], least Goldbach prime at most 947.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_90 : wem 151479055 151480002 153460000 &&& gm (wpm2 151479055 1980945) (P10k.take 161) = wem 151479055 151480002 153460000 := by
  decide +kernel

theorem bnd_90 : MinGBBound 151480002 153460000 947 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 161 947 (by decide)) chk_90

theorem lr_90 : (18 + 835963/1000000 : ℝ) ≤ Real.log ((151480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((151480002 : ℕ) : ℝ)) 18 (f := (835963/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_90 : (2 + 467883/500000 : ℝ) ≤ Real.log (18 + 835963/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 835963/1000000 : ℝ)) 2 (f := (467883/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_90 : ∀ n, Even n → 151480002 ≤ n → n ≤ 153460000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_90 ls_90 (by norm_num) (by norm_num) bnd_90

theorem r2_90 : ∀ n, Even n → 151480002 ≤ n → n ≤ 153460000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_90 ls_90 (by norm_num) (by norm_num) bnd_90

end LeanLab.GvLtR1989
