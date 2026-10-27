/-
P0042 GvLtR 1989 ratio check, window 25, even n in [48520002, 50500000], least Goldbach prime at most 761.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_38 : wem 48519241 48520002 50500000 &&& gm (wpm 48519241 1980759) (P10k.take 135) = wem 48519241 48520002 50500000 := by
  decide +kernel

theorem bnd_38 : MinGBBound 48520002 50500000 761 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 135 761 (by decide)) chk_38

theorem lr_38 : (17 + 139497/200000 : ℝ) ≤ Real.log ((48520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((48520002 : ℕ) : ℝ)) 17 (f := (139497/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_38 : (2 + 873421/1000000 : ℝ) ≤ Real.log (17 + 139497/200000 : ℝ) := by
  have h := le_log_of (x := (17 + 139497/200000 : ℝ)) 2 (f := (873421/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_38 : ∀ n, Even n → 48520002 ≤ n → n ≤ 50500000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_38 ls_38 (by norm_num) (by norm_num) bnd_38

theorem r2_38 : ∀ n, Even n → 48520002 ≤ n → n ≤ 50500000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_38 ls_38 (by norm_num) (by norm_num) bnd_38

end LeanLab.GvLtR1989
