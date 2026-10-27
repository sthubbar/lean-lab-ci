/-
P0042 GvLtR 1989 ratio check, window 92, even n in [181180002, 183160000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_105 : wem 181179095 181180002 183160000 &&& gm (wpm2 181179095 1980905) (P10k.take 155) = wem 181179095 181180002 183160000 := by
  decide +kernel

theorem bnd_105 : MinGBBound 181180002 183160000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_105

theorem lr_105 : (19 + 3/200 : ℝ) ≤ Real.log ((181180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((181180002 : ℕ) : ℝ)) 19 (f := (3/200 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_105 : (2 + 945227/1000000 : ℝ) ≤ Real.log (19 + 3/200 : ℝ) := by
  have h := le_log_of (x := (19 + 3/200 : ℝ)) 2 (f := (945227/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_105 : ∀ n, Even n → 181180002 ≤ n → n ≤ 183160000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_105 ls_105 (by norm_num) (by norm_num) bnd_105

theorem r2_105 : ∀ n, Even n → 181180002 ≤ n → n ≤ 183160000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_105 ls_105 (by norm_num) (by norm_num) bnd_105

end LeanLab.GvLtR1989
