/-
P0042 GvLtR 1989 ratio check, window 118, even n in [232660002, 234640000], least Goldbach prime at most 1063.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_131 : wem 232658939 232660002 234640000 &&& gm (wpm2 232658939 1981061) (P10k.take 179) = wem 232658939 232660002 234640000 := by
  decide +kernel

theorem bnd_131 : MinGBBound 232660002 234640000 1063 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 179 1063 (by decide)) chk_131

theorem lr_131 : (19 + 265087/1000000 : ℝ) ≤ Real.log ((232660002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((232660002 : ℕ) : ℝ)) 19 (f := (265087/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_131 : (2 + 958293/1000000 : ℝ) ≤ Real.log (19 + 265087/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 265087/1000000 : ℝ)) 2 (f := (958293/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_131 : ∀ n, Even n → 232660002 ≤ n → n ≤ 234640000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_131 ls_131 (by norm_num) (by norm_num) bnd_131

theorem r2_131 : ∀ n, Even n → 232660002 ≤ n → n ≤ 234640000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_131 ls_131 (by norm_num) (by norm_num) bnd_131

end LeanLab.GvLtR1989
