/-
P0042 GvLtR 1989 ratio check, window 114, even n in [224740002, 226720000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_127 : wem 224739011 224740002 226720000 &&& gm (wpm2 224739011 1980989) (P10k.take 167) = wem 224739011 224740002 226720000 := by
  decide +kernel

theorem bnd_127 : MinGBBound 224740002 226720000 991 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_127

theorem lr_127 : (19 + 230453/1000000 : ℝ) ≤ Real.log ((224740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((224740002 : ℕ) : ℝ)) 19 (f := (230453/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_127 : (2 + 478247/500000 : ℝ) ≤ Real.log (19 + 230453/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 230453/1000000 : ℝ)) 2 (f := (478247/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_127 : ∀ n, Even n → 224740002 ≤ n → n ≤ 226720000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_127 ls_127 (by norm_num) (by norm_num) bnd_127

theorem r2_127 : ∀ n, Even n → 224740002 ≤ n → n ≤ 226720000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_127 ls_127 (by norm_num) (by norm_num) bnd_127

end LeanLab.GvLtR1989
