/-
P0042 GvLtR 1989 ratio check, window 62, even n in [121780002, 123760000], least Goldbach prime at most 811.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_75 : wem 121779191 121780002 123760000 &&& gm (wpm2 121779191 1980809) (P10k.take 141) = wem 121779191 121780002 123760000 := by
  decide +kernel

theorem bnd_75 : MinGBBound 121780002 123760000 811 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 141 811 (by decide)) chk_75

theorem lr_75 : (18 + 24709/40000 : ℝ) ≤ Real.log ((121780002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((121780002 : ℕ) : ℝ)) 18 (f := (24709/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_75 : (2 + 924113/1000000 : ℝ) ≤ Real.log (18 + 24709/40000 : ℝ) := by
  have h := le_log_of (x := (18 + 24709/40000 : ℝ)) 2 (f := (924113/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_75 : ∀ n, Even n → 121780002 ≤ n → n ≤ 123760000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_75 ls_75 (by norm_num) (by norm_num) bnd_75

theorem r2_75 : ∀ n, Even n → 121780002 ≤ n → n ≤ 123760000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_75 ls_75 (by norm_num) (by norm_num) bnd_75

end LeanLab.GvLtR1989
