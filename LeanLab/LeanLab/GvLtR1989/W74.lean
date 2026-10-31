/-
P0042 GvLtR 1989 ratio check, window 74, even n in [145540002, 147520000], least Goldbach prime at most 1039.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_87 : wem 145538963 145540002 147520000 &&& gm (wpm2 145538963 1981037) (P10k.take 175) = wem 145538963 145540002 147520000 := by
  decide +kernel

theorem bnd_87 : MinGBBound 145540002 147520000 1039 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 175 1039 (by decide)) chk_87

theorem lr_87 : (18 + 19899/25000 : ℝ) ≤ Real.log ((145540002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((145540002 : ℕ) : ℝ)) 18 (f := (19899/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_87 : (2 + 23341/25000 : ℝ) ≤ Real.log (18 + 19899/25000 : ℝ) := by
  have h := le_log_of (x := (18 + 19899/25000 : ℝ)) 2 (f := (23341/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_87 : ∀ n, Even n → 145540002 ≤ n → n ≤ 147520000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_87 ls_87 (by norm_num) (by norm_num) bnd_87

theorem r2_87 : ∀ n, Even n → 145540002 ≤ n → n ≤ 147520000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_87 ls_87 (by norm_num) (by norm_num) bnd_87

end LeanLab.GvLtR1989
