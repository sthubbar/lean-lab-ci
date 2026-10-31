/-
P0042 GvLtR 1989 ratio check, window 107, even n in [210880002, 212860000], least Goldbach prime at most 1123.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_120 : wem 210878879 210880002 212860000 &&& gm (wpm2 210878879 1981121) (P10k.take 188) = wem 210878879 210880002 212860000 := by
  decide +kernel

theorem bnd_120 : MinGBBound 210880002 212860000 1123 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 188 1123 (by decide)) chk_120

theorem lr_120 : (19 + 83399/500000 : ℝ) ≤ Real.log ((210880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((210880002 : ℕ) : ℝ)) 19 (f := (83399/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_120 : (2 + 476589/500000 : ℝ) ≤ Real.log (19 + 83399/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 83399/500000 : ℝ)) 2 (f := (476589/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_120 : ∀ n, Even n → 210880002 ≤ n → n ≤ 212860000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_120 ls_120 (by norm_num) (by norm_num) bnd_120

theorem r2_120 : ∀ n, Even n → 210880002 ≤ n → n ≤ 212860000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_120 ls_120 (by norm_num) (by norm_num) bnd_120

end LeanLab.GvLtR1989
