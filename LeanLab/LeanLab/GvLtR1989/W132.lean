/-
P0042 GvLtR 1989 ratio check, window 132, even n in [260380002, 262360000], least Goldbach prime at most 1039.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_145 : wem 260378963 260380002 262360000 &&& gm (wpm2 260378963 1981037) (P10k.take 175) = wem 260378963 260380002 262360000 := by
  decide +kernel

theorem bnd_145 : MinGBBound 260380002 262360000 1039 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 175 1039 (by decide)) chk_145

theorem lr_145 : (19 + 377651/1000000 : ℝ) ≤ Real.log ((260380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((260380002 : ℕ) : ℝ)) 19 (f := (377651/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_145 : (2 + 964119/1000000 : ℝ) ≤ Real.log (19 + 377651/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 377651/1000000 : ℝ)) 2 (f := (964119/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_145 : ∀ n, Even n → 260380002 ≤ n → n ≤ 262360000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_145 ls_145 (by norm_num) (by norm_num) bnd_145

theorem r2_145 : ∀ n, Even n → 260380002 ≤ n → n ≤ 262360000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_145 ls_145 (by norm_num) (by norm_num) bnd_145

end LeanLab.GvLtR1989
