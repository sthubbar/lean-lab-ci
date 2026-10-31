/-
P0042 GvLtR 1989 ratio check, window 91, even n in [179200002, 181180000], least Goldbach prime at most 1153.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_104 : wem 179198849 179200002 181180000 &&& gm (wpm2 179198849 1981151) (P10k.take 191) = wem 179198849 179200002 181180000 := by
  decide +kernel

theorem bnd_104 : MinGBBound 179200002 181180000 1153 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 191 1153 (by decide)) chk_104

theorem lr_104 : (19 + 1003/250000 : ℝ) ≤ Real.log ((179200002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((179200002 : ℕ) : ℝ)) 19 (f := (1003/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_104 : (2 + 944649/1000000 : ℝ) ≤ Real.log (19 + 1003/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 1003/250000 : ℝ)) 2 (f := (944649/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_104 : ∀ n, Even n → 179200002 ≤ n → n ≤ 181180000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_104 ls_104 (by norm_num) (by norm_num) bnd_104

theorem r2_104 : ∀ n, Even n → 179200002 ≤ n → n ≤ 181180000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_104 ls_104 (by norm_num) (by norm_num) bnd_104

end LeanLab.GvLtR1989
