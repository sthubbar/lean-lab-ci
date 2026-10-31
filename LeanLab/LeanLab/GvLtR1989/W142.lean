/-
P0042 GvLtR 1989 ratio check, window 142, even n in [280180002, 282160000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_155 : wem 280179095 280180002 282160000 &&& gm (wpm2 280179095 1980905) (P10k.take 155) = wem 280179095 280180002 282160000 := by
  decide +kernel

theorem bnd_155 : MinGBBound 280180002 282160000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_155

theorem lr_155 : (19 + 450941/1000000 : ℝ) ≤ Real.log ((280180002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((280180002 : ℕ) : ℝ)) 19 (f := (450941/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_155 : (2 + 483947/500000 : ℝ) ≤ Real.log (19 + 450941/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 450941/1000000 : ℝ)) 2 (f := (483947/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_155 : ∀ n, Even n → 280180002 ≤ n → n ≤ 282160000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_155 ls_155 (by norm_num) (by norm_num) bnd_155

theorem r2_155 : ∀ n, Even n → 280180002 ≤ n → n ≤ 282160000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_155 ls_155 (by norm_num) (by norm_num) bnd_155

end LeanLab.GvLtR1989
