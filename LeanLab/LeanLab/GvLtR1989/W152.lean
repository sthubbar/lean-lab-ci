/-
P0042 GvLtR 1989 ratio check, window 152, even n in [299980002, 301960000], least Goldbach prime at most 1069.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_165 : wem 299978933 299980002 301960000 &&& gm (wpm2 299978933 1981067) (P10k.take 180) = wem 299978933 299980002 301960000 := by
  decide +kernel

theorem bnd_165 : MinGBBound 299980002 301960000 1069 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 180 1069 (by decide)) chk_165

theorem lr_165 : (19 + 20769/40000 : ℝ) ≤ Real.log ((299980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((299980002 : ℕ) : ℝ)) 19 (f := (20769/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_165 : (2 + 485699/500000 : ℝ) ≤ Real.log (19 + 20769/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 20769/40000 : ℝ)) 2 (f := (485699/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_165 : ∀ n, Even n → 299980002 ≤ n → n ≤ 301960000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_165 ls_165 (by norm_num) (by norm_num) bnd_165

theorem r2_165 : ∀ n, Even n → 299980002 ≤ n → n ≤ 301960000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_165 ls_165 (by norm_num) (by norm_num) bnd_165

end LeanLab.GvLtR1989
