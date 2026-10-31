/-
P0042 GvLtR 1989 ratio check, window 76, even n in [149500002, 151480000], least Goldbach prime at most 911.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_89 : wem 149499091 149500002 151480000 &&& gm (wpm2 149499091 1980909) (P10k.take 156) = wem 149499091 149500002 151480000 := by
  decide +kernel

theorem bnd_89 : MinGBBound 149500002 151480000 911 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 156 911 (by decide)) chk_89

theorem lr_89 : (18 + 164561/200000 : ℝ) ≤ Real.log ((149500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((149500002 : ℕ) : ℝ)) 18 (f := (164561/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_89 : (2 + 233767/250000 : ℝ) ≤ Real.log (18 + 164561/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 164561/200000 : ℝ)) 2 (f := (233767/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_89 : ∀ n, Even n → 149500002 ≤ n → n ≤ 151480000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_89 ls_89 (by norm_num) (by norm_num) bnd_89

theorem r2_89 : ∀ n, Even n → 149500002 ≤ n → n ≤ 151480000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_89 ls_89 (by norm_num) (by norm_num) bnd_89

end LeanLab.GvLtR1989
