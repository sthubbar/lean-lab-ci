/-
P0042 GvLtR 1989 ratio check, window 160, even n in [315820002, 317800000], least Goldbach prime at most 829.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_173 : wem 315819173 315820002 317800000 &&& gm (wpm2 315819173 1980827) (P10k.take 145) = wem 315819173 315820002 317800000 := by
  decide +kernel

theorem bnd_173 : MinGBBound 315820002 317800000 829 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 145 829 (by decide)) chk_173

theorem lr_173 : (19 + 570681/1000000 : ℝ) ≤ Real.log ((315820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((315820002 : ℕ) : ℝ)) 19 (f := (570681/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_173 : (2 + 974031/1000000 : ℝ) ≤ Real.log (19 + 570681/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 570681/1000000 : ℝ)) 2 (f := (974031/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_173 : ∀ n, Even n → 315820002 ≤ n → n ≤ 317800000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_173 ls_173 (by norm_num) (by norm_num) bnd_173

theorem r2_173 : ∀ n, Even n → 315820002 ≤ n → n ≤ 317800000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_173 ls_173 (by norm_num) (by norm_num) bnd_173

end LeanLab.GvLtR1989
