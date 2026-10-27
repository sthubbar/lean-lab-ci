/-
P0042 GvLtR 1989 ratio check, window 158, even n in [311860002, 313840000], least Goldbach prime at most 1087.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_171 : wem 311858915 311860002 313840000 &&& gm (wpm2 311858915 1981085) (P10k.take 181) = wem 311858915 311860002 313840000 := by
  decide +kernel

theorem bnd_171 : MinGBBound 311860002 313840000 1087 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 181 1087 (by decide)) chk_171

theorem lr_171 : (19 + 558063/1000000 : ℝ) ≤ Real.log ((311860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((311860002 : ℕ) : ℝ)) 19 (f := (558063/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_171 : (2 + 486693/500000 : ℝ) ≤ Real.log (19 + 558063/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 558063/1000000 : ℝ)) 2 (f := (486693/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_171 : ∀ n, Even n → 311860002 ≤ n → n ≤ 313840000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_171 ls_171 (by norm_num) (by norm_num) bnd_171

theorem r2_171 : ∀ n, Even n → 311860002 ≤ n → n ≤ 313840000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_171 ls_171 (by norm_num) (by norm_num) bnd_171

end LeanLab.GvLtR1989
