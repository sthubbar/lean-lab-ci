/-
P0042 GvLtR 1989 ratio check, window 134, even n in [264340002, 266320000], least Goldbach prime at most 853.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_147 : wem 264339149 264340002 266320000 &&& gm (wpm2 264339149 1980851) (P10k.take 147) = wem 264339149 264340002 266320000 := by
  decide +kernel

theorem bnd_147 : MinGBBound 264340002 266320000 853 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 147 853 (by decide)) chk_147

theorem lr_147 : (19 + 78549/200000 : ℝ) ≤ Real.log ((264340002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((264340002 : ℕ) : ℝ)) 19 (f := (78549/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_147 : (2 + 482449/500000 : ℝ) ≤ Real.log (19 + 78549/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 78549/200000 : ℝ)) 2 (f := (482449/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_147 : ∀ n, Even n → 264340002 ≤ n → n ≤ 266320000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_147 ls_147 (by norm_num) (by norm_num) bnd_147

theorem r2_147 : ∀ n, Even n → 264340002 ≤ n → n ≤ 266320000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_147 ls_147 (by norm_num) (by norm_num) bnd_147

end LeanLab.GvLtR1989
