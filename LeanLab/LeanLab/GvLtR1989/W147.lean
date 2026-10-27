/-
P0042 GvLtR 1989 ratio check, window 147, even n in [290080002, 292060000], least Goldbach prime at most 853.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_160 : wem 290079149 290080002 292060000 &&& gm (wpm2 290079149 1980851) (P10k.take 147) = wem 290079149 290080002 292060000 := by
  decide +kernel

theorem bnd_160 : MinGBBound 290080002 292060000 853 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 147 853 (by decide)) chk_160

theorem lr_160 : (19 + 242833/500000 : ℝ) ≤ Real.log ((290080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((290080002 : ℕ) : ℝ)) 19 (f := (242833/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_160 : (2 + 484839/500000 : ℝ) ≤ Real.log (19 + 242833/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 242833/500000 : ℝ)) 2 (f := (484839/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_160 : ∀ n, Even n → 290080002 ≤ n → n ≤ 292060000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_160 ls_160 (by norm_num) (by norm_num) bnd_160

theorem r2_160 : ∀ n, Even n → 290080002 ≤ n → n ≤ 292060000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_160 ls_160 (by norm_num) (by norm_num) bnd_160

end LeanLab.GvLtR1989
