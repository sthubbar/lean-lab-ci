/-
P0042 GvLtR 1989 ratio check, window 136, even n in [268300002, 270280000], least Goldbach prime at most 1063.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_149 : wem 268298939 268300002 270280000 &&& gm (wpm2 268298939 1981061) (P10k.take 179) = wem 268298939 268300002 270280000 := by
  decide +kernel

theorem bnd_149 : MinGBBound 268300002 270280000 1063 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 179 1063 (by decide)) chk_149

theorem lr_149 : (19 + 81523/200000 : ℝ) ≤ Real.log ((268300002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((268300002 : ℕ) : ℝ)) 19 (f := (81523/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_149 : (2 + 30177/31250 : ℝ) ≤ Real.log (19 + 81523/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 81523/200000 : ℝ)) 2 (f := (30177/31250 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_149 : ∀ n, Even n → 268300002 ≤ n → n ≤ 270280000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_149 ls_149 (by norm_num) (by norm_num) bnd_149

theorem r2_149 : ∀ n, Even n → 268300002 ≤ n → n ≤ 270280000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_149 ls_149 (by norm_num) (by norm_num) bnd_149

end LeanLab.GvLtR1989
