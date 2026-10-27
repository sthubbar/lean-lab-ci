/-
P0042 GvLtR 1989 ratio check, window 60, even n in [117820002, 119800000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_73 : wem 117819251 117820002 119800000 &&& gm (wpm2 117819251 1980749) (P10k.take 133) = wem 117819251 117820002 119800000 := by
  decide +kernel

theorem bnd_73 : MinGBBound 117820002 119800000 751 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_73

theorem lr_73 : (18 + 584667/1000000 : ℝ) ≤ Real.log ((117820002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((117820002 : ℕ) : ℝ)) 18 (f := (584667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_73 : (2 + 184467/200000 : ℝ) ≤ Real.log (18 + 584667/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 584667/1000000 : ℝ)) 2 (f := (184467/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_73 : ∀ n, Even n → 117820002 ≤ n → n ≤ 119800000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_73 ls_73 (by norm_num) (by norm_num) bnd_73

theorem r2_73 : ∀ n, Even n → 117820002 ≤ n → n ≤ 119800000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_73 ls_73 (by norm_num) (by norm_num) bnd_73

end LeanLab.GvLtR1989
