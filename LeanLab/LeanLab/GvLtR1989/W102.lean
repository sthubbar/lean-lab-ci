/-
P0042 GvLtR 1989 ratio check, window 102, even n in [200980002, 202960000], least Goldbach prime at most 1087.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_115 : wem 200978915 200980002 202960000 &&& gm (wpm2 200978915 1981085) (P10k.take 181) = wem 200978915 200980002 202960000 := by
  decide +kernel

theorem bnd_115 : MinGBBound 200980002 202960000 1087 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 181 1087 (by decide)) chk_115

theorem lr_115 : (19 + 59357/500000 : ℝ) ≤ Real.log ((200980002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((200980002 : ℕ) : ℝ)) 19 (f := (59357/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_115 : (2 + 475333/500000 : ℝ) ≤ Real.log (19 + 59357/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 59357/500000 : ℝ)) 2 (f := (475333/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_115 : ∀ n, Even n → 200980002 ≤ n → n ≤ 202960000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_115 ls_115 (by norm_num) (by norm_num) bnd_115

theorem r2_115 : ∀ n, Even n → 200980002 ≤ n → n ≤ 202960000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_115 ls_115 (by norm_num) (by norm_num) bnd_115

end LeanLab.GvLtR1989
