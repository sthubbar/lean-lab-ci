/-
P0042 GvLtR 1989 ratio check, window 87, even n in [171280002, 173260000], least Goldbach prime at most 907.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_100 : wem 171279095 171280002 173260000 &&& gm (wpm2 171279095 1980905) (P10k.take 155) = wem 171279095 171280002 173260000 := by
  decide +kernel

theorem bnd_100 : MinGBBound 171280002 173260000 907 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 155 907 (by decide)) chk_100

theorem lr_100 : (18 + 958809/1000000 : ℝ) ≤ Real.log ((171280002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((171280002 : ℕ) : ℝ)) 18 (f := (958809/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_100 : (2 + 942267/1000000 : ℝ) ≤ Real.log (18 + 958809/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 958809/1000000 : ℝ)) 2 (f := (942267/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_100 : ∀ n, Even n → 171280002 ≤ n → n ≤ 173260000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_100 ls_100 (by norm_num) (by norm_num) bnd_100

theorem r2_100 : ∀ n, Even n → 171280002 ≤ n → n ≤ 173260000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_100 ls_100 (by norm_num) (by norm_num) bnd_100

end LeanLab.GvLtR1989
