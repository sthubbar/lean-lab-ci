/-
P0042 GvLtR 1989 ratio check, window 58, even n in [113860002, 115840000], least Goldbach prime at most 1039.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_71 : wem 113858963 113860002 115840000 &&& gm (wpm2 113858963 1981037) (P10k.take 175) = wem 113858963 113860002 115840000 := by
  decide +kernel

theorem bnd_71 : MinGBBound 113860002 115840000 1039 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 175 1039 (by decide)) chk_71

theorem lr_71 : (18 + 550479/1000000 : ℝ) ≤ Real.log ((113860002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((113860002 : ℕ) : ℝ)) 18 (f := (550479/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_71 : (2 + 460247/500000 : ℝ) ≤ Real.log (18 + 550479/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 550479/1000000 : ℝ)) 2 (f := (460247/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_71 : ∀ n, Even n → 113860002 ≤ n → n ≤ 115840000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_71 ls_71 (by norm_num) (by norm_num) bnd_71

theorem r2_71 : ∀ n, Even n → 113860002 ≤ n → n ≤ 115840000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_71 ls_71 (by norm_num) (by norm_num) bnd_71

end LeanLab.GvLtR1989
