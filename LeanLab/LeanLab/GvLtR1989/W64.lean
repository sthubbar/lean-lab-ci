/-
P0042 GvLtR 1989 ratio check, window 64, even n in [125740002, 127720000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_77 : wem 125738993 125740002 127720000 &&& gm (wpm2 125738993 1981007) (P10k.take 169) = wem 125738993 125740002 127720000 := by
  decide +kernel

theorem bnd_77 : MinGBBound 125740002 127720000 1009 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_77

theorem lr_77 : (18 + 25989/40000 : ℝ) ≤ Real.log ((125740002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((125740002 : ℕ) : ℝ)) 18 (f := (25989/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_77 : (2 + 92583/100000 : ℝ) ≤ Real.log (18 + 25989/40000 : ℝ) := by
  have h := le_log_of (x := (18 + 25989/40000 : ℝ)) 2 (f := (92583/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_77 : ∀ n, Even n → 125740002 ≤ n → n ≤ 127720000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_77 ls_77 (by norm_num) (by norm_num) bnd_77

theorem r2_77 : ∀ n, Even n → 125740002 ≤ n → n ≤ 127720000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_77 ls_77 (by norm_num) (by norm_num) bnd_77

end LeanLab.GvLtR1989
