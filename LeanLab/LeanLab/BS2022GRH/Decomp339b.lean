/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Supply the running remainder estimate and its large A endpoint reduction.
Journal pp. 1240 and 1241, displays 32 and 33.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp339a

namespace LeanLab.BS2022GRH.Decomp339b
open Real Finset Classical ChenThresholdGRH DecompC164c Decomp339a
noncomputable section

/-- The summed main and correction budgets of display 33, p. 1240. -/
def totalBudget (n : ℕ) (A ε₁ : ℝ) : ℝ :=
  0.053 * log n / log (1 + ε₁) * mainScale n A ε₁ +
    0.08 * log n / log (1 + ε₁) * correctionScale n ε₁

/-- Exact normalization of display 33 into the error bracket at the running endpoint.
This algebra does not transfer endpoints or assume a residue bound. -/
theorem totalBudget_normalization (n : ℕ) (A ε₁ : ℝ) (hn : 1 < n) (hε : 0 < ε₁) :
    invTw * totalBudget n A ε₁ = (n : ℝ) / log n ^ 2 * errorBracket A n ε₁ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hL : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn)
  have hb : 0 < 1 + ε₁ := by linarith
  have hlb : 0 < log (1 + ε₁) := log_pos (by linarith)
  have h1 : log (n : ℝ) ^ (A - 1) = log (n : ℝ) ^ (A - 4) * log n ^ 3 := by
    rw [← rpow_natCast, ← rpow_add hL]
    congr 1
    ring
  have h2 : log (n : ℝ) ^ (A + 1) = log (n : ℝ) ^ (A - 4) * log n ^ 5 := by
    rw [← rpow_natCast, ← rpow_add hL]
    congr 1
    ring
  have h3 : (n : ℝ) ^ (-(1 / 8) : ℝ) = (n : ℝ) ^ (7 / 8 : ℝ) / n := by
    calc
      _ = (n : ℝ) ^ ((7 / 8 : ℝ) - 1) := by congr 1; norm_num
      _ = (n : ℝ) ^ (7 / 8 : ℝ) / (n : ℝ) ^ (1 : ℝ) := rpow_sub hn0 _ _
      _ = _ := by rw [rpow_one]
  have h4 : (1 + ε₁) ^ (-(1 / 2) : ℝ) = √(1 + ε₁) / (1 + ε₁) := by
    calc
      _ = (1 + ε₁) ^ ((1 / 2 : ℝ) - 1) := by congr 1; norm_num
      _ = (1 + ε₁) ^ (1 / 2 : ℝ) / (1 + ε₁) ^ (1 : ℝ) := rpow_sub hb _ _
      _ = _ := by rw [rpow_one, sqrt_eq_rpow]
  unfold totalBudget mainScale correctionScale errorBracket U7153.zz
  rw [h1, h2, h3, h4]
  field_simp [hL.ne', hlb.ne', hn0.ne', hb.ne', (rpow_pos_of_pos hL (A - 4)).ne']
  <;> ring

/-- Sum the independent per-slice bounds before any endpoint transfer.
CONDITIONAL ON Lemmas 4, 5 and 8 and the two task339a scalar leaves.
Journal pp. 1240 and 1241 display 33. -/
theorem remainder_le_totalBudget (h4 : PaperInputs148.Lemma4J)
    (hPhi : PaperInputs148.Lemma5PhiJ) (h8 : Decomp148a.Lemma8J) (hG : GRH)
    (α A u X₂ ε₁ : ℝ) (n : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) : remainder n A ε₁ ≤ totalBudget n A ε₁ := by
  exact remainder_sum_of_slice_bounds n A ε₁ (mainScale n A ε₁) (correctionScale n ε₁)
    (Lemma11C164.log_lower n (hX.trans hn)) hε hε1
    (mainScale_nonneg h8 hG α A u X₂ ε₁ n hε hε1 hα hα1 hA hc hX hn hev)
    (by unfold correctionScale; positivity)
    (fun j hj => slice_bound h4 hPhi h8 hG α A u X₂ ε₁ n j
      hε hε1 hα hα1 hA hc hX hn hev hj)

/-- LEAF. Scalar endpoint transfer restricted to A at least four.
Theorem 7 p. 1235 and the last step after display 33 on p. 1241.
The source allows positive A. The monotonicity route here requires this stronger guard.
No residue, finite sum, GRH or singular factor occurs in this statement. -/
theorem error_at_threshold (α A u X₂ N ε₁ : ℝ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hAge : 4 ≤ A) (hc : Cond25 α A u X₂)
    (hX : exp (exp 10) ≤ X₂) (hN : X₂ ≤ N) :
    errorBracket A N ε₁ ≤ errorBracket A X₂ ε₁ := by
  sorry

/-- The exact running endpoint form of the remainder estimate in display 33.
CONDITIONAL ON the two task339a scalar leaves and existing Lemmas 4, 5 and 8.
No transfer to X2 and no lower bound four on A is used. Journal pp. 1240 and 1241. -/
theorem remainder_bound_running (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 * errorBracket A n ε₁ := by
  have hN := hX.trans hn
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hL := Lemma11C164.log_lower n hN
  have hn1 : 1 < n := by
    have hnR : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hN
    exact_mod_cast hnR
  have hinv : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hs := remainder_le_totalBudget Decomp406c.lemma4_robin PublishedInputs232.lemma5_phi
    Decomp406e.lemma8J hG α A u X₂ ε₁ n hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have ht0 : 0 ≤ totalBudget n A ε₁ :=
    (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))).trans hs
  have hUN := DecompC169b.UNfull_invTw_ge_one n
  have hu : 0 ≤ UNfull n := by
    exact (mul_nonneg_iff_of_pos_right hinv).mp (by linarith : 0 ≤ UNfull n * invTw)
  calc
    remainder n A ε₁ ≤ totalBudget n A ε₁ := hs
    _ ≤ (UNfull n * invTw) * totalBudget n A ε₁ := le_mul_of_one_le_left ht0 hUN
    _ = UNfull n * ((n : ℝ) / log n ^ 2 * errorBracket A n ε₁) := by
      rw [mul_assoc, totalBudget_normalization n A ε₁ hn1 hε₁]
    _ = UNfull n * n / log n ^ 2 * errorBracket A n ε₁ := by ring

/-- Restricted large A consequence of the smaller scalar leaves, with no direct sorry.
CONDITIONAL ON those leaves and the existing Lemmas 4, 5 and 8.
This does not supply the sealed universal positive A statement.
The original DecompC164c remainder leaf is never invoked. Journal pp. 1239 to 1241. -/
theorem remainder_bound_large_A (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hAge : 4 ≤ A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := by
  have hu : 0 ≤ UNfull n := (by norm_num : (0 : ℝ) ≤ 2 / 5).trans (two_fifths_le_UNfull n)
  exact (remainder_bound_running α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hc hX hn hev).trans
    (mul_le_mul_of_nonneg_left
      (error_at_threshold α A u X₂ n ε₁ hε₁ hε₁1 hα hα1 hA hAge hc hX hn) (by positivity))

end
end LeanLab.BS2022GRH.Decomp339b
#print axioms LeanLab.BS2022GRH.Decomp339b.totalBudget_normalization
#print axioms LeanLab.BS2022GRH.Decomp339b.remainder_le_totalBudget
#print axioms LeanLab.BS2022GRH.Decomp339b.remainder_bound_running
#print axioms LeanLab.BS2022GRH.Decomp339b.error_at_threshold
#print axioms LeanLab.BS2022GRH.Decomp339b.remainder_bound_large_A
