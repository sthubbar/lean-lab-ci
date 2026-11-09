/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Running and restricted endpoint remainder bounds with every cited analytic input explicit.
Journal pp. 1240 and 1241 display 33.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.CharacterInputs332
import LeanLab.BS2022GRH.EndpointCompare332
import LeanLab.BS2022GRH.Decomp339b

namespace LeanLab.BS2022GRH.Decomp332b
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The running remainder estimate needs only the explicit Lemmas 3, 4 and 5.
Journal pp. 1240 and 1241 display 33. CONDITIONAL ON h3, h4, hPhi and GRH.
The finite slice, balancing, coefficient and correction steps have clean proofs. -/
theorem remainder_bound_running (h3 : Lemma3J) (h4 : PaperInputs148.Lemma4J)
    (hPhi : PaperInputs148.Lemma5PhiJ) (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
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
  have hs := Decomp339b.remainder_le_totalBudget h4 hPhi
    (CharacterInputs332.lemma8_of_inputs h3 h4 hPhi) hG α A u X₂ ε₁ n hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have ht0 : 0 ≤ Decomp339b.totalBudget n A ε₁ :=
    (sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))).trans hs
  have hUN := DecompC169b.UNfull_invTw_ge_one n
  have hu : 0 ≤ UNfull n := by
    exact (mul_nonneg_iff_of_pos_right hinv).mp (by linarith : 0 ≤ UNfull n * invTw)
  calc
    remainder n A ε₁ ≤ Decomp339b.totalBudget n A ε₁ := hs
    _ ≤ (UNfull n * invTw) * Decomp339b.totalBudget n A ε₁ := le_mul_of_one_le_left ht0 hUN
    _ = UNfull n * ((n : ℝ) / log n ^ 2 * errorBracket A n ε₁) := by
      rw [mul_assoc, Decomp339b.totalBudget_normalization n A ε₁ hn1 hε₁]
    _ = UNfull n * n / log n ^ 2 * errorBracket A n ε₁ := by ring

/-- The remainder transfers to X2 when A is at least four.
Journal p. 1241 after display 33. CONDITIONAL ON h3, h4, hPhi and GRH.
No scalar endpoint sorry or original finite remainder placeholder is invoked. -/
theorem remainder_bound_large_A (h3 : Lemma3J) (h4 : PaperInputs148.Lemma4J)
    (hPhi : PaperInputs148.Lemma5PhiJ) (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hAge : 4 ≤ A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := by
  have hu : 0 ≤ UNfull n := (by norm_num : (0 : ℝ) ≤ 2 / 5).trans (two_fifths_le_UNfull n)
  exact (remainder_bound_running h3 h4 hPhi α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hc hX hn hev).trans
    (mul_le_mul_of_nonneg_left
      (EndpointCompare332.error_at_threshold α A u X₂ n ε₁ hε₁ hε₁1 hα hα1 hA hAge hc hX hn) (by positivity))

end
end LeanLab.BS2022GRH.Decomp332b
#print axioms LeanLab.BS2022GRH.Decomp332b.remainder_bound_running
#print axioms LeanLab.BS2022GRH.Decomp332b.remainder_bound_large_A
