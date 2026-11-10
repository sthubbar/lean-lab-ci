/- AI wrote the Lean code for CODEX task164.
Journal Theorem 7, pp. 1234 to 1241. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceModel236
import LeanLab.BS2022GRH.SliceSieveAssembly236
import LeanLab.BS2022GRH.MassAssembly236
import LeanLab.BS2022GRH.Decomp332b
namespace LeanLab.BS2022GRH.DecompC164c
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- LEAF. Sieve the disjoint slices and sum, pp. 1236 and 1237 displays 27 to 29.
Use Theorem 4, Lemma 7 and Lemma 10. The expanded divisor range increases the error. -/
theorem sieve_slices (α A u ε C₁ C₂ X₂ ε₁ : ℝ) (n : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    (U7153.SB n : ℝ) ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + remainder n A ε₁ := by
  exact SliceSieve236.sieve_slices_of_inputs α A u ε C₁ C₂ X₂ ε₁ n hT
    DecompC169c.lemma7J PublishedInputs232.lemma2_theta hC₁ heps he0 he1 hε₁ hα hα1
    hA hc hX hn hev (PublishedInputs236.density_y_upper n hG (hX.trans hn) hev)
/-- LEAF. Bound the relaxed triple count by Lemma 14, pp. 1237 to 1239.
Use Schoenfeld Corollary 1 and partial summation for both prime variables. -/
theorem mass_bound (n : ℕ) (ε₁ : ℝ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hn : exp (exp 10) ≤ (n : ℝ)) :
    mass n ε₁ ≤ massBound n ε₁ := by
  exact SliceMass236.mass_bound_of_inputs PublishedInputs232.lemma1_schoenfeld hG
    n ε₁ hn hε₁ hε₁1 (SliceMass236.pair_weight_mertens n ε₁ hn hε₁ hε₁1)
/-- LEAF. Replace the running endpoint in the main term by X2.
Theorem 7 conclusion, pp. 1235 and 1241 after display 33.
The printed Lemma 14 bracket contains a short interval term whose normalization
introduces an extra log N. AuditC164 records this scalar mismatch as a QUESTION.
This leaf needs a stronger count bound or a justified compensation, not just algebra. -/
theorem main_at_threshold (α A u ε C₁ X₂ ε₁ : ℝ) (n : ℕ)
    (hC₁ : 0 ≤ C₁) (he0 : 0 < ε) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1)
    (hα : 0 < α) (hα1 : α < 1 / 16) (hA : 0 < A)
    (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂) (hn : X₂ ≤ (n : ℝ))
    (hm : mass n ε₁ ≤ massBound n ε₁) :
    mass n ε₁ * sieveCoefficient n α ε C₁ ≤
      UNfull n * n / log n ^ 2 * mainBracket α ε C₁ X₂ ε₁ := by
  sorry
/-- LEAF. Sum the bilinear remainder, pp. 1239 to 1241 displays 31 to 33.
Use Lemma 8 for each slice and Lemmas 4 and 5 for the coprimality correction. -/
theorem remainder_bound (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := by
  by_cases hA4 : 4 ≤ A
  · exact Decomp332b.remainder_bound_large_A DecompC164a.lemma3J
      PublishedInputs232.lemma4_robin PublishedInputs232.lemma5_phi
      α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hA4 hc hX hn hev
  · sorry
/-- The sealed bracket is the sum of its main and error parts. -/
theorem bracket_split (α A ε C₁ X₂ ε₁ : ℝ) :
    B7J α A ε C₁ X₂ ε₁ = mainBracket α ε C₁ X₂ ε₁ + errorBracket A X₂ ε₁ := by
  rfl
/-- Exact sealed Thm7J, OPEN through four named leaves. No direct sorry. -/
theorem thm7J : Thm7J := by
  intro α A u ε C₁ C₂ X₂ ε₁ n hG hT hC₁ hC₂ heps he0 he1 hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have hs := sieve_slices α A u ε C₁ C₂ X₂ ε₁ n hG hT hC₁ hC₂ heps he0 he1
    hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have hm := main_at_threshold α A u ε C₁ X₂ ε₁ n hC₁ he0 hε₁ hε₁1 hα hα1 hA hc hX hn
    (mass_bound n ε₁ hG hε₁ hε₁1 (hX.trans hn))
  have hr := remainder_bound α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hc hX hn hev
  calc (U7153.SB n : ℝ)
      ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + remainder n A ε₁ := hs
    _ ≤ UNfull n * n / log n ^ 2 * mainBracket α ε C₁ X₂ ε₁ +
        UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := add_le_add hm hr
    _ = UNfull n * n / log n ^ 2 * B7J α A ε C₁ X₂ ε₁ := by
      rw [bracket_split, mul_add]
end
end LeanLab.BS2022GRH.DecompC164c
#print axioms LeanLab.BS2022GRH.DecompC164c.sieve_slices
#print axioms LeanLab.BS2022GRH.DecompC164c.mass_bound
#print axioms LeanLab.BS2022GRH.DecompC164c.main_at_threshold
#print axioms LeanLab.BS2022GRH.DecompC164c.remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC164c.bracket_split
#print axioms LeanLab.BS2022GRH.DecompC164c.thm7J
