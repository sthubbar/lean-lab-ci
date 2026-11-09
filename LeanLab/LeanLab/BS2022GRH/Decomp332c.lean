/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Thread a supplied finite theta cap through the Theorem 6 assembly.
Journal pp. 1231 to 1234. https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Theta332
import LeanLab.BS2022GRH.DecompC169b

namespace LeanLab.BS2022GRH.Decomp332c
open Real Finset Classical ChenThresholdGRH DecompC169b
noncomputable section

/-- The main prime sum with its finite theta cap explicit.
Journal pp. 1233 and 1234 display 24. CONDITIONAL ON existing analytic inputs.
The separate PublishedInputs232 theta placeholder is not invoked. -/
theorem main_sum_bound (h2 : PaperInputs148.Lemma2J) (α A u ε C₁ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hC₁ : 0 ≤ C₁) (he0 : 0 < ε)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    mainSum n α ε C₁ ≤
      8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
      8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1)) := by
  have hN := hX.trans hn
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hN
  have hX1 : 1 < X₂ := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have h11 : exp 11 ≤ (n : ℝ) :=
    (le_log_iff_exp_le (by linarith : (0 : ℝ) < n)).mp
      (by linarith [Lemma11C164.log_lower n hN])
  obtain ⟨hliL, hliU⟩ := PublishedInputs232.li_bounds_large n h11
  have hcard := cardinality_upper_of_inputs PublishedInputs232.lemma1_schoenfeld
    PublishedInputs232.lemma4_robin hG n hN hliL hliU
  have hd := density_at_threshold n X₂ hX hn (PublishedInputs232.density_upper n hN hev)
  have hp := prime_sum_at_threshold n α ε C₁ X₂ hX hn hev hα hα1 he0.le hC₁
  have hr := prime_residue_sum PublishedInputs232.lemma1_schoenfeld
    h2 PublishedInputs232.lemma4_robin PublishedInputs232.lemma5_mu
    h3 hG α A u X₂ n hα hα1 hA hc hX hn hev
  have hcg := (CoefficientsC169.coefficient_ranges X₂ (paper_threshold18.trans hX)).2.2.1
  exact main_sum_from_estimates n α A ε C₁ X₂ hn1 hev hX1 hα hα1 he0.le hC₁
    hcg hcard hd hp hr

/-- The exact current Theorem 6 uses the supplied Lemmas 2, 3 and 7.
Journal pp. 1231 to 1234. CONDITIONAL ON the remaining published inputs. -/
theorem thm6_of_inputs (h2 : PaperInputs148.Lemma2J) (h3 : Lemma3J) (h7 : Lemma7J) : Thm6J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  have hs : (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤
      mainSum n α ε C₁ + totalRemainder n α u := by
    unfold mainSum totalRemainder
    rw [← sum_add_distrib]
    exact sum_le_sum fun q hq => quotient_sieve α A u ε C₁ C₂ X₂ n q hG hT
      h7 hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev hq
  have hm := main_sum_bound h2 α A u ε C₁ X₂ n hG h3 hC₁ he0
    hα hα1 hA hc hX hn hev
  have hr := total_remainder_of_inputs PublishedInputs232.lemma1_schoenfeld
    h2 PublishedInputs232.lemma4_robin PublishedInputs232.lemma5_mu PublishedInputs232.lemma5_phi
    α A u X₂ n hG h3 hα hα1 hA hc hX hn hev
  change (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤ _
  calc
    _ ≤ mainSum n α ε C₁ + totalRemainder n α u := hs
    _ ≤ (8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
          8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1))) +
          8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := add_le_add hm hr
    _ = 8 * (UNfull n * n / log n ^ 2) * B6J α A ε C₁ X₂ n := by
      unfold B6J
      ring

end
end LeanLab.BS2022GRH.Decomp332c
#print axioms LeanLab.BS2022GRH.Decomp332c.main_sum_bound
#print axioms LeanLab.BS2022GRH.Decomp332c.thm6_of_inputs
