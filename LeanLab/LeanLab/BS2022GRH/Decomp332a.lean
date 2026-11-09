/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Exact supply for the sealed ChenThresholdGRH target from existing smaller leaves.
Journal pp. 1228 to 1241. No duplicate analytic obligation is introduced.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp333a
import LeanLab.BS2022GRH.DecompC164c
import LeanLab.BS2022GRH.Decomp332b
import LeanLab.BS2022GRH.Decomp332c

namespace LeanLab.BS2022GRH.Decomp332a
open Real ChenThresholdGRH DecompC169a

/-- Theorem 5 using the supplied progression and product estimates.
Journal pp. 1228 to 1231. CONDITIONAL ON existing explicit source inputs.
The prime count density path removes the independent density placeholder. -/
theorem thm5_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm5J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  have hLX := (EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX).le
  apply Decomp333a.combination_of_estimates α A u ε C₂ X₂ n hX hn hLX
  · intro _
    have hnlog : 3200 < log (n : ℝ) :=
      (EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX).trans_le
        (log_le_log (by linarith : 0 < X₂) hn)
    apply WeakSieve333.lower_sieve_fixed_level α u ε C₁ C₂ n hT heps
      he0 he1 hα hα1 hc.2.2.1 hnlog hev
    intro v huv hvz
    by_cases hzlarge : exp 2753 < U7153.zz n
    · exact (h7 _ u v hzlarge hc.2.2.1 huv hvz).1
    · have hn0 : (0 : ℝ) < n := by linarith
      have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
      have hzlog : 400 < log (U7153.zz n) := by
        rw [U7153.zz, log_rpow hn0]
        linarith
      have hz400 : exp 400 < U7153.zz n := (lt_log_iff_exp_lt hz0).mp hzlog
      exact PublishedInputs233.small_level_product _ u v hz400 (le_of_not_gt hzlarge)
        hc.2.2.1 huv hvz
  · intro _
    exact remainder_bound_of_inputs PublishedInputs232.lemma1_schoenfeld
      (Theta332.theta_of_buthe ThetaInputs224.theta_buthe_1e19)
      PublishedInputs232.lemma4_robin PublishedInputs232.lemma5_mu α A u X₂ n hG h3
      hα hα1 hA hc hX hn hev
  · intro _
    exact Density333.density_lower_of_prime_count PublishedInputs232.lemma1_schoenfeld
      n hG (hX.trans hn) hev
      (hLX.trans (log_le_log (by linarith : 0 < X₂) hn))
  · intro _
    exact lower_cardinality PublishedInputs232.lemma1_schoenfeld PublishedInputs232.lemma4_robin
      n hG (hX.trans hn) (hLX.trans (log_le_log (by linarith : 0 < X₂) hn))

/-- Theorem 7 with the product input supplied by the caller.
Journal pp. 1234 to 1241. CONDITIONAL ON the existing main and remainder leaves.
No independent Lemma 7 proof is invoked on this sieve path.
For A at least four the remainder uses the explicit bilinear input path.
For smaller positive A the original finite remainder obligation remains. -/
theorem thm7_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm7J := by
  intro α A u ε C₁ C₂ X₂ ε₁ n hG hT hC₁ hC₂ heps he0 he1 hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have hs := SliceSieve236.sieve_slices_of_inputs α A u ε C₁ C₂ X₂ ε₁ n hT
    h7 (Theta332.theta_of_buthe ThetaInputs224.theta_buthe_1e19) hC₁ heps he0 he1 hε₁ hα hα1
    hA hc hX hn hev (PublishedInputs236.density_y_upper n hG (hX.trans hn) hev)
  have hm := DecompC164c.main_at_threshold α A u ε C₁ X₂ ε₁ n hC₁ he0 hε₁ hε₁1
    hα hα1 hA hc hX hn (DecompC164c.mass_bound n ε₁ hG hε₁ hε₁1 (hX.trans hn))
  have hr : DecompC164c.remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 *
      DecompC164c.errorBracket A X₂ ε₁ := by
    by_cases hA4 : 4 ≤ A
    · exact Decomp332b.remainder_bound_large_A h3 PublishedInputs232.lemma4_robin
        PublishedInputs232.lemma5_phi α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hA4 hc hX hn hev
    · exact DecompC164c.remainder_bound α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hc hX hn hev
  calc
    (U7153.SB n : ℝ) ≤ DecompC164c.mass n ε₁ * DecompC164c.sieveCoefficient n α ε C₁ +
        DecompC164c.remainder n A ε₁ := hs
    _ ≤ UNfull n * n / log n ^ 2 * DecompC164c.mainBracket α ε C₁ X₂ ε₁ +
        UNfull n * n / log n ^ 2 * DecompC164c.errorBracket A X₂ ε₁ := add_le_add hm hr
    _ = UNfull n * n / log n ^ 2 * B7J α A ε C₁ X₂ ε₁ := by
      rw [DecompC164c.bracket_split, mul_add]

/-- Exact sealed target assembled from the existing strictly smaller source obligations.
Journal pp. 1228 to 1241. CONDITIONAL ON those obligations.
The original ChenThresholdGRH placeholder is never invoked. -/
theorem theorems567_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm5J ∧ Thm6J ∧ Thm7J := by
  exact ⟨thm5_of_inputs h3 h7, Decomp332c.thm6_of_inputs (Theta332.theta_of_buthe ThetaInputs224.theta_buthe_1e19) h3 h7, thm7_of_inputs h3 h7⟩

end LeanLab.BS2022GRH.Decomp332a
#print axioms LeanLab.BS2022GRH.Decomp332a.thm5_of_inputs
#print axioms LeanLab.BS2022GRH.Decomp332a.thm7_of_inputs
#print axioms LeanLab.BS2022GRH.Decomp332a.theorems567_of_inputs
