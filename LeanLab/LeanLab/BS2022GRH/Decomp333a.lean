/- AI wrote the Lean code for CODEX task333. Goldbach is open.
Exact supply for DecompJ215 without changing that sealed file.
Journal Theorem 5 pp. 1228 to 1231, display 19 and display 20.
The smaller analytic leaves already exist in the task233 and task410 supply.
This file introduces no duplicate analytic obligation. -/
import LeanLab.BS2022GRH.Slack333
import LeanLab.BS2022GRH.WeakSieve333
import LeanLab.BS2022GRH.DecompC169a
import LeanLab.BS2022GRH.Density333

namespace LeanLab.BS2022GRH.Decomp333a
open Real ChenThresholdGRH DecompC169a

/-- The positive branch follows from four independent source estimates.
Journal pp. 1229 to 1231. CONDITIONAL ON the supplied estimates.
Both the sieve estimate and the residue estimate are non-strict. -/
theorem positive_branch_of_estimates (α A u ε C₂ X : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hLX : 3200 ≤ log X)
    (hc : 0 < lowerCoefficient α ε C₂)
    (hS : sieveMain n α ε C₂ - remainder n α u ≤ (U7153.SA n : ℝ))
    (hR : remainder n α u ≤ cGJ X * n / log n ^ A)
    (hV : 8 * UNfull n / log n *
      (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ density n)
    (hCard : (n : ℝ) / log n ≤ (U7153.Aset n).card) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X n < (U7153.SA n : ℝ) := by
  exact Slack333.target_of_weak_sieve α A u ε C₂ X n hX hn hLX hc.le hS hR hV hCard

/-- Exact combination with the source estimates explicit and no hidden analytic leaf.
Journal p. 1229 and p. 1231 display 20. CONDITIONAL ON the four estimates.
Only the positive coefficient branch uses them. -/
theorem combination_of_estimates (α A u ε C₂ X : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hLX : 3200 ≤ log X)
    (hS : 0 < lowerCoefficient α ε C₂ →
      sieveMain n α ε C₂ - remainder n α u ≤ (U7153.SA n : ℝ))
    (hR : 0 < lowerCoefficient α ε C₂ → remainder n α u ≤ cGJ X * n / log n ^ A)
    (hV : 0 < lowerCoefficient α ε C₂ → 8 * UNfull n / log n *
      (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ density n)
    (hCard : 0 < lowerCoefficient α ε C₂ → (n : ℝ) / log n ≤ (U7153.Aset n).card) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X n < (U7153.SA n : ℝ) := by
  by_cases hc : 0 < lowerCoefficient α ε C₂
  · exact positive_branch_of_estimates α A u ε C₂ X n hX hn hLX hc
      (hS hc) (hR hc) (hV hc) (hCard hc)
  · exact Scalar333.target_of_coefficient_nonpos α A ε C₂ X n hX hn hLX (le_of_not_gt hc)

/-- Exact sealed leaf supplied from existing smaller written source steps.
Journal pp. 1228 to 1231. CONDITIONAL ON the existing analytic leaves.
The density path uses the prime count input and task410 finite corrections.
The original DecompJ215 leaf and its assembly are not used. -/
lemma leaf_comb (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
  (hGRH : LeanLab.DERZ1997.GRH) (hSieve : LeanLab.BS2022GRH.ChenThresholdGRH.LinearSieveT4 ε C₁ C₂)
  (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : LeanLab.BS2022GRH.ChenThresholdGRH.epsJ u ≤ ε)
  (hε0 : 0 < ε) (hε1 : ε < 1 / 63) (halpha1 : 0 < α) (halpha2 : α < 1 / 8) (hA : 0 < A) (hCond : LeanLab.BS2022GRH.ChenThresholdGRH.Cond19 α A u X₂)
  (hX2X : 4e18 ≤ X₂) (hX2N : X₂ ≤ (n : ℝ)) (hev : Even n)
  (heq : LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n = (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) *
      (2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α)
        - ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α)))
    - 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ * LeanLab.BS2022GRH.ChenThresholdGRH.invTw * LeanLab.BS2022GRH.ChenThresholdGRH.cGJ X₂ / log (n:ℝ) ^ (A - 2)) :
  8 * (LeanLab.BS2022GRH.UNfull n * n / log n ^ 2) * LeanLab.BS2022GRH.ChenThresholdGRH.B5J α A ε C₂ X₂ n < (LeanLab.BS2022GRH.U7153.SA n : ℝ) := by
  have hLX := (EndpointC169.log_endpoint_gt α A u X₂ halpha1 halpha2 hA hCond hX2X).le
  apply combination_of_estimates α A u ε C₂ X₂ n hX2X hX2N hLX
  · intro _
    have hnlog : 3200 < log (n : ℝ) :=
      (EndpointC169.log_endpoint_gt α A u X₂ halpha1 halpha2 hA hCond hX2X).trans_le
        (log_le_log (by linarith : 0 < X₂) hX2N)
    apply WeakSieve333.lower_sieve_fixed_level α u ε C₁ C₂ n hSieve heps
      hε0 hε1 halpha1 halpha2 hCond.2.2.1 hnlog hev
    intro v huv hvz
    by_cases hzlarge : exp 2753 < U7153.zz n
    · exact (DecompC169c.lemma7J _ u v hzlarge hCond.2.2.1 huv hvz).1
    · have hn0 : (0 : ℝ) < n := by linarith
      have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
      have hzlog : 400 < log (U7153.zz n) := by
        rw [U7153.zz, log_rpow hn0]
        linarith
      have hz400 : exp 400 < U7153.zz n := (lt_log_iff_exp_lt hz0).mp hzlog
      exact PublishedInputs233.small_level_product _ u v hz400 (le_of_not_gt hzlarge)
        hCond.2.2.1 huv hvz
  · intro _
    exact remainder_bound α A u X₂ n hGRH DecompC164a.lemma3J
      halpha1 halpha2 hA hCond hX2X hX2N hev
  · intro _
    exact Density333.density_lower_of_prime_count PublishedInputs232.lemma1_schoenfeld
      n hGRH (hX2X.trans hX2N) hev
      (hLX.trans (log_le_log (by linarith : 0 < X₂) hX2N))
  · intro _
    exact lower_cardinality PublishedInputs232.lemma1_schoenfeld PublishedInputs232.lemma4_robin
      n hGRH (hX2X.trans hX2N) (hLX.trans (log_le_log (by linarith : 0 < X₂) hX2N))

end LeanLab.BS2022GRH.Decomp333a

#print axioms LeanLab.BS2022GRH.Decomp333a.positive_branch_of_estimates
#print axioms LeanLab.BS2022GRH.Decomp333a.combination_of_estimates
#print axioms LeanLab.BS2022GRH.Decomp333a.leaf_comb
