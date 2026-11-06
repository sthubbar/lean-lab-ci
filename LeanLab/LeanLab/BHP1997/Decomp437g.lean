/-
P0069, pages 12 to 15, the exact Theorem 4 assembly with task437 supplies.
Case 1 and Case 2 i have no new analytic sorry.
The two large-third-factor leaves remain OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437h

namespace LeanLab.BHP1997.Decomp437g
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a
open scoped BigOperators

/-- Page 13, a negative diagnostic for replacing the fourth-root third-factor bound
by its square-root supremum bound in Case 2. The exponent conditions hold,
but the resulting X exponent exceeds one half. This is a route obstruction,
not a claim that a paper statement fails. -/
theorem case2_supnorm_obstruction :
    1 / 2 + (0.001 : ℝ) < 0.55 ∧ (0.55 : ℝ) < 7 / 12 ∧
    |(0.41 : ℝ) - 0.44| < 2 * 0.55 - 1 - 0.001 ∧
    1 - ((0.41 : ℝ) + 0.44) < gam 0.55 - 0.001 ∧
    (1 - (0.55 : ℝ)) + (1 - (0.41 + 0.44)) / 2 > 1 / 2 := by
  norm_num [gam]

/-- Pages 12 to 15, exact original dyadic_mean_value statement.
Use the completed Case 1 supply and the two written branches of Case 2.
Both large-third-factor leaves remain explicit dependencies.
CONDITIONAL on those OPEN leaves and the original analytic premises. -/
theorem dyadic_mean_value (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) : Thm4.Theorem4Paper := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := Decomp437a.both_dominant hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := Decomp437f.neither_dominant hmean hlarge henergy B
  obtain ⟨η2, hη2, h2⟩ := Decomp437h.first_dominant hmean hlarge henergy B
  obtain ⟨η3, hη3, h3⟩ := Decomp437h.second_dominant hmean hlarge henergy B
  refine ⟨min η0 (min η1 (min η2 η3)), by positivity, ?_⟩
  intro ε hε hεη
  have he0 : ε < η0 := lt_of_lt_of_le hεη (min_le_left _ _)
  have he1 : ε < η1 := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
  have he2 : ε < η2 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he3 : ε < η3 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε he0 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε he1 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C2, hc2⟩ := h2 ε hε he2 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C3, hc3⟩ := h3 ε hε he3 c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1 + C2 + C3, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb2 := hc2 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb3 := hc3 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_four_parts S
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1)))]
  calc
    _ ≤ C0 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C3 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
      add_le_add (add_le_add (add_le_add hb0 hb1) hb2) hb3
    _ = _ := by ring

/-- Pages 11 to 15, the exact Section 3 input on the active sieve route.
CONDITIONAL on the two cited Lemma 1 inputs, logarithmic energy,
the two large-third-factor branches. -/
theorem section3_mean_values : Thm4.Theorem4Paper := by
  exact dyadic_mean_value DecompC165c.hybrid_mean_square DecompC165c.hybrid_large_values
    DecompC165c.energy_log_bound

end LeanLab.BHP1997.Decomp437g
