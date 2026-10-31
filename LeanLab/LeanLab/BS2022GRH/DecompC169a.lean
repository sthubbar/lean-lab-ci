/- AI wrote this Lean code for CODEX task169.
Theorem 5, journal pp. 1228 to 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp138
import LeanLab.BS2022GRH.DecompC164a
import LeanLab.BS2022GRH.EndpointC169
import LeanLab.BS2022GRH.DecompC169c

namespace LeanLab.BS2022GRH.DecompC169a
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The primes in P below x, journal p. 1227. -/
def primesBelow (n : ℕ) (x : ℝ) : Finset ℕ :=
  (range ⌈x⌉₊).filter (fun p => p.Prime ∧ ¬ p ∣ n ∧ (p : ℝ) < x)

/-- The small prime product Q in the proof of Theorem 5, p. 1229. -/
def smallProduct (n : ℕ) (u : ℝ) : ℕ := ∏ p ∈ primesBelow n u, p

/-- The density V at z, journal pp. 1227 and 1229. -/
def density (n : ℕ) : ℝ :=
  ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p : ℝ) - 1))

/-- The residue error r of Theorem 5, journal p. 1229. -/
def residue (n d : ℕ) : ℝ :=
  (((U7153.Aset n).filter (fun a => d ∣ a)).card : ℝ) -
    ((U7153.Aset n).card : ℝ) / (d.totient : ℝ)

/-- The squarefree divisors d of P at z with d less than QD, p. 1229. -/
def sieveDivisors (n : ℕ) (α u : ℝ) : Finset ℕ :=
  ((primesBelow n (U7153.zz n)).powerset.image (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < smallProduct n u * (n : ℝ) ^ (1 / 2 - α))

/-- The sum of absolute residue errors in the lower sieve, p. 1229. -/
def remainder (n : ℕ) (α u : ℝ) : ℝ :=
  ∑ d ∈ sieveDivisors n α u, |residue n d|

/-- The lower sieve coefficient at s equal to 4 minus 8 alpha, p. 1229. -/
def lowerCoefficient (α ε C₂ : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α) -
    ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α))

/-- The main term before bounding V and the cardinality, p. 1229. -/
def sieveMain (n : ℕ) (α ε C₂ : ℝ) : ℝ :=
  lowerCoefficient α ε C₂ * density n * ((U7153.Aset n).card : ℝ)

/-- LEAF. First lower sieve inequality of Theorem 5, p. 1229 after display 19.
Construct the finite sequence and apply Theorem 4 and Lemma 7.
The strict inequality needs a strict density or cardinality step because the lab
LinearSieveT4 records non-strict inequalities. The small z source range also needs review. -/
theorem sieve_lower (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : epsJ u ≤ ε)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    sieveMain n α ε C₂ - remainder n α u < (U7153.SA n : ℝ) := by
  sorry

/-- LEAF. Bound the lower sieve remainder by Lemmas 12 and 13, p. 1231 display 20.
Use Lemma 3, the squarefree modulus count in Lemma 5 and QD at most H on p. 1229. -/
theorem remainder_bound (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n α u ≤ cGJ X₂ * n / log n ^ A := by
  sorry

/-- LEAF. Main term and endpoint comparisons in Theorem 5, pp. 1228 and 1229.
Use Lemmas 10 and 11 and monotonicity of the endpoint factors.
The conclusion retains the weaker error normalization of the exact lab B5J.
Treat a negative lower coefficient separately before multiplying density bounds. -/
theorem endpoint_comparison (α A u ε C₂ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (hC₂ : 0 ≤ C₂) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hA : 0 < A) (hc : Cond19 α A u X₂)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ)) (hev : Even n)
    (hcoef : 0 ≤ lowerCoefficient α ε C₂) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n ≤
      sieveMain n α ε C₂ - cGJ X₂ * n / log n ^ A := by
  sorry

/-- LEAF. Positivity guards for the endpoint comparison, pp. 1228 and 1229 display 19.
Use the exponential part of condition 19 to bound log X2 below 3200.
The qG sign follows from its explicit formula or the nonnegative absolute error in Lemma 3. -/
theorem endpoint_factors (α A u X₂ : ℝ) (hG : GRH) (h3 : Lemma3J)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂) :
    0 < 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ) ∧ 0 ≤ cGJ X₂ := by
  have hL := EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX
  have hX0 : 0 < X₂ := by linarith
  exact ⟨EndpointC169.density_factor_pos X₂ hX0 hL.le,
    EndpointC169.cGJ_nonneg X₂ hX0 (by linarith)⟩

/-- The negative coefficient case is scalar algebra, Theorem 5 p. 1228.
The density factor and cG sign guards are explicit to avoid a false low-endpoint claim. -/
theorem negative_coefficient (α A ε C₂ X₂ : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ))
    (hdelta : 0 < 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))
    (hcg : 0 ≤ cGJ X₂) (hcoef : lowerCoefficient α ε C₂ < 0) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n < (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := by linarith
  have hlog : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hscale : 0 < 8 * (UNfull n * n / log n ^ 2) := by positivity
  have hInv : 0 ≤ invTw := by
    unfold invTw
    exact inv_nonneg.mpr (mul_nonneg (exp_pos _).le LeanLab.ChenExplicit.twinC_pos.le)
  have herr : 0 ≤ 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ *
      invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2) := by positivity
  have hmain := mul_neg_of_pos_of_neg hdelta hcoef
  have hbracket : B5J α A ε C₂ X₂ n < 0 := by
    unfold B5J
    change (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) * lowerCoefficient α ε C₂ - _ < 0
    linarith
  exact (mul_neg_of_pos_of_neg hscale hbracket).trans_le (Nat.cast_nonneg _)

/-- The exact existing Thm5J, OPEN through the four leaves and reused C164 inputs. -/
theorem thm5J_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm5J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  by_cases hcoef : 0 ≤ lowerCoefficient α ε C₂
  · have hs := sieve_lower α A u ε C₁ C₂ X₂ n hG hT h7
      hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
    have hr := remainder_bound α A u X₂ n hG h3
      hα hα1 hA hc hX hn hev
    have hm := endpoint_comparison α A u ε C₂ X₂ n hG hC₂ he0 he1 hα hα1 hA hc hX hn hev hcoef
    exact lt_of_le_of_lt (hm.trans (sub_le_sub_left hr _)) hs
  · obtain ⟨hd, hcg⟩ := endpoint_factors α A u X₂ hG h3 hα hα1 hA hc hX
    exact negative_coefficient α A ε C₂ X₂ n hX hn hd hcg (lt_of_not_ge hcoef)

/-- Exact Thm5J using the decomposed reciprocal estimates and task164 progression input. -/
theorem thm5J : Thm5J :=
  thm5J_of_inputs DecompC164a.lemma3J DecompC169c.lemma7J

end
end LeanLab.BS2022GRH.DecompC169a

#print axioms LeanLab.BS2022GRH.DecompC169a.sieve_lower
#print axioms LeanLab.BS2022GRH.DecompC169a.remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC169a.endpoint_comparison
#print axioms LeanLab.BS2022GRH.DecompC169a.thm5J

#print axioms LeanLab.BS2022GRH.DecompC169a.negative_coefficient

#print axioms LeanLab.BS2022GRH.DecompC169a.endpoint_factors

#print axioms LeanLab.BS2022GRH.DecompC169a.thm5J_of_inputs
