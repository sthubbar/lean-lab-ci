/- AI wrote this Lean code for CODEX task169.
Theorem 6, journal pp. 1231 to 1234. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.DecompC169b
open Real Finset Classical ChenThresholdGRH DecompC169a
noncomputable section

/-- The primes q in the sum of Theorem 6, p. 1231. -/
def qRange (n : ℕ) : Finset ℕ := (U7153.Qset n).filter (fun q => ¬ q ∣ n)

/-- The cardinality of A_q, journal p. 1232. -/
def aqCard (n q : ℕ) : ℝ := (((U7153.Aset n).filter (fun a => q ∣ a)).card : ℝ)

/-- The quotient level D_q, p. 1232 display 22. -/
def quotientLevel (n q : ℕ) (α : ℝ) : ℝ := (n : ℝ) ^ (1 / 2 - α) / q

/-- The sieve parameter s_q, p. 1232 display 22. -/
def quotientParameter (n q : ℕ) (α : ℝ) : ℝ :=
  log (quotientLevel n q α) / log (U7153.zz n)

/-- The upper sieve coefficient at s_q, p. 1232 display 22. -/
def upperCoefficient (n q : ℕ) (α ε C₁ : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant / quotientParameter n q α +
    ε * C₁ * exp 2 * hS (quotientParameter n q α)

/-- The error r_q at d, p. 1232 display 22. -/
def quotientResidue (n q d : ℕ) : ℝ :=
  aqCard n (q * d) - aqCard n q / (d.totient : ℝ)

/-- The squarefree divisors below QD_q, p. 1232 display 22. -/
def quotientDivisors (n q : ℕ) (α u : ℝ) : Finset ℕ :=
  ((primesBelow n (U7153.zz n)).powerset.image (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < smallProduct n u * quotientLevel n q α)

/-- The error sum R_q, p. 1232 display 22. -/
def quotientRemainder (n q : ℕ) (α u : ℝ) : ℝ :=
  ∑ d ∈ quotientDivisors n q α u, |quotientResidue n q d|

/-- The total error in display 23, p. 1232. -/
def totalRemainder (n : ℕ) (α u : ℝ) : ℝ :=
  ∑ q ∈ qRange n, quotientRemainder n q α u

/-- The weighted cardinality sum in display 23 before bounding V, p. 1232. -/
def mainSum (n : ℕ) (α ε C₁ : ℝ) : ℝ :=
  ∑ q ∈ qRange n, upperCoefficient n q α ε C₁ * density n * aqCard n q

/-- LEAF. Apply the upper linear sieve separately to A_q, p. 1232 display 22.
Use the same V and Q as in Theorem 5. Non-strict inequality suffices here.
The source range of Lemma 7 remains a review obligation on the full sealed domain. -/
theorem quotient_sieve (α A u ε C₁ C₂ X₂ : ℝ) (n q : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : epsJ u ≤ ε)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) (hq : q ∈ qRange n) :
    (U7153.SAq n q : ℝ) ≤
      upperCoefficient n q α ε C₁ * density n * aqCard n q +
        quotientRemainder n q α u := by
  sorry

/-- LEAF. Sum the main terms using display 24 and partial summation, pp. 1233 and 1234.
Use Lemma 11 for A, Lemma 13 for r at q, and the reciprocal prime estimates on p. 1234.
The l1 term contains the integral and endpoint correction. The l3 term contains r at q. -/
theorem main_sum_bound (α A u ε C₁ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hC₁ : 0 ≤ C₁) (he0 : 0 < ε)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    mainSum n α ε C₁ ≤
      8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
      8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1)) := by
  sorry

/-- LEAF. Sum R_q using the injective qd indexing, p. 1233 after display 23.
Use Lemmas 5 and 13 and the identity for r_q to obtain the l2 contribution.
The absolute value estimate is independent of the sign chosen in the residue identity. -/
theorem total_remainder_bound (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    totalRemainder n α u ≤
      8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := by
  sorry

/-- The exact existing Thm6J from the three named leaves. All analytic leaves stay OPEN. -/
theorem thm6J_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm6J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  have hs : (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤
      mainSum n α ε C₁ + totalRemainder n α u := by
    unfold mainSum totalRemainder
    rw [← sum_add_distrib]
    exact sum_le_sum fun q hq => quotient_sieve α A u ε C₁ C₂ X₂ n q hG hT
      h7 hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev hq
  have hm := main_sum_bound α A u ε C₁ X₂ n hG h3 hC₁ he0
    hα hα1 hA hc hX hn hev
  have hr := total_remainder_bound α A u X₂ n hG h3
    hα hα1 hA hc hX hn hev
  change (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤ _
  calc
    _ ≤ mainSum n α ε C₁ + totalRemainder n α u := hs
    _ ≤ (8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
          8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1))) +
          8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := add_le_add hm hr
    _ = 8 * (UNfull n * n / log n ^ 2) * B6J α A ε C₁ X₂ n := by
      unfold B6J
      ring

/-- Exact Thm6J using the decomposed reciprocal estimates and task164 progression input. -/
theorem thm6J : Thm6J :=
  thm6J_of_inputs DecompC164a.lemma3J DecompC169c.lemma7J

end
end LeanLab.BS2022GRH.DecompC169b

#print axioms LeanLab.BS2022GRH.DecompC169b.quotient_sieve
#print axioms LeanLab.BS2022GRH.DecompC169b.main_sum_bound
#print axioms LeanLab.BS2022GRH.DecompC169b.total_remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC169b.thm6J

#print axioms LeanLab.BS2022GRH.DecompC169b.thm6J_of_inputs
