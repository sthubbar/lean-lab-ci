import LeanLab.ChirreHagen2025.Decomp536aSplitMass

/-!
Second split of the two LEAFs of `Decomp536aSplitMass`, burst-20261122, session S123.
Ramare 2013 page 118 Lemmas 4.2 and 4.3.
`low_reciprocal_mass` is reduced to the verified Riemann hypothesis up to height
2.44 * 10 ^ 12 and the critical line form of the Lemma 4.3 sum, using the proved
identity |rho (rho - 1)| = 1/4 + gamma ^ 2 on the critical line.
`high_reciprocal_mass` is reduced to the Lemma 4.2 tail bound for the sum of
1/gamma ^ 2, using the proved bound |rho (rho - 1)| >= gamma ^ 2.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp536aSplitMassP2

/-- LEAF: Ramare 2013 page 118, the verified Riemann hypothesis input used for
Lemma 4.3: every nontrivial zero of height at most 2.44 * 10 ^ 12 lies on the
critical line. Cited computation, Platt and Trudgian 2021 verify RH up to 3 * 10 ^ 12.
Class HARD. -/
theorem verified_rh_low (z : ℂ)
    (hz : riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ 2.44 * 10 ^ 12) :
    z.re = 1 / 2 := by
  sorry

/-- LEAF: Ramare 2013 page 118 Lemma 4.3 on the critical line: the sum over all
nontrivial zeros of 1/(rho (1 - rho)) equals 2 + gamma - log 4 pi, about 0.046191,
with positive terms, which on the critical line are 1/(1/4 + gamma ^ 2); hence every
finite set of zeros on the critical line has weighted mass at most 0.0462.
Class HARD. -/
theorem critical_line_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ z.re = 1 / 2) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / (1 / 4 + z.im ^ 2)) ≤ 0.0462 := by
  apply Finset.sum_le_sum
  intro z hz
  have hz0 : riemannZeta z = 0 := (hs z hz).1
  have hzhalf : z.re = 1 / 2 := (hs z hz).2
  have hden : 0 < 1 / 4 + z.im ^ 2 := by positivity
  sorry

/-- LEAF: Ramare 2013 page 118 Lemma 4.2, the tail of the sum of 1/gamma ^ 2 over
ordinates above 2.44 * 10 ^ 12, of order log T/(pi T) by the zero counting function,
hence at most 0.0008 for every finite set of such zeros. Class HARD. -/
theorem high_inverse_square_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 2.44 * 10 ^ 12 < |z.im|) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤ 0.0008 := by
  sorry

/-- Proved: on the critical line |rho (rho - 1)| = 1/4 + gamma ^ 2. -/
theorem norm_mul_sub_one_of_re_half (z : ℂ) (h : z.re = 1 / 2) :
    ‖z * (z - 1)‖ = 1 / 4 + z.im ^ 2 := by
  have hz : z * (z - 1) = -((1 / 4 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h, sq] <;> ring
  rw [hz, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- Proved: |rho (rho - 1)| is at least the square of the ordinate. -/
theorem im_sq_le_norm_mul_sub_one (z : ℂ) : z.im ^ 2 ≤ ‖z * (z - 1)‖ := by
  rw [norm_mul]
  have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h2 : |z.im| ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simpa using this
  have : |z.im| * |z.im| ≤ ‖z‖ * ‖z - 1‖ :=
    mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs z.im]

/-- Exact statement of `Decomp536aSplitMass.low_reciprocal_mass`.
CONDITIONAL ON `verified_rh_low` and `critical_line_mass`. -/
theorem low_reciprocal_mass_of_leaves (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ 2.44 * 10 ^ 12) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.0462 := by
  have heq : (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) =
      ∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / (1 / 4 + z.im ^ 2) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul_sub_one_of_re_half z (verified_rh_low z (hs z hz))]
  rw [heq]
  exact critical_line_mass s (fun z hz => ⟨(hs z hz).1, verified_rh_low z (hs z hz)⟩)

/-- Exact statement of `Decomp536aSplitMass.high_reciprocal_mass`.
CONDITIONAL ON `high_inverse_square_mass`. -/
theorem high_reciprocal_mass_of_leaves (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 2.44 * 10 ^ 12 < |z.im|) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.0008 := by
  refine le_trans ?_ (high_inverse_square_mass s hs)
  apply Finset.sum_le_sum
  intro z hz
  have hpos : 0 < z.im ^ 2 := by
    have := (hs z hz).2.2.2
    have : 0 < |z.im| := lt_trans (by norm_num) this
    rw [← sq_abs]
    exact pow_pos this 2
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos (im_sq_le_norm_mul_sub_one z)

end LeanLab.ChirreHagen2025.Decomp536aSplitMassP2

#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP2.norm_mul_sub_one_of_re_half
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP2.im_sq_le_norm_mul_sub_one
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP2.low_reciprocal_mass_of_leaves
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP2.high_reciprocal_mass_of_leaves
