import LeanLab.ChirreHagen2025.Decomp536a

/-!
Split of `Decomp536a.verified_reciprocal_mass`, burst-20261122, session S88.
Ramare 2013 page 118 Lemma 4.3, Lemma 4.2 and the first estimate after equation 5.1.
The finite zero set is cut at the verified height 2.44 * 10 ^ 12: the low part is
bounded by the full reciprocal mass 2 + gamma - log 4 pi, about 0.04619, and the
high part by the Lemma 4.2 tail.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp536aSplitMass

/-- LEAF: Ramare 2013 page 118 Lemma 4.3 with the verified zeros, the low-height
reciprocal mass. Every finite set of nontrivial zeros of height at most
2.44 * 10 ^ 12 has multiplicity weighted reciprocal mass at most 0.0462, since the full
sum over all nontrivial zeros of the real part of 1/(rho (1 - rho)) equals
2 + gamma - log 4 pi, all its terms are positive, and on the critical line that real
part equals 1/|rho (rho - 1)|. Class HARD. -/
theorem low_reciprocal_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ 2.44 * 10 ^ 12) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.0462 := by
  sorry

/-- LEAF: Ramare 2013 page 118 Lemma 4.2, the tail of the reciprocal mass above the
verified height. Since |rho (rho - 1)| is at least the square of the ordinate, and the
zero counting function gives a sum of 1/gamma^2 over ordinates above T of order
log T / T, every finite set of nontrivial zeros above height 2.44 * 10 ^ 12 has weighted
reciprocal mass at most 0.0008. Class HARD. -/
theorem high_reciprocal_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 2.44 * 10 ^ 12 < |z.im|) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.0008 := by
  sorry

/-- Exact parent statement `Decomp536a.verified_reciprocal_mass`.
CONDITIONAL ON the two LEAFs above. -/
theorem verified_reciprocal_mass_of_leaves (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.047 := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun z : ℂ => |z.im| ≤ 2.44 * 10 ^ 12)]
  have h1 := low_reciprocal_mass (s.filter (fun z : ℂ => |z.im| ≤ 2.44 * 10 ^ 12))
    (fun z hz => by
      rw [Finset.mem_filter] at hz
      exact ⟨(hs z hz.1).1, (hs z hz.1).2.1, (hs z hz.1).2.2, hz.2⟩)
  have h2 := high_reciprocal_mass (s.filter (fun z : ℂ => ¬ |z.im| ≤ 2.44 * 10 ^ 12))
    (fun z hz => by
      rw [Finset.mem_filter] at hz
      exact ⟨(hs z hz.1).1, (hs z hz.1).2.1, (hs z hz.1).2.2, lt_of_not_ge hz.2⟩)
  linarith

end LeanLab.ChirreHagen2025.Decomp536aSplitMass
