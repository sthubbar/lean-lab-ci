/-
P0029 Bhowmik and Grimmelt 2026, arXiv 2607.27282, Section 7.4, pages 28 and 29.
Split of `leaf_pole_pole_S10` from S10_prop75merged.lean into two LEAFs:

* `leaf_pole_integral_S10`, display 7.20 page 29 at `ρ₁ = ρ₂ = 1` with `B_φ(1, 1) = 1` by
  display 7.1: `I_q^φ(N; 1, 1) = N + O_A(N ^ (-A))`, summed against `A_q(N; χ₀, χ₀)`, `q ≤ R`.
* `leaf_singular_tail_S10`, the tail `q > R` of the singular series, display 7.17 page 28:
  `N Σ_{q ≤ R} A_q(N; χ₀, χ₀) - N 𝔖(N)` in mean square.

`pole_pole_from_leaves_S10` is the exact statement of `leaf_pole_pole_S10`, without sorry from
the two leaves. No new definitions.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.S10_prop75merged

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

/-- LEAF: display 7.20 page 29, Lemma 7.6, at `ρ₁ = ρ₂ = 1`, with `B_φ(1, 1) = 1` from
display 7.1 page 26, inserted into the pole pole sum of page 28. Class MEDIUM. Pointwise
`I_q^φ(N; 1, 1) = N B_φ(1, 1) + O_A(N ^ (-A))` for `1 ≤ T_q ≤ N`; the error times
`Σ_{q ≤ R} |A_q(N; χ₀, χ₀)|` is small in mean square. -/
theorem leaf_pole_integral_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          (N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF: the tail `q > R` of the singular series in the main term `N 𝔖(N)` of display 7.17
page 28, with `A_q(N; χ₀, χ₀) = μ(q)² c_q(N) / φ(q)²` from display 6.4 page 23 and the
singular series 2.9 page 6. Class MEDIUM. -/
theorem leaf_singular_tail_S10 (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1) -
          N * singular N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- Assembly, without sorry: the exact statement of `leaf_pole_pole_S10` from
`leaf_pole_integral_S10` and `leaf_singular_tail_S10`, by `P - N 𝔖 = (P - N Σ A) + (N Σ A - N 𝔖)`. -/
theorem pole_pole_from_leaves_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          N * singular N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  have h := ms_add4_S10
    (fun X N => polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          (N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1))
    (fun X N => (N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1) -
          N * singular N)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun X => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5)
    (by obtain ⟨C, hC⟩ := leaf_pole_integral_S10 ϕ G hϕ hG ϑ hϑ0 hϑ
        exact ⟨C, fun X hX => by simpa [mul_assoc] using hC X hX⟩)
    (by obtain ⟨C, hC⟩ := leaf_singular_tail_S10 ϑ hϑ0 hϑ
        exact ⟨C, fun X hX => by simpa [mul_assoc] using hC X hX⟩)
    ⟨0, fun X _ => by simp⟩ ⟨0, fun X _ => by simp⟩
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun X hX => ?_⟩
  have := hC X hX
  simp only [add_zero] at this
  calc _ = ∑ N ∈ Finset.Icc 1 X,
        ‖(polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          (N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1)) +
         ((N : ℂ) * ∑ q ∈ Finset.range ⌊(X : ℝ) ^ ϑ⌋₊, Aq chi1 chi1 N (q + 1) -
          N * singular N)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun N _ => ?_
          congr 2; ring
    _ ≤ _ := by linarith [this]

#print axioms leaf_pole_integral_S10
#print axioms leaf_singular_tail_S10
#print axioms pole_pole_from_leaves_S10

end LeanLab.BhowmikGrimmelt2026
