/-
Split of `paper_dyadic_approximation_input`, the Section 11 estimate of Teravainen 2016,
arXiv 1611.08585v2, pages 44 and 45. Two LEAF lemmas follow the printed reduction: the
Vinogradov cutoff `χ₀` quoted before display (11.1), and the lower bound (11.1) for the sum of
`χ₀ (ξ p + κ)` over primes `p ∈ 𝒫`, `p ∼ N`. The assembly
`paper_dyadic_approximation_input_of_leaves` restates the sealed statement and deduces it with
no `sorry` of its own: a positive sum has a prime with `χ₀ (ξ p + κ) ≠ 0`, and the support of
`χ₀` forces `‖ξ p + κ‖ ≤ η / 2`. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

open Finset Complex
open scoped Classical

/-- LEAF: page 44, the cutoff `χ₀` chosen before display (11.1) as in the cited reference [14],
going back to Vinogradov. For each constant `C ≥ 2` there is `A₀ > 0` such that for every
`0 < η < 1` some `χ₀` satisfies `0 ≤ χ₀ ≤ 1`, `χ₀ (t) = 0` when `‖t‖ > η / 2`,
`χ₀ (t) = η / 2 + ∑_{r ≠ 0} c(r) e(r t)` with `c(r) ≪ η`, and
`∑_{|r| > R} |c(r)| ≪ R⁻¹` for `R = η⁻¹ (log η⁻¹)^C`. Class MEDIUM: a Vinogradov smoothing
with smoothness order of size `log η⁻¹`. -/
theorem leaf_vinogradov_cutoff_S11 (C : ℝ) (hC : 2 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ η : ℝ, 0 < η → η < 1 →
      ∃ (χ₀ : ℝ → ℝ) (c : ℤ → ℂ),
        (∀ t, 0 ≤ χ₀ t ∧ χ₀ t ≤ 1) ∧
        (∀ t, η / 2 < distInt t → χ₀ t = 0) ∧
        c 0 = 0 ∧ Summable (fun r => ‖c r‖) ∧
        (∀ t, (χ₀ t : ℂ) = ((η / 2 : ℝ) : ℂ) + ∑' r : ℤ, c r * exp (2 * Real.pi * I * r * t)) ∧
        (∀ r, ‖c r‖ ≤ A₀ * η) ∧
        (∑' r : ℤ, (if η⁻¹ * Real.log η⁻¹ ^ C < |(r : ℝ)| then ‖c r‖ else 0)) ≤
          A₀ / (η⁻¹ * Real.log η⁻¹ ^ C) := by
  sorry

/-- LEAF: page 45, display (11.1), equivalently (11.3), proved on pages 45 to 47 from
Theorem 6.5 applied to `L(n) = 64 n + 5` and Hypothesis 6.4 with `η = N^(-θ)` and the choices
(11.2). For a positive irrational `ξ`, real `κ` and `0 < θ < 1/80` there is a large constant
`C` such that for every `A₀ > 0` some `δ₀ > 0` gives, for infinitely many `N`, and every cutoff
`χ₀` with the properties of the previous leaf for `η = N^(-θ)`,
`∑_{p ∼ N, p ∈ 𝒫} χ₀ (ξ p + κ) ≥ δ₀ η N / (log N)^(3/2)`. Class HARD: this is the Section 11
prime approximation estimate, a type I and type II sieve argument. -/
theorem leaf_lower_bound_11_1 (ξ : ℝ) (hξ : Irrational ξ) (hξ0 : 0 < ξ)
    (κ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 80) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ A₀ : ℝ, 0 < A₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ X : ℕ, ∃ N : ℕ, max 2 X ≤ N ∧
        ∀ (χ₀ : ℝ → ℝ) (c : ℤ → ℂ),
          (∀ t, 0 ≤ χ₀ t ∧ χ₀ t ≤ 1) →
          (∀ t, (N : ℝ) ^ (-θ) / 2 < distInt t → χ₀ t = 0) →
          c 0 = 0 → Summable (fun r => ‖c r‖) →
          (∀ t, (χ₀ t : ℂ) = (((N : ℝ) ^ (-θ) / 2 : ℝ) : ℂ) +
            ∑' r : ℤ, c r * exp (2 * Real.pi * I * r * t)) →
          (∀ r, ‖c r‖ ≤ A₀ * (N : ℝ) ^ (-θ)) →
          (∑' r : ℤ, (if ((N : ℝ) ^ (-θ))⁻¹ * Real.log ((N : ℝ) ^ (-θ))⁻¹ ^ C < |(r : ℝ)|
              then ‖c r‖ else 0)) ≤
            A₀ / (((N : ℝ) ^ (-θ))⁻¹ * Real.log ((N : ℝ) ^ (-θ))⁻¹ ^ C) →
          δ₀ * (N : ℝ) ^ (-θ) * N / Real.log N ^ ((3 : ℝ) / 2) ≤
            ∑ p ∈ (Ioc N (2 * N)).filter InP, χ₀ (ξ * p + κ) := by
  sorry

/-- The sealed Section 11 input, assembled from the two LEAF steps above.
CONDITIONAL ON those leaves. -/
theorem paper_dyadic_approximation_input_of_leaves (ξ : ℝ) (hξ : Irrational ξ) (hξ0 : 0 < ξ)
    (κ θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1 / 80) :
    ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
      InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2 := by
  intro X
  obtain ⟨C, hC, hB⟩ := leaf_lower_bound_11_1 ξ hξ hξ0 κ θ hθ0 hθ1
  obtain ⟨A₀, hA₀, hA⟩ := leaf_vinogradov_cutoff_S11 C hC
  obtain ⟨δ₀, hδ₀, hN⟩ := hB A₀ hA₀
  obtain ⟨N, hXN, hsum⟩ := hN X
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hXN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hη0 : 0 < (N : ℝ) ^ (-θ) := Real.rpow_pos_of_pos (by linarith) _
  have hη1 : (N : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
  obtain ⟨χ₀, c, h01, hsupp, hc0, hsum_c, hexp, hcη, htail⟩ := hA _ hη0 hη1
  have hlow := hsum χ₀ c h01 hsupp hc0 hsum_c hexp hcη htail
  have hpos : 0 < δ₀ * (N : ℝ) ^ (-θ) * N / Real.log N ^ ((3 : ℝ) / 2) := by
    have hlog : 0 < Real.log N := Real.log_pos hN1
    have : 0 < Real.log N ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hlog _
    positivity
  have hne : ∃ p ∈ (Ioc N (2 * N)).filter InP, χ₀ (ξ * p + κ) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_eq_zero hcon] at hlow
    linarith
  obtain ⟨p, hp, hχ⟩ := hne
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨N, p, le_trans (max_le_max (by norm_num) le_rfl) hXN, hp.1.1.le, hp.1.2, hp.2, ?_⟩
  by_contra hd
  exact hχ (hsupp _ (lt_of_not_ge hd))

#print axioms paper_dyadic_approximation_input_of_leaves

end LeanLab.Teravainen2016
