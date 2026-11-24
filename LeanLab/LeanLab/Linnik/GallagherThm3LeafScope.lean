/-
Scope check of the two open leaves of `LeanLab/Linnik/SPLIT_gallagher_theorem3.lean`.

Gallagher 1975 P0094 p.127 Theorem 3 keeps the quoted exceptional term only for an exceptional
zero at height `T = P ^ 5` whose conductor is at most `P`, and takes `r ≤ P` as a restriction,
not as a derived bound. The OFF ROUTE split in `SPLIT_gallagher_theorem3.lean` quantifies its
third leaf `split_frequency_error_bound` over every radius `r ≤ N ^ θ`, including `r = 0`.
Because the exceptional weight is nonnegative and vanishes at `r = 0`, that leaf is exactly
equivalent to its `r = 0` instance: the Theorem 3 bound with no exceptional term at all, at every
large `N`. That is stronger than the printed theorem, which needs the exceptional term whenever an
exceptional zero is present. This file proves that equivalence. It is a scope statement, not a
counterexample: no exceptional zero is known, so the leaf is not refuted.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.SPLIT_gallagher_theorem3

namespace LeanLab.Linnik.Decomp466a

open LeanLab.Linnik.Decomp1532b (excSet)

/-- Gallagher 1975 p.127 Theorem 3. The quoted exceptional weight is zero at radius zero. -/
theorem exceptionalWeight_zero (n : ℤ) : exceptionalWeight 0 n = 0 := by
  simp [exceptionalWeight]

/-- Gallagher 1975 p.127 Theorem 3. The quoted exceptional weight is nonnegative. -/
theorem exceptionalWeight_nonneg (r : ℕ) (n : ℤ) : 0 ≤ exceptionalWeight r n := by
  unfold exceptionalWeight
  positivity

/-- Gallagher 1975 p.127 Theorem 3. The totient weight is nonnegative. -/
theorem totientWeight_nonneg' (n : ℤ) : 0 ≤ totientWeight n := by
  unfold totientWeight
  positivity

/-- Scope of the third leaf of the OFF ROUTE split of Gallagher 1975 p.127 Theorem 3.
The leaf `split_frequency_error_bound`, quantified over every radius `r ≤ N ^ θ`, is
equivalent to the same bound with the exceptional term deleted. So it asserts the Theorem 3
error bound with no exceptional term, which the printed theorem does not give.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem split_frequency_error_bound_iff_no_exceptional_term :
    (∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, (r : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n)) ↔
    (∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ))) := by
  constructor
  · rintro ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, h⟩
    refine ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, ?_⟩
    intro θ hθ hθθ₀
    obtain ⟨N₀, hN₀⟩ := h θ hθ hθθ₀
    refine ⟨N₀, fun N hN n hn => ?_⟩
    have hr : ((0 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ := by
      simpa using Real.rpow_nonneg (Nat.cast_nonneg N) θ
    simpa [exceptionalWeight_zero] using hN₀ N hN 0 hr n hn
  · rintro ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, h⟩
    refine ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, ?_⟩
    intro θ hθ hθθ₀
    obtain ⟨N₀, hN₀⟩ := h θ hθ hθθ₀
    refine ⟨N₀, fun N hN r _ n hn => le_trans (hN₀ N hN n hn) ?_⟩
    have hA : 0 ≤ K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n := by
      have h1 : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg hK.le h1) (totientWeight_nonneg' n)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (exceptionalWeight_nonneg r n)) hA

/-- Scope of the second leaf of the OFF ROUTE split of Gallagher 1975 p.127 Theorem 3.
At `θ = 1` the leaf `split_exceptional_conductor_lt_scale` says that every member of the
exceptional set at height `N ^ 5` has conductor at most `N`. Gallagher p.127 and p.131 impose
`r ≤ P` as a restriction on the quoted term; the definition of `excSet` admits conductors up to
the height itself, so this is a claim about the location of exceptional zeros, not a step of
the printed proof.
AI wrote the Lean code. Binary Goldbach is open. -/
theorem split_exceptional_conductor_lt_scale_at_one
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ,
      ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5), (x.1 : ℝ) + 1 ≤ (N : ℝ) ^ θ)
    (N : ℕ) : ∀ x ∈ excSet exceptionalStrip ((N : ℝ) ^ 5), (x.1 : ℝ) + 1 ≤ (N : ℝ) := by
  intro x hx
  have := h 1 one_pos le_rfl N x (by simpa using hx)
  simpa using this

end LeanLab.Linnik.Decomp466a

#print axioms LeanLab.Linnik.Decomp466a.split_frequency_error_bound_iff_no_exceptional_term
#print axioms LeanLab.Linnik.Decomp466a.split_exceptional_conductor_lt_scale_at_one
