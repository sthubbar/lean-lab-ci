/-
Split of `LeanLab.Linnik.Decomp466a.gallagher_theorem3`.

The sealed statement is one uniform bound for the major arc frequency error at
scale `N ^ θ`, carrying an exceptional radius `r` that is either zero or one more
than the conductor of a character whose L-function has a zero in the fixed strip.
It asserts positive constants `c`, `K`, a cut-off `θ₀` in `(0, 1]`, the existence
of an admissible radius at every large `N`, and the error bound at every nonzero
frequency.

The proof step is cut into three leaves.

* `split_exceptional_radius_select`: at every large `N` a radius can be selected,
  either zero or one more than the conductor of a member of the exceptional set at
  height `(N ^ θ) ^ 5`, with no claim yet about its size.
* `split_exceptional_conductor_lt_scale`: a conductor that comes from the
  exceptional set at height `(N ^ θ) ^ 5` is already at most the scale `N ^ θ`. This
  is what makes the radius selected by the first leaf admissible in the bound.
* `split_frequency_error_bound`: the constants and the error bound for every radius
  that is at most the scale `N ^ θ`.

Assembly: `gallagher_theorem3_split`, the sealed statement, proved from the three
leaves with no sorry. The radius is chosen through the first leaf, bounded through
the second, and the error bound is applied through the third.

AI-written Lean code. Checked only by the Lean kernel. Goldbach is open.
-/
import LeanLab.Linnik.Decomp466a

namespace LeanLab.Linnik.Decomp466a

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- LEAF. The exceptional radius is selected. For every cut-off `θ₀` in `(0, 1]` and
every exponent `θ` below it, all sufficiently large `N` admit a radius `r` which is
either zero, or one more than the conductor of a character in the exceptional set at
height `(N ^ θ) ^ 5`. This is the first half of the sealed statement, with no
frequency bound and no size constraint on the conductor. -/
theorem split_exceptional_radius_select :
    ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ ≤ 1 → ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5), r = x.1 + 1) := by
  intro _ _ _ _ _ _
  exact ⟨0, fun _ _ => ⟨0, Or.inl rfl⟩⟩

/-- LEAF. The exceptional conductor is smaller than the scale. A member of the
exceptional set at height `(N ^ θ) ^ 5`, with `θ` in `(0, 1]`, has conductor one more
than its first coordinate, and that conductor is already at most `N ^ θ`. This is the
estimate that lets the selected radius enter the error bound. -/
theorem split_exceptional_conductor_lt_scale :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ,
      ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5), (x.1 : ℝ) + 1 ≤ (N : ℝ) ^ θ := by
  sorry

/-- LEAF. The frequency error bound. There are positive constants `c`, `K` and a
cut-off `θ₀` in `(0, 1]` such that for every exponent `θ` below the cut-off, every
sufficiently large `N`, every radius `r` at most the scale `N ^ θ` and every nonzero
integer frequency `n`, the complex frequency error at scale `N ^ θ` is at most `K`
times `N / log N ^ 2` times the totient weight of `n` times the sum of the main
count, the exponential error and the exceptional weight of `r`. -/
theorem split_frequency_error_bound :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, (r : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  sorry

theorem gallagher_theorem3_split :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  obtain ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, hbound⟩ := split_frequency_error_bound
  refine ⟨c, K, θ₀, hc, hK, hθ₀, hθ₁, ?_⟩
  intro θ hθ hθθ₀
  obtain ⟨N₁, hN₁⟩ := hbound θ hθ hθθ₀
  obtain ⟨N₂, hN₂⟩ := split_exceptional_radius_select θ₀ hθ₀ hθ₁ θ hθ hθθ₀
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂' : N₂ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨r, hr⟩ := hN₂ N hN₂'
  have hrle : (r : ℝ) ≤ (N : ℝ) ^ θ := by
    rcases hr with h | ⟨x, hx, hrx⟩
    · subst h
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      simpa using Real.rpow_nonneg hN0 θ
    · rw [hrx]
      push_cast
      exact split_exceptional_conductor_lt_scale θ hθ (le_trans hθθ₀ hθ₁) N x hx
  refine ⟨r, ?_, ?_⟩
  · rcases hr with h | ⟨x, hx, hrx⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, hrx, hrle⟩
  · intro n hn
    exact hN₁ N hN₁' r hrle n hn

end LeanLab.Linnik.Decomp466a
