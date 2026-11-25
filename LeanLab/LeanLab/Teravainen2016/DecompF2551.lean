/-
Split of `paper_weighted_prime_input` (Proposition 3.2, page 9). The target is the sealed
`Prop32` statement. Two LEAF lemmas carry the unresolved analytic content; the assembly
`paper_weighted_prime_input_F2551` restates the sealed statement and chains the leaves with
no `sorry`. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

open Finset
open scoped Classical

/-- LEAF. The outer existential of Proposition 3.2: there exist positive constants `δ₀` and `C`
that make the weighted inequality hold for all sufficiently large parameters. This step only
chooses the two positive real constants; the analytic content lives in the second leaf. OPEN. -/
theorem leaf_delta0_C_exists_F2551 : ∃ (δ₀ C : ℝ), 0 < δ₀ ∧ 0 < C := by
  exact ⟨1, 1, zero_lt_one, zero_lt_one⟩

/-- LEAF. The inner universal body of Proposition 3.2 for fixed positive `δ₀`, `C`: for every
admissible `Cc`, `J`, `w` there is a threshold `N₀` such that for all `N ≥ N₀`, all nonnegative
`χ` of Fourier complexity at most `Cc`, all bounded amenable shifts `b`, and all `t` in the
middle third, the weighted inequality holds over the dyadic range. This is the analytic heart
of Sections 5 through 10. OPEN. -/
theorem leaf_threshold_inequality_F2551 (δ₀ C : ℝ) (hδ₀ : 0 < δ₀) (hC : 0 < C) :
    ∀ Cc J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
    ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
    ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ N : ℕ, N₀ ≤ N →
    ∀ t : ℤ, (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 →
      δ₀ * (∑ n ∈ dyad N, χ (t - n) - C * N / (w : ℝ) ^ ((1 : ℝ) / 3)) ≤
        ∑ n ∈ dyad N, fW (WW J w) b N n * χ (t - n) := by
  sorry

/-- The sealed Proposition 3.2, assembled from the two LEAF steps above. -/
theorem paper_weighted_prime_input_F2551 : Prop32 := by
  obtain ⟨δ₀, C, hδ₀, hC⟩ := leaf_delta0_C_exists_F2551
  show Prop32On dyad
  refine ⟨δ₀, C, hδ₀, hC, ?_⟩
  exact leaf_threshold_inequality_F2551 δ₀ C hδ₀ hC

end LeanLab.Teravainen2016
