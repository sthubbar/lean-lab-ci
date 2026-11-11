import LeanLab.LanguascoPintzZaccagnini2007.Growing481

/-!
Restoring the weight in P0045 displays 12 to 14 for the page 6 qualitative remark.
Only the inequality N minus M at most N is needed.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter

/-- P0045 page 6, remark after display 10, with the weighted exceptional sum of displays 12 to 14.
The singular series mass remains small after restoring its positive shifted argument. -/
theorem weighted_bad_sum_diverging481 (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) (k : ℕ) (hk : 1 ≤ k)
    (K₁ Cstar : ℕ) (hC : 0 < Cstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ E : Finset ℕ, E.card ≤ K₁ →
      (∀ r ∈ E, g X ≤ (oddRad131 r : ℝ)) →
      ∀ N ∈ evenJ131 X, ∀ B ⊆ tuples131 k X,
        (∀ ν ∈ B, ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) →
        ∑ ν ∈ B, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          ε * N * Lg X ^ k := by
  obtain ⟨X₀, hX₀⟩ := major_arcs_j2_diverging481 g hg k hk K₁ Cstar hC ε hε
  refine ⟨X₀, fun X hX E hcard hrad N hN B hB hbad => ?_⟩
  calc
    _ ≤ (N : ℝ) * ∑ ν ∈ B, Sing (N - tuplePower131 ν) := by
      rw [mul_sum]
      exact sum_le_sum fun ν _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le N (tuplePower131 ν)) (Sing_nonneg131 _)
    _ ≤ (N : ℝ) * (ε * Lg X ^ k) := mul_le_mul_of_nonneg_left
      (hX₀ X hX E hcard hrad N hN B hB hbad) (Nat.cast_nonneg _)
    _ = ε * N * Lg X ^ k := by ring

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.weighted_bad_sum_diverging481
