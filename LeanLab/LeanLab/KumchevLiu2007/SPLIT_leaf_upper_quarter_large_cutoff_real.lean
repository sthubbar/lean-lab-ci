/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 as applied on
page 15, burst-20261124 S4 keep going.

Split of `SixthTwin1122.leaf_upper_quarter_large_cutoff_real`. Above the real
sixth root of the window Y a z-rough integer m below the square root of Y has
at most two prime factors, since three would give m at least z ^ 3, which is
above Y ^ (1/2). So the weighted short sum is the sum over the primes of the
window plus the sum over the composite rough integers, which are the products
of two primes at least z. The leaves state the mean square estimate for each
of the two parts separately, on the same quarter [3Y / 8, Y / 2] and under the
same hypotheses. The assembly writes the rough weight as its prime part plus
its composite part, bounds the square of a sum by twice the sum of squares and
integrates, with the helper inequality of the lower quarter file. No new definition.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_lower_quarter_large_cutoff_real

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122.UpperQuarterParts

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the prime
part of the large cut-off upper quarter: the z-rough integers of the square root
window that are prime, which are the primes at least z, on [3Y / 8, Y / 2]. -/
theorem leaf_upper_quarter_large_cutoff_prime_part (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then roughWeight z m else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4 as applied on page 15, class HARD, the
composite part of the large cut-off upper quarter: the z-rough integers of the
square root window that are not prime. Since z exceeds the real sixth root of
Y these are exactly the products of two primes at least z, on [3Y / 8, Y / 2]. -/
theorem leaf_upper_quarter_large_cutoff_two_prime_part (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (if m.Prime then 0 else roughWeight z m) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Exact statement of `SixthTwin1122.leaf_upper_quarter_large_cutoff_real`
from the prime part and the two prime part leaves. -/
theorem leaf_upper_quarter_large_cutoff_real_of_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → windowY X ε ^ ((1 : ℝ) / 6) < z →
        z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (3 * windowY X ε / 8)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_upper_quarter_large_cutoff_prime_part A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_upper_quarter_large_cutoff_two_prime_part A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  refine ⟨2 * C1 + 2 * C2, max X1 X2, by linarith, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have e1 := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have e2 := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz hz6 hzY
  have hY : 0 ≤ windowY X ε := by
    unfold windowY; exact Real.rpow_nonneg (by linarith) _
  have hsplit : ∀ m : ℕ, roughWeight z m *
      fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) =
      (if m.Prime then roughWeight z m else 0) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) +
      (if m.Prime then 0 else roughWeight z m) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro m; split_ifs <;> ring
  simp_rw [hsplit]
  refine (QuarterParts.short_sum_sq_integral_add_le _ _ _ H _ _ (by linarith)).trans ?_
  have hk : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ A =
      2 * (C1 * H ^ 2 / Real.log X ^ A) + 2 * (C2 * H ^ 2 / Real.log X ^ A) := by ring
  rw [hk]
  linarith

end LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122.UpperQuarterParts

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.SixthTwin1122.UpperQuarterParts.leaf_upper_quarter_large_cutoff_real_of_leaves
