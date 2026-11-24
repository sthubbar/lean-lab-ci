/-
Split of `leaf_section4Block_mean_value_positive_small_high` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small, burst-20261122 S84 feed1122.

The sealed leaf bounds the integral in `t` of the norm of the block Dirichlet polynomial over
the upper height range, from `x ^ (1/4)` up to `x ^ (0.45 - 2 ε / 3)`. As for the lower range,
P0069 obtains display 4.1 for the block of display 4.7 from Theorem 4 on page 12 through
Lemma 10, pages 26 and 27, and Theorem 4 bounds sums over well spaced sets of heights. This
split reuses the MEDIUM discretization leaf
`leaf_section4Block_integral_le_two_wellspaced_sums` of
SPLIT_leaf_section4Block_mean_value_positive_small_low and adds one HARD leaf, the well spaced
mean value over the upper range. The assembly
`leaf_section4Block_mean_value_positive_small_high_split` repeats the sealed statement binder
for binder and is proved from those leaves with no further sorry.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_positive_small_low

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF: the well spaced mean value for the block over the upper height range, P0069 page 12,
Theorem 4, applied on pages 26 and 27 through Lemma 10 to the factorization `M_1 N L` of the
block of display 4.7, `d` in dyadic ranges, grouping `max m n ≤ 0.46`. For every finite set
`S` of heights in `[x ^ (1/4), x ^ (0.45 - 2 ε / 3)]` with distinct points at distance at least
one, the sum over `S` of the norm of the twisted block polynomial at `1/2 + i t` is at most
`C x^{1/2} (log x)^{-A}`, uniformly in `S`, `q ≤ (log x)^A` and `χ`. Non-vacuous.
Class: HARD -/
theorem leaf_section4Block_wellspaced_positive_small_high
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ S : Finset ℝ,
            (∀ t ∈ S, x ^ (1 / 4 : ℝ) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3)) →
            (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
            ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- The assembly, with nothing open beyond the leaves: the sealed statement
`leaf_section4Block_mean_value_positive_small_high`, binder for binder, with constant `2 C`. -/
theorem leaf_section4Block_mean_value_positive_small_high_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (x ^ (1 / 4 : ℝ))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η, hη, H⟩ := leaf_section4Block_wellspaced_positive_small_high h4 B hB
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  obtain ⟨C, X, hC⟩ := H ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  refine ⟨C + C, X, ?_⟩
  intro x hx q hq hlog χ
  obtain ⟨S₁, S₂, hS₁, hS₂, hw₁, hw₂, hint⟩ :=
    leaf_section4Block_integral_le_two_wellspaced_sums _
      (s84a3_block_norm_continuous ε m n a b x q χ) (fun t => norm_nonneg _)
      (x ^ (1 / 4 : ℝ)) (x ^ (0.45 - 2 * ε / 3))
  calc _ ≤ _ := hint
    _ ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) + C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add (hC x hx q hq hlog χ S₁ hS₁ hw₁) (hC x hx q hq hlog χ S₂ hS₂ hw₂)
    _ = (C + C) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Decomp528a
