/-
Split of `energy_log_bound` in LeanLab.BHP1997.DecompC165c into leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks, for every real exponent `B`, for one exponent `K` and one positive
constant `C`, such that the coefficient energy of every Dirichlet polynomial whose
coefficients obey `‖a n‖ ≤ τ(n)^B` is at most `C * (log F)^K`, uniformly in the
coefficients and in the window `c1 F < n < c2 F`.

The split follows the shape of the estimate.

Leaf 1 replaces each `‖a n‖ ^ 2` by its divisor bound, turning the energy into the
divisor moment `Σ τ(n)^(2B) / n` over the same window.

Leaf 2 is the divisor moment in the range `B ≤ 1/2`. There the exponent `2B` is at most
one, so the divisor factor is at most `τ(n)`, and the moment is at most the sum of
`τ(n) / n` below the range, which is a square of a logarithm.

Leaf 3 is the divisor moment in the complementary range `1/2 ≤ B`. There the divisor
factor is a positive power of `τ(n)` above the first power, and the moment costs a
power of the logarithm through the product over the primes below the range.

Leaf 4 exchanges the two logarithms: `log (⌊c2 F⌋₊ + 2)` is comparable with `log F`
on the range `F ≥ 2`, and the comparison survives raising to the power `K`.

Nothing else is needed, so the assembly below has no sorry.

Every leaf is OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- LEAF 1 of 4. The coefficient step: it removes the dependence on the coefficients.
Every `‖a n‖` is replaced by the divisor bound `τ(n)^B` it obeys, and the squares and
the division by `n` are carried through term by term, so the energy of `a` on the
window is at most the divisor moment on the same window. No estimate on the moment is
asserted here.

Degenerate readings: with `c1 ≤ 0` the window may contain `n = 0`, where the
coefficient bound forces `‖a 0‖ = 0` and both sides of the term inequality are
divisions by zero and equal `0`; at `a = 0` the left side is `0`. -/
theorem leaf_energy_le_divisor_moment (a : ℕ → ℂ) (B c1 c2 F : ℝ)
    (ha : Thm4.CoeffBound a B) :
    energy a c1 c2 F ≤
      ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
          (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
        ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
  sorry

/-- LEAF 2 of 4. The divisor moment for `B ≤ 1/2`. For a fixed exponent `B ≤ 1/2` and a
fixed window scale `c2` there are an exponent `K ≥ 0` and a constant `C > 0`, both
allowed to depend on `B` and `c2`, such that the divisor moment over the whole range
below `⌊c2 F⌋₊` is at most `C * (log (⌊c2 F⌋₊ + 2))^K` for every `F ≥ 2`.

Here `2B ≤ 1`, so each divisor factor `τ(n)^(2B)` is at most `τ(n)` itself, because
`τ(n) ≥ 1` for `n ≥ 1`; the exponent `K` may be taken equal to two. This is a single
estimate on a divisor sum, with no sequence, no character and no window filter in it.

Degenerate readings: `B = 1/2` is the boundary case and is included; `B ≤ 0` is
included as well and is then a harmonic-sum estimate; at `F = 2` with `c2 ≤ 0` the
range is `{0}`, whose single term is a division by zero and equals `0`. -/
theorem leaf_divisor_moment_half (B : ℝ) (hB : B ≤ 1 / 2) (c2 : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      ∀ F : ℝ, 2 ≤ F →
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := by
  sorry

/-- LEAF 3 of 4. The divisor moment for `1/2 ≤ B`. For a fixed exponent `B ≥ 1/2` and a
fixed window scale `c2` there are `K ≥ 0` and `C > 0`, both allowed to depend on `B`
and `c2`, with the same conclusion as the previous leaf.

Here the divisor factor is a power of `τ(n)` above the first power, so the moment is no
longer a harmonic sum: it is at most the product over the primes below the range of
`1 + Σ_{k ≥ 1} (k+1)^(2B) / p^k`, and the logarithm of that product is a fixed
multiple of `log log`, hence a fixed power of the logarithm of the range. This is the
case where the exponent `K` genuinely depends on `B`.

Degenerate readings: `B = 1/2` is the boundary case and is included, so this leaf and
the previous one overlap there and must agree; the range is nonempty for `F ≥ 2` and
`c2 > 0`, and for `c2 ≤ 0` the single term is a division by zero and equals `0`, so
the leaf is not vacuous. -/
theorem leaf_divisor_moment_large (B : ℝ) (hB : 1 / 2 ≤ B) (c2 : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      ∀ F : ℝ, 2 ≤ F →
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := by
  sorry

/-- LEAF 4 of 4. The logarithmic comparison. For a fixed window scale `c2` and a fixed
exponent `K ≥ 0` there is `D > 0`, allowed to depend on `c2` and `K`, such that
`(log (⌊c2 F⌋₊ + 2))^K ≤ D * (log F)^K` for every `F ≥ 2`.

The range `⌊c2 F⌋₊` is comparable with `F` up to the fixed factor `c2 + 2` once
`F ≥ 2`, so the two logarithms differ by an additive constant, and the constant is
absorbed into `D` after raising to the power `K`; this is where `K ≥ 0` is used.

Degenerate readings: with `c2 ≤ 0` the left logarithm is `log 2` and `D = 1` works;
with `K = 0` both sides equal one and any `D > 0` works; `F = 2` is the boundary case
and is included. -/
theorem leaf_log_floor_rpow_le (c2 K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ F : ℝ, 2 ≤ F →
      Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := by
  sorry

/-- The assembly of `energy_log_bound` from the four leaves, with the sealed statement
unchanged. The two cases `B ≤ 1/2` and `1/2 ≤ B` select the second or the third leaf;
the first leaf changes the energy into the divisor moment, the fourth leaf replaces the
logarithm of the range by the logarithm of `F`, and the sum over the window filter is
bounded by the sum over the whole range because every summand is nonnegative. -/
theorem energy_log_bound_split : EnergyLogBound := by
  intro B c1 c2 hc1 hc2
  rcases le_total B (1 / 2) with hB | hB
  · obtain ⟨K, C, hK, hC, hbound⟩ := leaf_divisor_moment_half B hB c2
    obtain ⟨D, hD, hlog⟩ := leaf_log_floor_rpow_le c2 K hK
    refine ⟨K, C * D, mul_pos hC hD, ?_⟩
    intro a ha F hF
    have h1 :
        energy a c1 c2 F ≤
          ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) :=
      leaf_energy_le_divisor_moment a B c1 c2 F ha
    have h2 :
        (∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          ∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro x _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg x)
    have h3 :
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K :=
      hbound F hF
    have h4 : Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := hlog F hF
    calc energy a c1 c2 F
        ≤ C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := le_trans (le_trans h1 h2) h3
      _ ≤ C * (D * Real.log F ^ K) := mul_le_mul_of_nonneg_left h4 hC.le
      _ = C * D * Real.log F ^ K := by ring
  · obtain ⟨K, C, hK, hC, hbound⟩ := leaf_divisor_moment_large B hB c2
    obtain ⟨D, hD, hlog⟩ := leaf_log_floor_rpow_le c2 K hK
    refine ⟨K, C * D, mul_pos hC hD, ?_⟩
    intro a ha F hF
    have h1 :
        energy a c1 c2 F ≤
          ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) :=
      leaf_energy_le_divisor_moment a B c1 c2 F ha
    have h2 :
        (∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          ∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro x _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg x)
    have h3 :
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K :=
      hbound F hF
    have h4 : Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := hlog F hF
    calc energy a c1 c2 F
        ≤ C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := le_trans (le_trans h1 h2) h3
      _ ≤ C * (D * Real.log F ^ K) := mul_le_mul_of_nonneg_left h4 hC.le
      _ = C * D * Real.log F ^ K := by ring

-- Axiom audit driver for the assembly.
#print axioms energy_log_bound_split
-- The three inputs of the sealed statement, printed from the imported module.
#print LeanLab.BHP1997.DecompC165c.EnergyLogBound
#print LeanLab.BHP1997.MeanSquareC165.energy
#print LeanLab.BHP1997.Thm4.CoeffBound

end LeanLab.BHP1997.DecompC165c
