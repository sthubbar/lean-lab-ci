/-
KEEP GOING split of `SplitS5LuZerosFinite.leaf_mass39_sum`, CLOUD S5 burst-20261127, unit S5-01c.

P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010) 2359-2392,
p. 2369 display (39), from the density estimate (38), which Lu states for `1/2 ≤ α ≤ 1` only.

The usual method behind (39) treats the zeros with `β ≥ 1/2` by (38) and partial summation, and
the zeros with `β < 1/2` trivially, since then `N^(β-1) ≤ N^(-1/2)` and there are `≪ N^(1/2)` of
them.  This file states those two pieces as LEAFs and proves the assembly.

AI wrote this Lean code.  Binary Goldbach is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_01b_finite

namespace LeanLab.ExceptionalSet.SplitS5LuZerosHalves
open LeanLab.ExceptionalSet
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open LeanLab.ExceptionalSet.SplitS5LuZeros

/-- LEAF: Lu 2010, p. 2369, the step from (38) to (39) for the zeros with `β ≥ 1/2`. HARD.
`Σ_{q ≤ P} Σ*_{χ mod q} Σ_{|γ| ≤ 4πN/(qQ), β ≥ 1/2} N^(β-1) ≪ 1`, by partial summation over `β`
from the density estimate (38), `Σ_{q ≤ x} N*(α, T, q) ≪ (x²T)^((12/5+ε)(1-α))`, of Huxley and
Jutila, applied dyadically in `q`; for `q ~ x` one has `x² · 4πN/(xQ) ≪ P N^(1/4) = N^0.3715`. -/
theorem leaf_mass39_upper_half :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ x ∈ (luFamilyH height39 N).filter (fun x => (1 / 2 : ℝ) ≤ x.rho.re),
        weight N x.rho ≤ C := by
  sorry

/-- LEAF: the zero count behind the trivial part of (39). MEDIUM.
The number of zeros, with multiplicity, of `L(s, χ)`, `χ` primitive of modulus `q ≤ P`,
`0 < β < 1`, `|γ| ≤ 4πN/(qQ)`, is `≪ N^(1/2)`.  By the classical bound
`N(T, χ) ≪ T log(q(T + 2))` for `T ≥ 1`, see [12] or Davenport Ch. 16, the count is
`≪ Σ_{q ≤ P} q · N^(1/4)/q · log N ≪ P N^(1/4) log N = N^(0.3715) log N`. -/
theorem leaf_zero_count_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ((luFamilyH height39 N).card : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := by
  sorry

/-- `leaf_mass39_sum` of `SplitS5LuZerosFinite`, statement verbatim, from the two halves:
zeros with `β < 1/2` have weight at most `N^(-1/2)`. -/
theorem leaf_mass39_sum_of_leaves :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ x ∈ luFamilyH height39 N, weight N x.rho ≤ C := by
  obtain ⟨C1, hC1, N1, h1⟩ := leaf_mass39_upper_half
  obtain ⟨C2, hC2, N2, h2⟩ := leaf_zero_count_sqrt
  refine ⟨C1 + C2, by linarith, max (max N1 N2) 1, fun N hN => ?_⟩
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not (luFamilyH height39 N)
    (fun x => (1 / 2 : ℝ) ≤ x.rho.re)]
  have hlow : ∑ x ∈ (luFamilyH height39 N).filter (fun x => ¬ (1 / 2 : ℝ) ≤ x.rho.re),
      weight N x.rho ≤ C2 := by
    calc ∑ x ∈ (luFamilyH height39 N).filter (fun x => ¬ (1 / 2 : ℝ) ≤ x.rho.re), weight N x.rho
        ≤ ∑ x ∈ (luFamilyH height39 N).filter (fun x => ¬ (1 / 2 : ℝ) ≤ x.rho.re),
            (N : ℝ) ^ (-(1 / 2) : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [Finset.mem_filter] at hx
          unfold weight
          exact Real.rpow_le_rpow_of_exponent_le hNone (by linarith [not_le.mp hx.2])
      _ = (((luFamilyH height39 N).filter (fun x => ¬ (1 / 2 : ℝ) ≤ x.rho.re)).card : ℝ) *
            (N : ℝ) ^ (-(1 / 2) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((luFamilyH height39 N).card : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ C2 * (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ) :=
          mul_le_mul_of_nonneg_right (h2 N hN2) (by positivity)
      _ = C2 := by
          rw [mul_assoc, ← Real.rpow_add hNpos]
          norm_num
  linarith [h1 N hN1]

example : type_of% @LeanLab.ExceptionalSet.SplitS5LuZerosFinite.leaf_mass39_sum :=
  leaf_mass39_sum_of_leaves

end LeanLab.ExceptionalSet.SplitS5LuZerosHalves

#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosHalves.leaf_mass39_sum_of_leaves
