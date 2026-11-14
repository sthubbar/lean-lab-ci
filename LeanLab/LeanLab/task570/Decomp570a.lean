/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Supply split of Decomp115.analytic_lower_bound, pages 192 to 199.
The three analytic inputs stay open in Decomp319a; this module restates the
three steps and proves them from ten finer leaves.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp319a

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a

namespace LeanLab.Hathi2021.Decomp570a

open Decomp319a

/-- Page 193. The reduced residue exponential sum C with degree d. -/
noncomputable def residueSum (q a d : ℕ) : ℂ :=
  ∑ m ∈ (Finset.Icc 1 q).filter (fun m => Nat.Coprime m q),
    e ((a : ℝ) * (m : ℝ) ^ d / q)

/-- Page 193. The coefficient A in the prime and two prime squares singular series.
The zero denominator extension is not used in the series. -/
noncomputable def singularCoefficient (n : ℤ) (q : ℕ) : ℂ :=
  (∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
    residueSum q a 1 * residueSum q a 2 ^ 2 * e (-(a : ℝ) * n / q)) /
      (Nat.totient q : ℂ) ^ 3

/-- Page 193. The real singular series for a prime and two prime squares.
Summation starts at denominator one. -/
noncomputable def singularSeries (n : ℤ) : ℝ :=
  (∑' q : ℕ, singularCoefficient n (q + 1)).re

/-- Pages 193 and 194. The shared exponent singular mass at k equal to 82.
The tuple multiplicities come from the expansion of G to power 82.
Each residual avoids the forbidden class 2 modulo 3. -/
noncomputable def singularMass (n₁ n₂ : ℕ) : ℝ := by
  classical
  exact ∑ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
    let h : ℤ := ∑ j, (2 : ℤ) ^ (ν j).val
    let r₁ : ℤ := (n₁ : ℤ) - h
    let r₂ : ℤ := (n₂ : ℤ) - h
    if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁ ∧ 2 ≤ r₂ ∧
        r₁ % 3 ≠ 2 ∧ r₂ % 3 ≠ 2
    then singularSeries r₁ * singularSeries r₂ else 0

/-- LEAF. Hu page 193, Lemma 2.1, citing reference 2 Lemma 2.3.
This is the required shared exponent analogue of the printed average.
The printed common congruence restriction does not provide this statement.
Its validity is an open source question, not a certified cited theorem.
It contains no major arc integral. -/
theorem averaged_singular_mass (C : ℝ) (hC : 1 < C) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (566388 / 100000 : ℝ) * L n₁ ^ 82 ≤ singularMass n₁ n₂ := by
  sorry

/-- LEAF. Hu page 194, proof of Lemma 2.2, citing reference 2 Lemma 2.2.
The major arc comparison with the averaged singular mass is separated
from its arithmetic lower bound. The positive tolerance allows the
asymptotic error implicit in the displayed comparison. -/
theorem major_arc_singular_comparison (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) * singularMass n₁ n₂ -
        η * scale n₁ n₂ ≤ R1 n₁ n₂ := by
  sorry

/-- Page 194, Lemma 2.2. CONDITIONAL ON the averaged singular mass and
major arc comparison. This has the exact statement of the sealed leaf. -/
theorem major_arc_lower (C δ : ℝ) (hC : 1 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (556388 / 100000 * Real.pi ^ 2 / 16 - δ) * scale n₁ n₂ ≤ R1 n₁ n₂ := by
  obtain ⟨N₁, h₁⟩ := averaged_singular_mass C hC
  obtain ⟨N₂, h₂⟩ := major_arc_singular_comparison C δ hC hδ
  refine ⟨max N₁ N₂, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn hlt hratio
  have hm := h₁ n₁ n₂ ho₁ ho₂ ((le_max_left _ _).trans hn) hlt hratio
  have ha := h₂ n₁ n₂ ho₁ ho₂ ((le_max_right _ _).trans hn) hlt hratio
  have hc : 0 ≤ Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) := by positivity
  have hmass := mul_le_mul_of_nonneg_left hm hc
  have hs := scale_nonneg n₁ n₂
  unfold scale at *
  nlinarith [sq_nonneg Real.pi]


/-- Page 193 Lemma 2.1 and page 192 shared shifts.
The common residual congruence cannot hold for the odd pair 2t plus 3
and 2t plus 1, for any shared shift h. This is a notation obstruction. -/
theorem shared_shift_common_congruence_impossible (t h : ℤ) :
    (2 * t + 3 - h) % 3 ≠ (2 * t + 1 - h) % 3 := by
  omega

end LeanLab.Hathi2021.Decomp570a
