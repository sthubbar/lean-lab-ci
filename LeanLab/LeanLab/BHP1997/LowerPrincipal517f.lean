/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". This file splits that consequence for the E2 and E4 sums of display 5.15 into its
two uses of the prime number theorem:

* the rough cofactor `n3`, or `n5`, of display 5.15 has the Buchstab local density, uniformly in
  the level, with every log power saved, `leaf_rough_interval_density`;
* the outer primes `p1 p2`, or `p1 p2 p3 p4`, summed against that density give the E2, or E4,
  integral of page 51 with `1` replaced by `s`, `leaf_two_density_main` and
  `leaf_four_density_main`.

Burst p3: the first is PROVED in `RoughDensity517e`; the other two are CONDITIONAL ON the open
Riemann sum leaves of `TwoDensityMain517b` and `FourDensityMain517`.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.RoughFamily514
import LeanLab.BHP1997.RoughDensity517e
import LeanLab.BHP1997.TwoDensityMain517
import LeanLab.BHP1997.FourDensityMain517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", applied to the rough variable `n3` or `n5` of display 5.15, page 50. The integers of
an interval `(a, b]` with no prime factor below `z`, where `z ≥ X ^ c` and `b ≤ X`, have local
density `ω(log n / log z) / log z` with every log power saved: each such integer is a product of
at most `1 / c` primes, the prime number theorem with error term is applied to each prime, and
the Buchstab identity sums the resulting densities. -/
theorem leaf_rough_interval_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.log X ^ (-A) := by
  exact rough_interval_density ω hω hz hc A hA

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", applied to the outer primes `p1`, `p2` of the E2 sum of display 5.15. With the rough
cofactor `n3 = m / (p1 p2)` replaced by its Buchstab density at level `p2`, the sum over prime
pairs with exponents in E2 has local density `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) /
(β1 β2^2)` at `m = Z^s`, with every log power saved on every prefix of J. -/
theorem leaf_two_density_main (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact two_density_main ω hω hz hε hε8

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", applied to the outer primes `p1`, `p2`, `p3`, `p4` of the E4 sum of display 5.15.
With the rough cofactor `n5 = m / (p1 p2 p3 p4)` replaced by its Buchstab density at level `p4`,
the sum over prime quadruples with exponents in E4 has local density the E4 integral of page 51
with `1` replaced by `s`, over `log Z`, at `m = Z^s`, with every log power saved on every prefix
of J. -/
theorem leaf_four_density_main (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
            if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
                  Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)
            else 0) -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact four_density_main ω hω hz hε hε8

end LeanLab.BHP1997.LowerShortC165
