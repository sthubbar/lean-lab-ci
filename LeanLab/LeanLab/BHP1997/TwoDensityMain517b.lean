/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: the outer primes `p1`, `p2` at one point `m` of J.

The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the sum over the prime pairs `p2 < p1` with exponents in E2 this file writes
the consequence as three one variable steps and proves the exact algebra between them:

* `two_pair_sum_split`: with `w` the indicator of the primes and `l n = 1 / log n`, the double
  sum over `w b w a` is the double sum over `l b l a` plus two error sums, one with the factor
  `w a - l a` for each fixed `b`, one with the factor `w b - l b` for each fixed integer `a`;
* `two_pair_first_prime`, in `TwoDensityMain517d.lean`: the first error sum, the prime number
  theorem with partial summation in `p1` for each fixed prime `p2`;
* `two_pair_second_prime`, in `TwoDensityMain517d.lean`: the second error sum, the prime
  number theorem with partial summation in `p2` for each fixed integer `a`;
* `two_pair_riemann`: the double sum over integers with the densities `1 / (log a log b)` is
  the E2 integral of page 51 at `s = log m / log Z`. No prime number theorem is used in this
  step. It is split here into its two one variable passages from a sum to an integral,
  `leaf_two_pair_riemann_first` and `leaf_two_pair_riemann_second`, which are the two open
  leaves.

`two_pair_density_pointwise` is proved from these three statements.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.TwoDensityMain517d

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Interchange of
the two outer variables over the triangle `1 ≤ b < a ≤ N`. -/
theorem two_pair_triangle_swap (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, g a b =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, g a b := by
  refine Finset.sum_comm' fun b a => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Exact algebra
of the two applications of the prime number theorem: with `w` the indicator of the primes and
`l` the density `1 / log`, the sum over `w b w a` is the sum over `l a l b` plus an error with
the factor `w a - l a` for each fixed `b` and an error with the factor `w b - l b` for each
fixed `a`. -/
theorem two_pair_sum_split (N : ℕ) (w l : ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, F a b * (l a * l b) := by
  have e1 : ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, w b * (l a * F a b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have e2 := two_pair_triangle_swap N (fun a b => w b * (l a * F a b))
  have e3 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, w b * (l a * F a b) =
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, F a b * (l a * l b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := two_pair_triangle_swap N (fun a b => F a b * (l a * l b))
  beta_reduce at e2 e4
  rw [e1, e2, e3, ← e4]
  ring

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. The sum over
the prime pairs `p2 < p1` up to `N` with a condition `E` is the iterated sum over `b` and then
`a > b` weighted by the indicator of the primes. -/
theorem two_pair_sum_iterated (N : ℕ) (E : ℕ → ℕ → Prop) (t : ℕ → ℕ → ℝ) :
    ∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧ E i.1 i.2), t i.1 i.2 =
      ∑ b ∈ Finset.Icc 1 N, primeWeight b *
        ∑ a ∈ Finset.Ioc b N, primeWeight a * (if E a b then t a b else 0) := by
  rw [Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb1 := (Finset.mem_Icc.mp hb).1
  have hIoc : Finset.Ioc b N = (Finset.Icc 1 N).filter (fun a => b < a) := by
    ext a
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hIoc, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : a.Prime <;> by_cases h2 : b.Prime <;> by_cases h3 : b < a <;>
    by_cases h4 : E a b <;> simp [primeWeight, h1, h2, h3, h4]

/-- LEAF: P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the
passage from the sum over the first outer variable to the integral of page 51. For each fixed
integer `b` the sum over the integers `a > b` with exponents in E2 of
`ω(log (m / (a b)) / log b) / (a log a)` is the integral over the first exponent `β1` of
`ω((s - β1 - β2) / β2) / β1` on the section of E2 at `β2 = log b / log Z`, where `m = Z^s`:
the change of variables `a = Z^β1` has `da / (a log a) = dβ1 / β1`, and on `a > b ≥
(2 Y) ^ (1 / 10)` the sum of a function of bounded variation is its integral up to a power
saving. The statement is summed over `b` with the remaining weight `1 / (b log^2 b)`. No
prime number theorem is used. -/
theorem leaf_two_pair_riemann_first (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)| ≤ C * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the
passage from the sum over the second outer variable to the integral of page 51. The sum over
the integers `b` of `M(log b / log Z) / (b log^2 b)`, where `M(β2)` is the integral over the
first exponent of `ω((s - β1 - β2) / β2) / β1` on the section of E2 at `β2`, is
`(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)`: the change of variables `b = Z^β2`
has `db / (b log^2 b) = dβ2 / (β2^2 log Z)`, the function `M` has bounded variation and
vanishes below `β2 = 1 / 10`, so the sum is the integral up to a power saving, and the order
of the two integrals is exchanged by Fubini. No prime number theorem is used. -/
theorem leaf_two_pair_riemann_second (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 51, display 5.17, the E2 sum of display 5.15 at one point `m` of J, the passage
from sums to the integral of page 51. The sum over the integer pairs `b < a` with exponents in
E2 of `ω(log (m / (a b)) / log b) / (a b log a log^2 b)` is
`(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at `m = Z^s`. No prime number theorem
is used. CONDITIONAL ON `leaf_two_pair_riemann_first` and `leaf_two_pair_riemann_second`. -/
theorem two_pair_riemann (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := leaf_two_pair_riemann_first ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := leaf_two_pair_riemann_second ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) (|C1| + |C2| + 1), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hC : |C1| + |C2| + 1 ≤ max (max C1 C2) (|C1| + |C2| + 1) := le_max_right _ _
  have hxone : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg C1
    have h2 := abs_nonneg C2
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have a1 := abs_le.mp (hC1 x hx1 m hm1 hm2)
  have a2 := abs_le.mp (hC2 x hx2 m hm1 hm2)
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have k4 := mul_le_mul_of_nonneg_right hC hL
  have k5 : (|C1| + |C2| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", the outer primes `p1`, `p2` of the E2 sum of display 5.15 at one point `m` of J. The
sum over the prime pairs with exponents in E2 of `ω(log (m / (p1 p2)) / log p2) / log p2`
weighted by `1 / (p1 p2)` is `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at
`m = Z^s`, with every log power saved. CONDITIONAL ON `leaf_two_pair_riemann_first` and
`leaf_two_pair_riemann_second`. -/
theorem two_pair_density_pointwise (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
            Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := two_pair_first_prime ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := two_pair_second_prime ω hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := two_pair_riemann ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : C3 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC : |C1| + |C2| + |C3| + 1 ≤ max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg C1
    have h2 := abs_nonneg C2
    have h3 := abs_nonneg C3
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have b1 := hC1 x hx1 m hm1 hm2
  have b2 := hC2 x hx2 m hm1 hm2
  have b3 := hC3 x hx3 m hm1 hm2
  have hiter := two_pair_sum_iterated ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (fun a b => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (fun a b => ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
      Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)))
  have hsplit := two_pair_sum_split ⌊2 * x ^ (11 / 20 + ε)⌋₊ primeWeight
    (fun n => 1 / Real.log (n : ℝ))
    (fun a b => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
      ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0)
  beta_reduce at hiter hsplit
  rw [hiter, hsplit]
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have a3 := abs_le.mp b3
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have k3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hL
  have k4 := mul_le_mul_of_nonneg_right hC hL
  have k5 : (|C1| + |C2| + |C3| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + |C3| * Real.log x ^ (-A) +
        Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end LeanLab.BHP1997.LowerShortC165
