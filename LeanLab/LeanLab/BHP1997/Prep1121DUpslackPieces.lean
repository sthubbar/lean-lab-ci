/-
P0069 Baker Harman Pintz 1997, Section 5, page 53. The third positive piece j_m of the
four term display, reindexed as a divisor sum. For each divisor n = p1 * p2 of m with
Y^c1 <= p2 < p1 < Y^c4 the inner term upperRough (m / p1 / p2) (Y^c1) depends only on
n = p1 * p2, so the double sum over prime factors regroups as one sum over the divisors
n of m, weighted by the number of ordered factorizations n = p1 * p2 with p1, p2 prime
and the two cutoffs of the display. The bound n < Y^(2 c4) uses
2 c4 = 1/2 + theta2/4 - 2 eps with theta2 = 2(1/16 - 1/10^5), proved below.

REPAIR NOTE 20261122T1015Z. The branch first stated the regrouping with the weight
`(n.divisors.filter fun d => Y^c1 <= d and d < Y^c4 and Y^c1 <= n / d and n / d < d).card`,
counting every divisor d of n and not only the prime ones. That form is not the paper's
step and is false: at eps = 0, Y = 1000, m = 12 the left side is 0, since 1000^c1 is
about 2.3712, so p1 is 3 and the inner filter on the prime factors of 4, equal to 2, is
empty, while the right side is 1, from n = 12 and the composite d = 4 with n / d = 3 at
once above Y^c1 and below d. The weight here counts prime d only, which is what the
display sums over, and then the regrouping is the exact reindexing that the page performs.
The counterexample was computed, not kernel checked.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069 page 53: the exponent identity 2 * c4 = 1/2 + theta2/4 - 2 * eps, where
theta2 = 2*(1/16 - 1/10^5). PROVED by unfolding the definitions. -/
theorem upD_two_c4_eq {ε : ℝ} : 2 * upperC4 ε = 1/2 + (2*(1/16-1/10^5))/4 - 2*ε := by
  unfold upperC4
  ring

/-- P0069 page 53. The double prime-factor sum j_m regrouped as a divisor sum. For each
divisor n of m the weight is the number of pairs (p1, p2) of primes with p1 * p2 = n and
Y^c1 <= p2 < p1 < Y^c4, written as the count of the divisors d of n with d and n / d both
prime under those two cutoffs, d playing p1 and n / d playing p2; the inner term is
upperRough (m / n) (Y^c1), because m / p1 / p2 = m / (p1 * p2) once p1 and p2 divide m.
This is the page 53 reindexing behind the divisor sum for j_m. PROVED by the bijection
(p1, p2) to (p1 * p2, p1) between the prime pairs and the pairs (n, d) of a divisor n of
m with a prime divisor d of n. -/
theorem upD_j_rep (ε Y : ℝ) (m : ℕ) :
    upperJ ε Y m =
      ∑ n ∈ m.divisors,
        (((n.divisors.filter fun d : ℕ =>
            d.Prime ∧ (n / d).Prime ∧
            Y ^ upperC1 ε ≤ ((n / d : ℕ) : ℝ) ∧ ((n / d : ℕ) : ℝ) < (d : ℝ) ∧
            Y ^ upperC1 ε ≤ (d : ℝ) ∧ (d : ℝ) < Y ^ upperC4 ε).card : ℝ)) *
          upperRough (m / n) (Y ^ upperC1 ε) := by
  classical
  have hsplit : ∀ n ∈ m.divisors,
      (((n.divisors.filter fun d : ℕ =>
            d.Prime ∧ (n / d).Prime ∧
            Y ^ upperC1 ε ≤ ((n / d : ℕ) : ℝ) ∧ ((n / d : ℕ) : ℝ) < (d : ℝ) ∧
            Y ^ upperC1 ε ≤ (d : ℝ) ∧ (d : ℝ) < Y ^ upperC4 ε).card : ℝ) *
          upperRough (m / n) (Y ^ upperC1 ε))
        = ∑ d ∈ n.divisors.filter (fun d : ℕ =>
            d.Prime ∧ (n / d).Prime ∧
            Y ^ upperC1 ε ≤ ((n / d : ℕ) : ℝ) ∧ ((n / d : ℕ) : ℝ) < (d : ℝ) ∧
            Y ^ upperC1 ε ≤ (d : ℝ) ∧ (d : ℝ) < Y ^ upperC4 ε),
          upperRough (m / n) (Y ^ upperC1 ε) := by
    intro n _
    rw [Finset.sum_const, nsmul_eq_mul]
  unfold upperJ
  rw [Finset.sum_sigma']
  simp only [Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x : (Σ _ : ℕ, ℕ) => (⟨x.1 * x.2, x.1⟩ : Σ _ : ℕ, ℕ))
    (fun y : (Σ _ : ℕ, ℕ) => (⟨y.2, y.1 / y.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p1, p2⟩ hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hp1S, hp2T⟩ := hp
    rw [Finset.mem_filter] at hp1S hp2T
    obtain ⟨hp1pf, hp1lo, hp1hi⟩ := hp1S
    obtain ⟨hp2pf, hp2lo, hp2lt⟩ := hp2T
    obtain ⟨hp1p, hp1dvd, hm0⟩ := Nat.mem_primeFactors.mp hp1pf
    obtain ⟨hp2p, hp2dvd, -⟩ := Nat.mem_primeFactors.mp hp2pf
    have hq : p1 * p2 / p1 = p2 := Nat.mul_div_right p2 hp1p.pos
    have hmem : p1 * p2 ∈ m.divisors := by
      rw [Nat.mem_divisors]
      refine ⟨?_, hm0⟩
      have hm : m = p1 * (m / p1) := (Nat.mul_div_cancel' hp1dvd).symm
      rw [hm]
      exact mul_dvd_mul_left p1 hp2dvd
    rw [Finset.mem_sigma]
    refine ⟨hmem, ?_⟩
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨dvd_mul_right p1 p2, Nat.mul_ne_zero hp1p.pos.ne' hp2p.pos.ne'⟩,
      hp1p, by rw [hq]; exact hp2p, by rw [hq]; exact hp2lo, by rw [hq]; exact hp2lt,
      hp1lo, hp1hi⟩
  · rintro ⟨n, d⟩ ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hn, hd⟩ := ha
    rw [Finset.mem_filter] at hd
    obtain ⟨hdd, hdp, hnp, hlo, hlt, hdlo, hdhi⟩ := hd
    obtain ⟨hnm, hm0⟩ := Nat.mem_divisors.mp hn
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hdd
    have hmd : d ∣ m := dvd_trans hdn hnm
    have hmd0 : m / d ≠ 0 := by
      intro h
      have hm : m = d * (m / d) := (Nat.mul_div_cancel' hmd).symm
      rw [h, mul_zero] at hm
      exact hm0 hm
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter, Nat.mem_primeFactors,
      Nat.mem_primeFactors]
    exact ⟨⟨⟨hdp, hmd, hm0⟩, hdlo, hdhi⟩,
      ⟨hnp, Nat.div_dvd_div hdn hnm, hmd0⟩, hlo, hlt⟩
  · rintro ⟨p1, p2⟩ hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hp1S, -⟩ := hp
    rw [Finset.mem_filter] at hp1S
    obtain ⟨hp1pf, -, -⟩ := hp1S
    obtain ⟨hp1p, -, -⟩ := Nat.mem_primeFactors.mp hp1pf
    have hq : p1 * p2 / p1 = p2 := Nat.mul_div_right p2 hp1p.pos
    rw [hq]
  · rintro ⟨n, d⟩ ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hn, hd⟩ := ha
    rw [Finset.mem_filter] at hd
    obtain ⟨hdd, -⟩ := hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hdd
    rw [Nat.mul_div_cancel' hdn]
  · rintro ⟨p1, p2⟩ _
    rfl


end LeanLab.BHP1997.DecompC165d
