/-
R-5310, CLOUD 20261020T2317Z-cloud53, unit U-6778, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The probability generating function route.  For a finite family `S` with
weights `w` and a statistic `k`, here `k p = Ω (N - p)` on the primes `p < N`,
put `pgf S w k z = Σ_{s ∈ S} w s * z ^ k s`.  Binary Goldbach for `N` is the
`z ^ 1` coefficient of the unweighted family being positive.  Plain math twins:

* `pgf_twist`: the parity twist, weights `w * (1 + λ)` with `λ = (-1) ^ k`,
  has generating function `G(z) + G(-z)`.  This is Selberg's parity example
  written as a generating function identity.
* `twist_coeff_odd`: every odd coefficient of the twisted family is zero; in
  particular the `z ^ 1` coefficient, the Goldbach mass, vanishes.
* `twist_nonneg`: the twisted weights are nonnegative when `w` is, so the
  twisted family is a genuine measure.
* `pgf_twist_sub_le`: on reals the twist changes `G(z)` by at most
  `G_{|w|}(|z|)`, a bound with no information about the sign of `z`.
* `goldbach_coeff`: for every `N`, the number of primes `p < N` with
  `Ω (N - p) = 1` equals the number of primes `p < N` with `N - p` prime.
* `goldbach_coeff_thirty`: non-vacuity, at `N = 30` that count is 6.
-/
import Mathlib

namespace LeanLab.Routes.R5310

open Finset
open scoped ArithmeticFunction.Omega

/-- The generating function `Σ_{s ∈ S} w s * z ^ k s`. -/
def pgf {ι R : Type*} [CommRing R] (S : Finset ι) (w : ι → R) (k : ι → ℕ) (z : R) : R :=
  ∑ s ∈ S, w s * z ^ k s

/-- The parity twist `w ↦ w * (1 + (-1) ^ k)` turns `G(z)` into `G(z) + G(-z)`. -/
theorem pgf_twist {ι R : Type*} [CommRing R] (S : Finset ι) (w : ι → R) (k : ι → ℕ)
    (z : R) :
    pgf S (fun s => w s * (1 + (-1) ^ k s)) k z = pgf S w k z + pgf S w k (-z) := by
  unfold pgf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [neg_pow]
  ring

/-- The twisted family has zero mass at every odd value of `k`. -/
theorem twist_coeff_odd {ι R : Type*} [CommRing R] (S : Finset ι) (w : ι → R)
    (k : ι → ℕ) (j : ℕ) (hj : Odd j) :
    ∑ s ∈ S.filter (fun s => k s = j), w s * (1 + (-1) ^ k s) = 0 := by
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Finset.mem_filter] at hs
  rw [hs.2, hj.neg_one_pow]
  ring

/-- The twisted weights are nonnegative. -/
theorem twist_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 + (-1) ^ n := by
  rcases n.even_or_odd with h | h
  · rw [h.neg_one_pow]; norm_num
  · rw [h.neg_one_pow]; norm_num

/-- On the reals the twist moves `G(z)` by at most `Σ |w| |z| ^ k`. -/
theorem pgf_twist_sub_le {ι : Type*} (S : Finset ι) (w : ι → ℝ) (k : ι → ℕ) (z : ℝ) :
    |pgf S (fun s => w s * (1 + (-1) ^ k s)) k z - pgf S w k z| ≤
      ∑ s ∈ S, |w s| * |z| ^ k s := by
  rw [pgf_twist, add_sub_cancel_left]
  unfold pgf
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [abs_mul, abs_pow, abs_neg]

/-- Binary Goldbach as the `z ^ 1` coefficient: `Ω (N - p) = 1` iff `N - p` is prime. -/
theorem goldbach_coeff (N : ℕ) :
    ((Finset.range N).filter (fun p => p.Prime ∧ Ω (N - p) = 1)).card =
      ((Finset.range N).filter (fun p => p.Prime ∧ (N - p).Prime)).card := by
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [ArithmeticFunction.cardFactors_eq_one_iff_prime]

/-- Non-vacuity: at `N = 30` the Goldbach coefficient count is 6:
`p = 7, 11, 13, 17, 19, 23`. -/
theorem goldbach_coeff_thirty :
    ((Finset.range 30).filter (fun p => p.Prime ∧ Ω (30 - p) = 1)).card = 6 := by
  rw [goldbach_coeff]
  decide

/-- Non-vacuity of the twist: a two point family with `k = 1, 2` and weights 1. -/
theorem pgf_twist_example (z : ℤ) :
    pgf ({1, 2} : Finset ℕ) (fun s => (1 : ℤ) * (1 + (-1) ^ s)) id z = 2 * z ^ 2 := by
  simp [pgf]

end LeanLab.Routes.R5310

#print axioms LeanLab.Routes.R5310.pgf_twist
#print axioms LeanLab.Routes.R5310.twist_coeff_odd
#print axioms LeanLab.Routes.R5310.twist_nonneg
#print axioms LeanLab.Routes.R5310.pgf_twist_sub_le
#print axioms LeanLab.Routes.R5310.goldbach_coeff
#print axioms LeanLab.Routes.R5310.goldbach_coeff_thirty
#print axioms LeanLab.Routes.R5310.pgf_twist_example
