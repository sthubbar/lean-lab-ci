import Mathlib
import LeanLab.Common.Goldbach

/-!
# R-0030, T3 MOONSHOT: the automorphic partner, and the L² price of transferring it to the primes

Unit U-1275, PC 20261020T1903Z-4664. AI wrote this file.

Route: in `r(N) = Σ_{p<N} 1_P(N - p)` replace the partner `1_P` by a sequence `g` whose
reflected prime sum `Σ_{p<N} g(N - p)` is controllable for every `N`, for instance Hecke
eigenvalues of a cusp form, where Kuznetsov-type spectral bounds for shifted convolutions supply
the Type II input, plus a sieve-visible main part. The transfer back to `1_P` is paid in L²:

* `partner_split`: `Σ_p 1_P(N - p) = Σ_p g(N - p) + Σ_p (1_P - g)(N - p)`, exact;
* `reflect_sq_le`: `Σ_{p<N prime} h(N - p)² ≤ Σ_{m<N} h(m)²`, the reflection is injective;
* `goldbach_of_partner_l2`: if `π(N) · Σ_{m<N} (1_P - g)(m)² < (Σ_{p<N} g(N - p))²`
  then `N` is a sum of two primes;
* `vacuity_ten`: the hypothesis holds at `N = 10` with `g = 1_P`.
Binary Goldbach is OPEN; this is a criterion and a barrier map, not progress on it.
-/

namespace LeanLab.Routes.R0030

open Finset

/-- The prime indicator as a real function. -/
noncomputable def ind (m : ℕ) : ℝ := if m.Prime then 1 else 0

/-- The primes below `N`. -/
def primesBelow' (N : ℕ) : Finset ℕ := (range N).filter Nat.Prime

/-- Exact split of the Goldbach count against any partner `g`. -/
theorem partner_split (N : ℕ) (g : ℕ → ℝ) :
    ∑ p ∈ primesBelow' N, ind (N - p) =
      ∑ p ∈ primesBelow' N, g (N - p) + ∑ p ∈ primesBelow' N, (ind (N - p) - g (N - p)) := by
  rw [← sum_add_distrib]; congr 1; ext p; ring

/-- Reflecting the primes below `N` into `[0, N)` is injective, so a sum of squares over the
reflected primes is at most the full sum of squares. -/
theorem reflect_sq_le (N : ℕ) (h : ℕ → ℝ) :
    ∑ p ∈ primesBelow' N, h (N - p) ^ 2 ≤ ∑ m ∈ range N, h m ^ 2 := by
  have hinj : Set.InjOn (fun p => N - p) (primesBelow' N : Set ℕ) := by
    intro a ha b hb hab
    simp only [primesBelow', coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    simp only at hab; omega
  rw [← sum_image (f := fun m => h m ^ 2) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [mem_image, primesBelow', mem_filter, mem_range] at hm ⊢
    obtain ⟨p, ⟨hp, hpr⟩, rfl⟩ := hm
    have := hpr.two_le; omega
  · intro _ _ _; positivity

/-- The partner criterion: an L² approximation of the primes by `g`, good enough against the
reflected prime sum of `g`, forces a Goldbach representation of `N`. -/
theorem goldbach_of_partner_l2 (N : ℕ) (g : ℕ → ℝ)
    (h : ((primesBelow' N).card : ℝ) * ∑ m ∈ range N, (ind m - g m) ^ 2 <
      (∑ p ∈ primesBelow' N, g (N - p)) ^ 2) :
    LeanLab.IsGoldbachSum N := by
  by_contra hno
  have hzero : ∀ p ∈ primesBelow' N, ind (N - p) = 0 := by
    intro p hp
    simp only [primesBelow', mem_filter, mem_range] at hp
    unfold ind; split_ifs with hq
    · exact absurd ⟨p, N - p, hp.2, hq, by omega⟩ hno
    · rfl
  have heq : ∑ p ∈ primesBelow' N, g (N - p) =
      -∑ p ∈ primesBelow' N, (ind (N - p) - g (N - p)) := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro p hp; rw [hzero p hp]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := primesBelow' N)
    (f := fun p => ind (N - p) - g (N - p))
  have hrefl := reflect_sq_le N (fun m => ind m - g m)
  have hcard : (0 : ℝ) ≤ (primesBelow' N).card := by positivity
  have : (∑ p ∈ primesBelow' N, g (N - p)) ^ 2 ≤
      ((primesBelow' N).card : ℝ) * ∑ m ∈ range N, (ind m - g m) ^ 2 := by
    rw [heq, neg_sq]
    exact hcs.trans (mul_le_mul_of_nonneg_left hrefl hcard)
  linarith

/-- Vacuity: at `N = 10` with `g = 1_P` the left side is `0` and the right side is `3² = 9`,
from `10 = 3 + 7 = 5 + 5 = 7 + 3`. -/
theorem vacuity_ten :
    ((primesBelow' 10).card : ℝ) * ∑ m ∈ range 10, (ind m - ind m) ^ 2 <
      (∑ p ∈ primesBelow' 10, ind (10 - p)) ^ 2 := by
  have hP : primesBelow' 10 = {2, 3, 5, 7} := by decide
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
    mul_zero, hP]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [ind]
  norm_num

theorem goldbach_ten : LeanLab.IsGoldbachSum 10 :=
  goldbach_of_partner_l2 10 ind vacuity_ten

end LeanLab.Routes.R0030
