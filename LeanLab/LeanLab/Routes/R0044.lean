/-
R-0044, U-1390, PC 20261021T1003Z-20044, MOONSHOT T3. AI wrote this code.
GRH plus pair correlation route, Languasco-Perelli 1996: under GRH and a pair
correlation hypothesis for Dirichlet zeros the Goldbach exceptional set in
[X, X + X^{2θ}] is O(X^ε).  The analytic inputs reach r(N) only through a mean
square over N.  Two facts, neither is progress on Goldbach, which is OPEN.
1. `exceptional_mean_square`: the mechanism.  If the main term is at least m on the
   window W, the number of N ∈ W with r(N) = 0, times m², is at most the mean square
   Σ_{N ∈ W} (r N - M N)².
2. `single_exception_blind`: changing r to 0 at one N₀ raises the mean square by
   exactly M N₀² minus the old term, so a mean square bound B ≥ M N₀² plus the rest
   never excludes a single exception.
-/
import Mathlib

open Finset

namespace LeanLab.Routes.R0044

open Classical in
/-- Mean square to exceptional count, the Chebyshev step behind every GRH plus
pair correlation exceptional set bound. -/
theorem exceptional_mean_square (W : Finset ℕ) (r M : ℕ → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hM : ∀ N ∈ W, m ≤ M N) :
    ((W.filter fun N => r N = 0).card : ℝ) * m ^ 2 ≤ ∑ N ∈ W, (r N - M N) ^ 2 := by
  have h1 : ((W.filter fun N => r N = 0).card : ℝ) * m ^ 2
      = ∑ N ∈ W.filter (fun N => r N = 0), m ^ 2 := by
    rw [sum_const, nsmul_eq_mul]
  have h2 : ∑ N ∈ W.filter (fun N => r N = 0), m ^ 2
      ≤ ∑ N ∈ W.filter (fun N => r N = 0), (r N - M N) ^ 2 := by
    refine sum_le_sum fun N hN => ?_
    rw [mem_filter] at hN
    rw [hN.2, zero_sub, neg_sq]
    have := hM N hN.1
    nlinarith
  have h3 : ∑ N ∈ W.filter (fun N => r N = 0), (r N - M N) ^ 2
      ≤ ∑ N ∈ W, (r N - M N) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  linarith

/-- One exception costs exactly M N₀² in the mean square. -/
theorem single_exception_blind (W : Finset ℕ) (r M : ℕ → ℝ) (N₀ : ℕ) (h : N₀ ∈ W) :
    ∑ N ∈ W, (Function.update r N₀ 0 N - M N) ^ 2
      = ∑ N ∈ W.erase N₀, (r N - M N) ^ 2 + M N₀ ^ 2 := by
  rw [← add_sum_erase W _ h, Function.update_self, zero_sub, neg_sq, add_comm]
  congr 1
  refine sum_congr rfl fun N hN => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hN)]

/-- Mean square blindness: any bound B that allows M N₀² beyond the other terms is
also met by the function with an exception at N₀. -/
theorem mean_square_cannot_exclude (W : Finset ℕ) (r M : ℕ → ℝ) (N₀ : ℕ) (h : N₀ ∈ W)
    (B : ℝ) (hB : ∑ N ∈ W.erase N₀, (r N - M N) ^ 2 + M N₀ ^ 2 ≤ B) :
    Function.update r N₀ 0 N₀ = 0 ∧
      ∑ N ∈ W, (Function.update r N₀ 0 N - M N) ^ 2 ≤ B := by
  refine ⟨Function.update_self _ _ _, ?_⟩
  rw [single_exception_blind W r M N₀ h]
  exact hB

/-- Vacuity of `exceptional_mean_square`: W = {4, 6, 8}, main term 2, so m = 2 is
allowed; with r = 2 off 6 and r 6 = 0 the mean square is exactly 4 = 1 · 2². -/
example : ∀ N ∈ ({4, 6, 8} : Finset ℕ), (2 : ℝ) ≤ (fun _ => (2 : ℝ)) N := by
  intro N _; norm_num

example : ∑ N ∈ ({4, 6, 8} : Finset ℕ),
    (Function.update (fun _ => (2 : ℝ)) 6 0 N - 2) ^ 2 = 4 := by
  rw [single_exception_blind {4, 6, 8} (fun _ => (2 : ℝ)) (fun _ => 2) 6 (by decide)]
  norm_num

/-- Vacuity of `mean_square_cannot_exclude`: B = 4 admits the exception at 6. -/
example : ∑ N ∈ ({4, 6, 8} : Finset ℕ).erase 6, ((fun _ => (2 : ℝ)) N - 2) ^ 2
    + (2 : ℝ) ^ 2 ≤ 4 := by
  norm_num

end LeanLab.Routes.R0044

#print axioms LeanLab.Routes.R0044.exceptional_mean_square
#print axioms LeanLab.Routes.R0044.single_exception_blind
#print axioms LeanLab.Routes.R0044.mean_square_cannot_exclude
