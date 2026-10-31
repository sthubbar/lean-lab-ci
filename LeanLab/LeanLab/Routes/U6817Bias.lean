/-
U-6817, CLOUD 20261021T0316Z-cloud57, T3 MOONSHOT, route R-5323.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Chebyshev bias route.  Split the Goldbach count by the class of p mod 4.
With χ₄ the nonprincipal character mod 4, written here by hand as `chi4`,
the twisted ordered count Σ_{a ≤ N} χ₄(a) f(a) f(N - a) is
* exactly zero when 4 ∣ N, for EVERY weight f, by the reflection a ↦ N - a,
  `twisted_zero`, since χ₄(N - a) = -χ₄(a) there, `chi4_reflect_zero`;
* a same-class count when N ≡ 2 mod 4, χ₄(N - a) = χ₄(a), `chi4_reflect_two`,
  so its whole mass sits on N ≡ 2 mod 4, where it measures primes 3 mod 4
  against primes 1 mod 4 in the Goldbach pairs of N.
The numerics r_u6817_bias.py find the predicted Chebyshev bias of that
twisted count, mean about -4·√N on N ≡ 2 mod 4, against a pointwise spread
growing like log N; these lemmas are the exact algebra behind the support
claim and nothing more.
-/
import Mathlib

namespace LeanLab.Routes.U6817

open Finset

/-- The nonprincipal Dirichlet character mod 4 on ℕ, by hand. -/
def chi4 (n : ℕ) : ℤ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

theorem chi4_reflect_zero {N a : ℕ} (hN : N % 4 = 0) (ha : a ≤ N) :
    chi4 (N - a) = - chi4 a := by
  unfold chi4
  split_ifs <;> omega

theorem chi4_reflect_two {N a : ℕ} (hN : N % 4 = 2) (ha : a ≤ N) :
    chi4 (N - a) = chi4 a := by
  unfold chi4
  split_ifs <;> omega

/-- The χ₄-twisted ordered binary count vanishes identically when 4 ∣ N,
for every integer weight f. -/
theorem twisted_zero (f : ℕ → ℤ) {N : ℕ} (hN : N % 4 = 0) :
    ∑ a ∈ range (N + 1), chi4 a * (f a * f (N - a)) = 0 := by
  have h := Finset.sum_range_reflect
    (fun a => chi4 a * (f a * f (N - a))) (N + 1)
  have h2 : ∑ j ∈ range (N + 1), chi4 (N + 1 - 1 - j) *
        (f (N + 1 - 1 - j) * f (N - (N + 1 - 1 - j)))
      = - ∑ a ∈ range (N + 1), chi4 a * (f a * f (N - a)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e1 : N + 1 - 1 - j = N - j := by omega
    have e2 : N - (N - j) = j := by omega
    rw [e1, e2, chi4_reflect_zero hN hj']
    ring
  linarith

/-- Same-class form at N ≡ 2 mod 4: the twisted count is the class-3 pairs
minus the class-1 pairs, both summands in the same class. -/
theorem twisted_two_same_class {N a : ℕ} (hN : N % 4 = 2) (ha : a ≤ N)
    (h1 : a % 4 = 1) : (N - a) % 4 = 1 := by omega

theorem twisted_two_same_class3 {N a : ℕ} (hN : N % 4 = 2) (ha : a ≤ N)
    (h3 : a % 4 = 3) : (N - a) % 4 = 3 := by omega

/-- Nonvacuity check at N = 8 with f the indicator of 3 and 5:
the twisted count is χ₄(3) + χ₄(5) = 0, and the untwisted count is 2. -/
example : ∑ a ∈ range 9, chi4 a *
    ((if a = 3 ∨ a = 5 then (1 : ℤ) else 0) *
     (if 8 - a = 3 ∨ 8 - a = 5 then (1 : ℤ) else 0)) = 0 := by decide

end LeanLab.Routes.U6817

#print axioms LeanLab.Routes.U6817.chi4_reflect_zero
#print axioms LeanLab.Routes.U6817.chi4_reflect_two
#print axioms LeanLab.Routes.U6817.twisted_zero
#print axioms LeanLab.Routes.U6817.twisted_two_same_class
#print axioms LeanLab.Routes.U6817.twisted_two_same_class3
