import LeanLab.Romanov.Erdos
import LeanLab.DensityGoldbach.AlsetriShaoLocal

/-!
# R-5063, covering congruences: why the Erdős method refutes `p + 2^k` and cannot touch `p + q`

Lab proof, unit U-5608, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics:
Erdős 1950 for the covering, the local count is the singular series factor. Binary Goldbach is
OPEN; this is a T3 route, never progress on Goldbach.

* `pow_two_obstructed`: infinitely many odd `n` are not `p + 2^k`, by a covering with moduli
  dividing `2^24 - 1` and the class mod 31, from Romanov/Erdos.lean.
* `binary_local`: for every odd squarefree `m` and every residue `n mod m` there is a unit `x`
  with `n - x` a unit, indeed at least `∏_{p ∣ m} (p - 2)` of them; so no covering system can
  forbid `n = p + q` for all pairs of primes in fixed classes, from AlsetriShaoLocal.card_X_ge.
-/

namespace LeanLab.Routes.R5063

open Finset

theorem pow_two_obstructed :
    {n : ℕ | Odd n ∧ ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k}.Infinite :=
  LeanLab.Romanov.erdos_infinite

theorem binary_local (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hsq : Squarefree m) :
    haveI : NeZero m := ⟨hm.ne'⟩
    ∀ n : ZMod m, ∃ x : ZMod m, IsUnit x ∧ IsUnit (n - x) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  intro n
  have h := LeanLab.DensityGoldbach.AlsetriShaoLocal.card_X_ge m hm hsq n
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 2) := by
    refine prod_pos fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
    have := hpr.two_le
    omega
  obtain ⟨x, hx⟩ := card_pos.1 (lt_of_lt_of_le hpos h)
  simp only [LeanLab.DensityGoldbach.AlsetriShaoLocal.Xset, mem_filter, mem_univ, true_and] at hx
  exact ⟨x, hx⟩

/-- Vacuity test: the hypotheses hold at `m = 105`. -/
example : ∃ x : ZMod 105, IsUnit x ∧ IsUnit (1 - x) :=
  binary_local 105 (by norm_num) (by decide) (by
    rw [show (105 : ℕ) = 3 * 5 * 7 by norm_num]
    exact (Nat.squarefree_mul (by norm_num)).2 ⟨(Nat.squarefree_mul (by norm_num)).2
      ⟨Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩, (by norm_num : Nat.Prime 7).squarefree⟩) 1

end LeanLab.Routes.R5063
