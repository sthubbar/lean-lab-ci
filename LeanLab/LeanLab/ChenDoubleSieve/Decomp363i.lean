import LeanLab.ChenDoubleSieve.Decomp363h

/-!
The local weights used in the application of the linear sieve in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 5 equation 2.2 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task363

/-- The page 38 local weight satisfies the strict range in equation 2.2.
The prime two is absent when N is even. -/
theorem local_weight_bounds {N p : ℕ} (hEven : Even N) (hp : p.Prime)
    (hcop : p.Coprime N) :
    0 ≤ (p : ℝ) / (p.totient : ℝ) ∧ (p : ℝ) / (p.totient : ℝ) < p := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) hEven.two_dvd
  have hpR : (3 : ℝ) ≤ p := by
    exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · rw [div_lt_iff₀ (by linarith : 0 < (p : ℝ) - 1)]
    nlinarith

/-- The local Euler product is exactly the product with density w p divided by p
for the paper's weights w p equal p divided by phi p. -/
theorem localDensity_totient (N : ℕ) (z : ℝ) :
    (∏ p ∈ Wu41.PS N 0 z,
      (1 - ((p : ℝ) / (p.totient : ℝ)) / p)) = localDensity N z := by
  unfold localDensity
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Wu41.mem_PS.mp hp).1
  have hpos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]
  field_simp [hpos.ne', show (p : ℝ) - 1 ≠ 0 by linarith]

end LeanLab.ChenDoubleSieve.Task363
