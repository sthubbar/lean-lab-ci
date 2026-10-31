import Mathlib

/-!
# U-1572, T3 MOONSHOT: the Gaussian lift of binary Goldbach, the real axis slice

PC run 20261027T0403Z-13216, unit U-1572. AI wrote this Lean code.
Binary Goldbach is OPEN. Nothing here is progress on Goldbach.

Route: ask for an even rational integer `N` as `π + π'` with `π, π'` Gaussian primes. Writing
`π = a + b i`, this holds as soon as `a² + b²` and `(N - a)² + b²` are both rational primes,
and on the slice `b = 0` it is restricted binary Goldbach with `p, q ≡ 3 mod 4`.
The two norms differ by `N (N - 2a)`, so for fixed `a` the problem is a pair of shifted
quadratics `b² + A`, `b² + A + D`, a twin type problem, and the joint condition needs a sieve
on two forms: Selberg's parity barrier applies. The route is BLOCKED; this file only proves the
algebra that turns two prime norms into a Gaussian Goldbach representation.

Plain math twins:
* `norm_reflect`: `N(N - (a + b i)) = (N - a)² + b²`.
* `norm_gap`: `((N - a)² + b²) - (a² + b²) = N (N - 2a)`.
* `prime_of_natAbs_norm_prime`: a Gaussian integer of prime norm is a Gaussian prime.
* `gauss_rep_of_norms`: if `a² + b²` and `(N - a)² + b²` are prime then `N = π + π'`
  with `π = a + b i` and `π' = (N - a) - b i` Gaussian primes.
* `gauss_rep_of_three_mod_four`: restricted binary Goldbach, `N = p + q`, `p ≡ q ≡ 3 mod 4`,
  gives a Gaussian representation, so the Gaussian statement is weaker than that one.
* `odd_forces_two`: for odd `N`, if both norms are prime then one of them is `2`.
* vacuity: `10 = (1 + 4i) + (9 - 4i)`, norms 17 and 97.
-/

namespace LeanLab.Routes.U1572

open GaussianInt

/-- Plain math: `N(N - (a + b i)) = (N - a)² + b²`. -/
theorem norm_reflect (N a b : ℤ) :
    Zsqrtd.norm ((N : GaussianInt) - ⟨a, b⟩) = (N - a) ^ 2 + b ^ 2 := by
  simp [Zsqrtd.norm_def]
  ring

/-- Plain math: `N(a + b i) = a² + b²`. -/
theorem norm_point (a b : ℤ) : Zsqrtd.norm (⟨a, b⟩ : GaussianInt) = a ^ 2 + b ^ 2 := by
  simp [Zsqrtd.norm_def]
  ring

/-- Plain math: the two norms differ by `N (N - 2a)`, independent of `b`. -/
theorem norm_gap (N a b : ℤ) :
    ((N - a) ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2) = N * (N - 2 * a) := by
  ring

/-- Plain math: a Gaussian integer whose norm is a rational prime is a Gaussian prime. -/
theorem prime_of_natAbs_norm_prime (z : GaussianInt) (h : (Zsqrtd.norm z).natAbs.Prime) :
    Prime z := by
  have hirr : Irreducible z := by
    refine ⟨?_, ?_⟩
    · intro hu
      have := (Zsqrtd.norm_eq_one_iff).2 hu
      rw [this] at h
      exact Nat.not_prime_one h
    · intro x y hxy
      have hm : (Zsqrtd.norm z).natAbs = (Zsqrtd.norm x).natAbs * (Zsqrtd.norm y).natAbs := by
        rw [hxy, Zsqrtd.norm_mul, Int.natAbs_mul]
      rw [hm] at h
      rcases Nat.prime_mul_iff.1 h with ⟨_, hy⟩ | ⟨_, hx⟩
      · exact Or.inr ((Zsqrtd.norm_eq_one_iff).1 hy)
      · exact Or.inl ((Zsqrtd.norm_eq_one_iff).1 hx)
  exact hirr.prime

/-- Plain math: if `a² + b²` and `(N - a)² + b²` are rational primes then
`N = (a + b i) + ((N - a) - b i)` is a sum of two Gaussian primes. -/
theorem gauss_rep_of_norms (N a b : ℤ) (h1 : (a ^ 2 + b ^ 2).natAbs.Prime)
    (h2 : ((N - a) ^ 2 + b ^ 2).natAbs.Prime) :
    ∃ π π' : GaussianInt, Prime π ∧ Prime π' ∧ π + π' = (N : GaussianInt) := by
  refine ⟨⟨a, b⟩, (N : GaussianInt) - ⟨a, b⟩, ?_, ?_, by ring⟩
  · apply prime_of_natAbs_norm_prime
    rw [norm_point]; exact h1
  · apply prime_of_natAbs_norm_prime
    rw [norm_reflect]; exact h2

/-- Plain math: restricted binary Goldbach, `N = p + q` with `p ≡ q ≡ 3 mod 4`, gives a
Gaussian representation, since such rational primes stay prime in `GaussianInt`. -/
theorem gauss_rep_of_three_mod_four (N p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (h : p + q = N) :
    ∃ π π' : GaussianInt, Prime π ∧ Prime π' ∧ π + π' = ((N : ℤ) : GaussianInt) := by
  have := Fact.mk hp
  have := Fact.mk hq
  refine ⟨((p : ℤ) : GaussianInt), ((q : ℤ) : GaussianInt), ?_, ?_, ?_⟩
  · have := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).2 hp3
    simpa using this
  · have := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime q).2 hq3
    simpa using this
  · subst h; push_cast; ring

/-- Plain math: for odd `N`, two prime norms `a² + b²` and `(N - a)² + b²` force one of them
to be `2`, since they differ by the odd number `N (N - 2a)`. The Gaussian lift keeps the
parity of `N` condition of binary Goldbach. -/
theorem odd_forces_two (N a b : ℤ) (hN : Odd N) (h1 : (a ^ 2 + b ^ 2).natAbs.Prime)
    (h2 : ((N - a) ^ 2 + b ^ 2).natAbs.Prime) :
    (a ^ 2 + b ^ 2).natAbs = 2 ∨ ((N - a) ^ 2 + b ^ 2).natAbs = 2 := by
  have hodd : Odd (((N - a) ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2)) := by
    rw [norm_gap]
    refine hN.mul ?_
    rcases hN with ⟨k, hk⟩
    exact ⟨k - a, by rw [hk]; ring⟩
  rcases h1.eq_two_or_odd' with e1 | o1
  · exact Or.inl e1
  rcases h2.eq_two_or_odd' with e2 | o2
  · exact Or.inr e2
  exfalso
  have o1' : Odd (a ^ 2 + b ^ 2) := Int.natAbs_odd.1 o1
  have o2' : Odd ((N - a) ^ 2 + b ^ 2) := Int.natAbs_odd.1 o2
  have : Even (((N - a) ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2)) := Odd.sub_odd o2' o1'
  exact (Int.not_even_iff_odd.2 hodd) this

/-- Vacuity instance: `10 = (1 + 4i) + (9 - 4i)`, norms `17` and `97`, both prime. -/
theorem vacuity_ten : ∃ π π' : GaussianInt, Prime π ∧ Prime π' ∧ π + π' = ((10 : ℤ) : GaussianInt) :=
  gauss_rep_of_norms 10 1 4 (by norm_num) (by norm_num)

/-- Vacuity instance for the b = 0 slice: `10 = 3 + 7`. -/
theorem vacuity_ten_slice :
    ∃ π π' : GaussianInt, Prime π ∧ Prime π' ∧ π + π' = (((10 : ℕ) : ℤ) : GaussianInt) :=
  gauss_rep_of_three_mod_four 10 3 7 (by norm_num) (by norm_num) rfl rfl rfl

end LeanLab.Routes.U1572
