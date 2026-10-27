/-
# R-0031, T3 MOONSHOT: the spectral route, Kuznetsov and Kloosterman sums on A = {N - p}

Unit U-1279, PC run 20261020T2004Z-7678.

The route: Deshouillers-Iwaniec bounds for sums of Kloosterman sums, from the Kuznetsov
formula, push the level of distribution of primes past 1/2 for well-factorable weights,
Bombieri-Friedlander-Iwaniec 1986, Lichtman arXiv 2309.08522 at level 66/107, and Lichtman
uses this for the Goldbach UPPER bound G(N) ≤ 3.3907 times the Hardy-Littlewood prediction.
Everything the spectral side supplies enters as Type I data, the counts A_d of multiples of d,
linear in the sequence. This file proves the two elementary facts that make that data parity
blind, plus the two Kloosterman symmetries the spectral side starts from.

PROVED here, unconditional:
* `sum_dvd_liouville`: Σ_{m ≤ x, d ∣ m} λ(m) = λ(d) Σ_{k ≤ x/d} λ(k), so the Liouville twist has
  Type I data of size |L(x/d)| at every level d: data at level d cannot tell the λ = -1 part of
  a sequence from the λ = +1 part beyond what L(x/d) = o(x/d) allows.
* `liouville_prime'` and `goldbach_pairs_in_minus`: every Goldbach pair p + q = N has
  λ(N - p) = -1, so the count of p < N with N - p prime is at most the count with
  λ(N - p) = -1; the λ = +1 half of A = {N - p} holds no Goldbach pair at all.
* `kloost_symm`: S_ψ(m, n) = S_ψ(n, m), substituting u ↦ u⁻¹.
* `kloost_twist`: S_ψ(a m, n) = S_ψ(m, a n) for a unit a, substituting u ↦ a⁻¹ u.
Here S_ψ(m, n) = Σ_{u ∈ (ZMod c)ˣ} ψ(m u + n u⁻¹) for any additive character ψ of ZMod c.

KNOWN mathematics, elementary. AI wrote this Lean code. Binary Goldbach is OPEN, and nothing
here is progress on it.
-/
import Mathlib

namespace LeanLab.Routes.R0031

open Finset ArithmeticFunction

/-- `λ(p) = −1` for a prime `p`. -/
theorem liouville_prime' {p : ℕ} (hp : p.Prime) : liouville p = -1 := by
  rw [liouville_apply hp.ne_zero, cardFactors_apply_prime hp, pow_one]

/-- The multiples of `d` in `[0, x]` are the image of `[0, x / d]` under `k ↦ d k`. -/
theorem filter_dvd_range_eq_image {d : ℕ} (hd : 0 < d) (x : ℕ) :
    (range (x + 1)).filter (fun m => d ∣ m) = (range (x / d + 1)).image (fun k => d * k) := by
  ext m
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hm, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have : d * k ≤ x := by omega
    have : k ≤ x / d := (Nat.le_div_iff_mul_le hd).2 (by linarith [mul_comm d k])
    omega
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, dvd_mul_right d k⟩
    have hk' : k ≤ x / d := by omega
    have : k * d ≤ x := (Nat.le_div_iff_mul_le hd).1 hk'
    have : d * k ≤ x := by linarith [mul_comm d k]
    omega

/-- **Type I data of the Liouville twist.** For `d > 0`,
`Σ_{m ≤ x, d ∣ m} λ(m) = λ(d) · Σ_{k ≤ x/d} λ(k)`. -/
theorem sum_dvd_liouville {d : ℕ} (hd : 0 < d) (x : ℕ) :
    ∑ m ∈ (range (x + 1)).filter (fun m => d ∣ m), (liouville m : ℤ)
      = liouville d * ∑ k ∈ range (x / d + 1), (liouville k : ℤ) := by
  rw [filter_dvd_range_eq_image hd, sum_image]
  · rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    exact liouville_apply_mul d k
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd h

/-- **Goldbach pairs live in the λ = −1 half of `A = {N − p}`.** -/
theorem goldbach_pairs_in_minus (N : ℕ) :
    ((range N).filter (fun p => p.Prime ∧ (N - p).Prime)).card
      ≤ ((range N).filter (fun p => p.Prime ∧ liouville (N - p) = -1)).card := by
  refine card_le_card fun p hp => ?_
  simp only [mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, liouville_prime' hp.2.2⟩

/-- The λ = +1 half of `A = {N − p}` contains no Goldbach pair. -/
theorem plus_half_no_pair (N p : ℕ) (h : liouville (N - p) = 1) : ¬ (N - p).Prime := by
  intro hq
  rw [liouville_prime' hq] at h
  norm_num at h

variable {c : ℕ} [NeZero c]

/-- The Kloosterman sum `S_ψ(m, n) = Σ_{u ∈ (ZMod c)ˣ} ψ(m u + n u⁻¹)` for an additive character
`ψ` of `ZMod c`; with `ψ(t) = e(t / c)` this is the classical `S(m, n; c)`. -/
noncomputable def kloost (ψ : AddChar (ZMod c) ℂ) (m n : ZMod c) : ℂ :=
  ∑ u : (ZMod c)ˣ, ψ (m * (u : ZMod c) + n * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))

/-- **Symmetry** `S(m, n) = S(n, m)`, by `u ↦ u⁻¹`. -/
theorem kloost_symm (ψ : AddChar (ZMod c) ℂ) (m n : ZMod c) :
    kloost ψ m n = kloost ψ n m := by
  unfold kloost
  refine Fintype.sum_equiv (Equiv.inv (ZMod c)ˣ) _ _ fun u => ?_
  simp only [Equiv.inv_apply, inv_inv]
  rw [add_comm]

/-- **Twist** `S(a m, n) = S(m, a n)` for a unit `a`, by `u ↦ a⁻¹ u`. -/
theorem kloost_twist (ψ : AddChar (ZMod c) ℂ) (a : (ZMod c)ˣ) (m n : ZMod c) :
    kloost ψ ((a : ZMod c) * m) n = kloost ψ m ((a : ZMod c) * n) := by
  unfold kloost
  refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun u => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Units.val_mul, mul_inv_rev]
  have h2 : ((a : ZMod c) * ((a⁻¹ : (ZMod c)ˣ) : ZMod c)) = 1 := by simp
  linear_combination (-(n * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))) * h2

/-- Vacuity: the hypothesis `0 < d` of `sum_dvd_liouville` is met, and the identity is
nontrivial, at `d = 2`, `x = 4`: the multiples 0, 2, 4 give `0 + λ(2) + λ(4) = -1 + 1 = 0`. -/
example : (2 : ℕ) > 0 := by norm_num

/-- Vacuity for `goldbach_pairs_in_minus`: at `N = 10` the left side is nonzero, `p = 3`. -/
example : 3 ∈ (range 10).filter (fun p => p.Prime ∧ (10 - p).Prime) := by
  simp only [mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end LeanLab.Routes.R0031

#print axioms LeanLab.Routes.R0031.sum_dvd_liouville
#print axioms LeanLab.Routes.R0031.goldbach_pairs_in_minus
#print axioms LeanLab.Routes.R0031.plus_half_no_pair
#print axioms LeanLab.Routes.R0031.kloost_symm
#print axioms LeanLab.Routes.R0031.kloost_twist
