import LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP3

/-!
AI wrote this Lean code, burst S117 burst-20261122 final round. Binary Goldbach is open.
Split of `Decomp243aFeed1122LowerP3.leaf_linearDensity_totient`, the density condition of
Iwaniec Kowalski 6.34 for `g(p) = 1/(p-1)` on the odd sifting primes of BJS
https://arxiv.org/abs/2207.09452 p. 43 equation 142, into Mertens' product theorem in block
form and the convergent extra factor `∏ (1 + 1/(p(p-2)))`, via the exact identity
`(1 - 1/(p-1))⁻¹ = (1 - 1/p)⁻¹ (1 + 1/(p(p-2)))` for `p ≥ 3`.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP4

open Finset Real
open LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower

noncomputable section

/-- LEAF: Mertens' third theorem in block form, Iwaniec Kowalski equation 6.34 with
`g(p) = 1/p`, Mertens 1874, restricted to any finite set of primes in `[w, w')`; the local
factors are at least `1`, so it follows from the full block, compare the PROVED
`LeanLab.AlmostPrimes.Decomp1528b.mertens3_block` up to endpoint conventions and the bound
`exp(c/log w) ≤ 1 + K/log w`. Class MEDIUM. -/
theorem leaf_mertens_block_subset :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ℕ) (w w' : ℝ), 2 ≤ w → w < w' →
      (∀ p ∈ S, p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < w') →
      ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ log w' / log w * (1 + K / log w) := by
  sorry

/-- LEAF: the tail of the convergent product `∏_{p ≥ w, p > 2} (1 + 1/(p(p-2)))` is
`1 + O(1/w)`, hence `1 + O(1/log w)`, Halberstam Richert p. 142 remark on `Ω₂(1)`, for any
finite set of odd primes at least `w`. Class EASY. -/
theorem leaf_extra_factor_tail :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ℕ) (w : ℝ), 2 ≤ w →
      (∀ p ∈ S, p.Prime ∧ 2 < p ∧ w ≤ (p : ℝ)) →
      ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤ 1 + K / log w := by
  sorry

/-- The local identity `(1 - 1/(p-1))⁻¹ = (1 - 1/p)⁻¹ (1 + 1/(p(p-2)))` for `p ≥ 3`. -/
theorem local_factor_split {p : ℝ} (hp : 3 ≤ p) :
    (1 - 1 / (p - 1))⁻¹ = (1 - 1 / p)⁻¹ * (1 + 1 / (p * (p - 2))) := by
  have h1 : p - 1 ≠ 0 := by intro h; linarith
  have h2 : p - 2 ≠ 0 := by intro h; linarith
  have h0 : p ≠ 0 := by intro h; linarith
  have h3 : 1 - 1 / (p - 1) = (p - 2) / (p - 1) := by field_simp; ring
  have h4 : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [h3, h4, inv_div, inv_div]
  field_simp
  ring

/-- Every prime factor of the sifting primorial is odd. -/
theorem two_lt_of_mem_primeFactors {N : ℕ} {θ : ℝ} {p : ℕ}
    (hp : p ∈ (sievePrimorial N θ).primeFactors) : 2 < p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  unfold sievePrimorial at hd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).mp hd
  obtain ⟨-, hq1, hq2, -⟩ := mem_filter.mp hq
  rw [(Nat.prime_dvd_prime_iff_eq hpp hq1).mp hpq]
  exact hq2

/-- `leaf_linearDensity_totient` with the same statement, from the two leaves. -/
theorem leaf_linearDensity_totient_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (w w' : ℝ), 2 ≤ w → w < w' →
      ∏ p ∈ (sievePrimorial N ((1 : ℝ) / 8)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ log w' / log w * (1 + K / log w) := by
  obtain ⟨K1, hK1, hM⟩ := leaf_mertens_block_subset
  obtain ⟨K2, hK2, hE⟩ := leaf_extra_factor_tail
  refine ⟨K1 + K2 + K1 * K2 / log 2, by positivity, fun N w w' hw hww' => ?_⟩
  set S := (sievePrimorial N ((1 : ℝ) / 8)).primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w')
  have hmem : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < w' := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp1, two_lt_of_mem_primeFactors hp1, hp2, hp3⟩
  have hsplit : ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ =
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by
      have := (hmem p hp).2.1; exact_mod_cast this
    exact local_factor_split h3
  have hA := hM S w w' hw hww' (fun p hp => ⟨(hmem p hp).1, (hmem p hp).2.2⟩)
  have hB := hE S w hw (fun p hp => ⟨(hmem p hp).1, (hmem p hp).2.1, (hmem p hp).2.2.1⟩)
  have hBnn : 0 ≤ ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    refine prod_nonneg fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by
      have := (hmem p hp).2.1; exact_mod_cast this
    have : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
      apply div_nonneg zero_le_one; nlinarith
    linarith
  have hL2 : 0 < log 2 := log_pos (by norm_num)
  have hLw : log 2 ≤ log w := log_le_log (by norm_num) hw
  have hL : 0 < log w := lt_of_lt_of_le hL2 hLw
  have hL' : 0 < log w' := log_pos (by linarith)
  have hR1 : 0 ≤ log w' / log w * (1 + K1 / log w) := by positivity
  rw [hsplit]
  calc (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))
      ≤ (log w' / log w * (1 + K1 / log w)) * (1 + K2 / log w) :=
        mul_le_mul hA hB hBnn hR1
    _ ≤ log w' / log w * (1 + (K1 + K2 + K1 * K2 / log 2) / log w) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hq : K1 * K2 / log w / log w ≤ K1 * K2 / log 2 / log w := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact div_le_div_of_nonneg_left (by positivity) hL2 hLw
        have : (1 + K1 / log w) * (1 + K2 / log w) =
            1 + (K1 + K2) / log w + K1 * K2 / log w / log w := by
          field_simp; ring
        rw [this]
        have : 1 + (K1 + K2 + K1 * K2 / log 2) / log w =
            1 + (K1 + K2) / log w + K1 * K2 / log 2 / log w := by
          field_simp; ring
        rw [this]; linarith

end

end LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP4
