/-
Split of the OPEN leaf `upper_self_scaled_deleted_centred_prefix_bound` of
SPLIT_upper_self_scaled_principal_centred_prefix_bound into a MEDIUM leaf, a HARD leaf and a
proved conversion lemma, with an assembly that carries that same statement, proved from them and
using no sorry.

Source: P0069 Baker, Harman and Pintz 1997, Section 5, page 53. The deleted part of k_m at the
self scale Y = m counts m = p1 p2 p3 n4 with m^c1 ≤ p3 < p2 < p1 < m^c4, n4 free of primes below
p3, and the exponent triple in the deleted set E. The paper evaluates its mass by the prime number
theorem and partial summation, which sees m as a product of distinct primes times n4. Integers m
with a repeated prime factor p ≥ m^c1 are not counted correctly by that heuristic, and the paper
discards them silently as a lower order error.

Leaf 1, MEDIUM: the terms with m divisible by p^2 for some prime p ≥ m^c1 contribute O(Y^(1-c1)).
Leaf 2, HARD: the main part, m with no repeated prime factor above m^c1, has the centred prefix
bound at the density upperDeletedIntegral over log Y, by the PNT and partial summation.
Lemma, PROVED here: Y^(1-c1) is eventually below C Y (log x)^(-A) for every A.

This file adds no definition and edits no existing file. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_principal_centred_prefix_bound

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: repeated prime factors in the deleted part of k_m, P0069 page 53. MEDIUM, for Open
Math OS: on J, the terms with p^2 ∣ m for a prime p ≥ m^c1, weighted by log m over log Y, have mass
at most C Y^(1-c1). Bounded weight, at most (1/c1)^3 triples, and at most 2Y Σ_{p ≥ Y^c1} p^(-2)
plus (2Y)^(1/2) such m, with c1 about 1/8. Easier than the parent: a counting bound, no density.
Non-vacuity: m = q^2 r in J with q a prime near Y^c1. -/
theorem upper_self_scaled_deleted_repeated_prime_bound
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))‖ ≤
          C * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
  sorry

/-- LEAF: the main part of the deleted density of P0069 page 53, the set E not covered by
Lemma 33. HARD, for Codex: k_m minus its kept part at the self scale, restricted to m with no
repeated prime factor p ≥ m^c1 and weighted by log m over log Y, has on each segment from Y to t,
Y ≤ t ≤ 2Y, mass upperDeletedIntegral over log Y per element up to C Y (log x)^(-A). The prime
number theorem with de la Vallee Poussin error for p1, p2, p3 and the Buchstab asymptotic for the
cofactor n4, then partial summation to the triple integral over E. Easier than the parent: the
repeated prime terms are removed. Non-vacuity: at t = 2Y the segment is the whole interval. -/
theorem upper_self_scaled_deleted_squarefree_centred_prefix_bound
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 1 else 0)) : ℝ) : ℂ) -
            ((upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- Proved: the power saving Y^(1-c1) beats every power of log. -/
theorem upper_self_scaled_power_saving {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (A : ℝ) (hA : 0 < A) (C1 : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      C1 * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  set s : ℝ := 11 / 20 + ε with hs
  set c : ℝ := upperC1 ε with hc
  have hc0 : 0 < c := by rw [hc]; unfold upperC1; norm_num; linarith
  have hs0 : 0 < s := by rw [hs]; linarith
  have hlo := (isLittleO_log_rpow_rpow_atTop A (mul_pos hs0 hc0)).bound (c := 1) one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlo
  refine ⟨max (max N 2) |C1|, fun x hx => ?_⟩
  have hx2 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_right N 2) (le_max_left _ _)) hx
  have hxN : N ≤ x := le_trans (le_trans (le_max_left N 2) (le_max_left _ _)) hx
  have hC1 : |C1| ≤ max (max N 2) |C1| := le_max_right _ _
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hb := hN x hxN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hb
  have hlA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hl0 A
  have key : x ^ (-(s * c)) ≤ Real.log x ^ (-A) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hl0.le]
    exact inv_anti₀ hlA hb
  have hpow : (x ^ s) ^ (1 - c) = x ^ s * x ^ (-(s * c)) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; ring_nf
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx0.le _
  rw [hpow]
  calc C1 * (x ^ s * x ^ (-(s * c))) ≤ |C1| * (x ^ s * x ^ (-(s * c))) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C1| * (x ^ s * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hxs) (abs_nonneg _)
    _ ≤ max (max N 2) |C1| * (x ^ s * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- The statement of `upper_self_scaled_deleted_centred_prefix_bound` of the imported file,
verbatim, assembled from the two leaves and the proved power saving lemma: the deleted part splits
as the repeated prime part plus the main part, and the triangle inequality adds the bounds. -/
theorem upper_self_scaled_deleted_centred_prefix_bound_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) -
            ((upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := upper_self_scaled_deleted_repeated_prime_bound hε hε8
  obtain ⟨C2, hC2⟩ :=
    upper_self_scaled_deleted_squarefree_centred_prefix_bound h4 h9 hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := upper_self_scaled_power_saving hε hε8 A hA C1
  refine ⟨max (max (max C1 C2) C3) 1 + |C2| + |C3|, fun x hx t htl htu => ?_⟩
  have hab : 0 ≤ |C2| + |C3| := by positivity
  have hmx : max (max (max C1 C2) C3) 1 ≤ x := by linarith
  have hx1 : C1 ≤ x := le_trans (le_trans (le_trans (le_max_left C1 C2) (le_max_left _ C3))
    (le_max_left _ 1)) hmx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_trans (le_max_right C1 C2) (le_max_left _ C3))
    (le_max_left _ 1)) hmx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_right _ C3) (le_max_left _ 1)) hmx
  have hxo : (1 : ℝ) ≤ x := le_trans (le_max_right _ 1) hmx
  set L : ℝ := Real.log (x ^ (11 / 20 + ε)) with hL
  set d : ℝ := upperDeletedIntegral ω ε with hd
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) with hS
  have hsum : ∀ m ∈ S, ((((Real.log (m : ℝ) / L *
              (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) - ((d : ℝ) : ℂ) / (L : ℂ))) =
      ((((Real.log (m : ℝ) / L *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))
      + (((Real.log (m : ℝ) / L *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 1 else 0)) : ℝ) : ℂ) - ((d : ℝ) : ℂ) / (L : ℂ))) := by
    intro m _
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hxo) _)
  refine le_trans (norm_add_le _ _) ?_
  have e1 := hC1 x hx1 t htl htu
  have e2 := hC2 x hx2 t htl htu
  have e3 := hC3 x hx3
  have hc : C3 + C2 ≤ max (max (max C1 C2) C3) 1 + |C2| + |C3| := by
    have : (0:ℝ) ≤ max (max (max C1 C2) C3) 1 := le_trans (by norm_num) (le_max_right _ 1)
    linarith [le_abs_self C2, le_abs_self C3]
  calc _ ≤ C3 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := add_le_add (le_trans e1 e3) e2
    _ = (C3 + C2) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ (max (max (max C1 C2) C3) 1 + |C2| + |C3|) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hc hYL
    _ = _ := by ring

end LeanLab.BHP1997.Upper312Route
