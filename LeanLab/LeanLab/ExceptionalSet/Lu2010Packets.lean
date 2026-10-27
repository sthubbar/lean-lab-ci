/-
P0095 Lu 2010, equation 63 on page 2379.
CODEX task47, unit U-8092. AI wrote this Lean code. Binary Goldbach is open.

Finite weighted energy and the inverse-cube sum over multiples of a conductor.
The weights in the intended application come from the zero integrals of equation 63.
No analytic zero-density bound is asserted here.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Lu2010Packets
open Finset

/-- Cauchy Schwarz for a finite weighted family of complex coefficients. -/
theorem weighted_norm_sq {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * z i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
  have htri : ‖∑ i ∈ s, (w i : ℂ) * z i‖ ≤ ∑ i ∈ s, w i * ‖z i‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply sum_le_sum
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  intro i hi
  nlinarith [sq_nonneg (w i * ‖z i‖)]

/-- A common energy bound for the packets gives the square of their total weight. -/
theorem weighted_packet_energy {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (w : ι → ℝ) (z : ι → κ → ℂ) {H : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hE : ∀ i ∈ s, ∑ k ∈ t, ‖z i k‖ ^ 2 ≤ H) :
    ∑ k ∈ t, ‖∑ i ∈ s, (w i : ℂ) * z i k‖ ^ 2 ≤
      (∑ i ∈ s, w i) ^ 2 * H := by
  calc (∑ k ∈ t, ‖∑ i ∈ s, (w i : ℂ) * z i k‖ ^ 2)
      ≤ ∑ k ∈ t, (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i k‖ ^ 2 :=
        sum_le_sum fun k _ => weighted_norm_sq s w (fun i => z i k) hw
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ∑ k ∈ t, ‖z i k‖ ^ 2 := by
      rw [← mul_sum, sum_comm]
      simp_rw [mul_sum]
    _ ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * H := by
      apply mul_le_mul_of_nonneg_left _ (sum_nonneg hw)
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hE i hi) (hw i hi)
    _ = (∑ i ∈ s, w i) ^ 2 * H := by rw [← sum_mul]; ring

/-- The elementary inverse-cube sum is at most 2. -/
theorem sum_inv_cube_le_two (Q : ℕ) :
    ∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 3 ≤ 2 := by
  calc (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 3)
      ≤ ∑ m ∈ Icc 1 Q, ((m : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
        rw [one_div]
        apply inv_anti₀ (by positivity)
        nlinarith [sq_nonneg (m : ℝ)]
    _ = ∑ m ∈ Ioo 0 (Q + 1), ((m : ℝ) ^ 2)⁻¹ := by
      congr 1
    _ ≤ 2 := by simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (Q + 1)

/-- Multiples of r gain r cubed in the inverse-cube sum. -/
theorem sum_multiples_inv_cube {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) :
    ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), 1 / (q : ℝ) ^ 3 ≤ 2 / (r : ℝ) ^ 3 := by
  classical
  let s := (Icc 1 Q).filter (fun q => r ∣ q)
  have hr0 : 0 < r := by omega
  have hinj : Set.InjOn (fun q => q / r) s := by
    intro q hq q' hq' he
    have hq := (mem_filter.mp hq).2
    have hq' := (mem_filter.mp hq').2
    have h1 : r * (q / r) = q := Nat.mul_div_cancel' hq
    have h2 : r * (q' / r) = q' := Nat.mul_div_cancel' hq'
    change q / r = q' / r at he
    rw [← h1, ← h2, he]
  have hsub : s.image (fun q => q / r) ⊆ Icc 1 Q := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
    obtain ⟨hqI, hd⟩ := mem_filter.mp hq
    obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hqI
    have he : r * (q / r) = q := Nat.mul_div_cancel' hd
    have hm1 : 1 ≤ q / r := by nlinarith
    exact mem_Icc.mpr ⟨hm1, (Nat.div_le_self q r).trans hqQ⟩
  have he : (∑ q ∈ s, 1 / (q : ℝ) ^ 3) =
      (1 / (r : ℝ) ^ 3) * ∑ m ∈ s.image (fun q => q / r), 1 / (m : ℝ) ^ 3 := by
    rw [sum_image hinj, mul_sum]
    apply sum_congr rfl
    intro q hq
    have hqdiv := (mem_filter.mp hq).2
    have hqmul : r * (q / r) = q := Nat.mul_div_cancel' hqdiv
    have hqreal : (q : ℝ) = (r : ℝ) * (q / r : ℕ) := by exact_mod_cast hqmul.symm
    rw [hqreal, mul_pow, one_div_mul_one_div]
  change (∑ q ∈ s, 1 / (q : ℝ) ^ 3) ≤ _
  rw [he]
  calc (1 / (r : ℝ) ^ 3) * ∑ m ∈ s.image (fun q => q / r), 1 / (m : ℝ) ^ 3
      ≤ (1 / (r : ℝ) ^ 3) * ∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (1 / (r : ℝ) ^ 3) * 2 :=
      mul_le_mul_of_nonneg_left (sum_inv_cube_le_two Q) (by positivity)
    _ = 2 / (r : ℝ) ^ 3 := by ring

end LeanLab.ExceptionalSet.Lu2010Packets

#print axioms LeanLab.ExceptionalSet.Lu2010Packets.weighted_norm_sq
#print axioms LeanLab.ExceptionalSet.Lu2010Packets.weighted_packet_energy
#print axioms LeanLab.ExceptionalSet.Lu2010Packets.sum_inv_cube_le_two
#print axioms LeanLab.ExceptionalSet.Lu2010Packets.sum_multiples_inv_cube
