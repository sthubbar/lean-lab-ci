import LeanLab.ExceptionalSet.Fejer467
import Mathlib.Analysis.PSeries

/-!
P0082 page370 displays40 and41. Finite Fourier transport and tail estimates.
The coefficient and approximation bounds are explicit hypotheses.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.FourierTransport553
open Finset

/-- P0082 page370 display41, finite weighted phase estimate. -/
theorem weighted_phase_le {ι : Type*} (s : Finset ι) (c φ : ι → ℂ)
    (U : ℝ) (hφ : ∀ i ∈ s, ‖φ i‖ ≤ U) :
    ‖∑ i ∈ s, c i * φ i‖ ≤ (∑ i ∈ s, ‖c i‖) * U := by
  calc
    _ ≤ ∑ i ∈ s, ‖c i * φ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖c i‖ * ‖φ i‖ := by simp only [norm_mul]
    _ ≤ ∑ i ∈ s, ‖c i‖ * U :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hφ i hi) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

/-- P0082 page370 after display41, a large approximated phase forces a
large unfiltered summand. This is the finite triangle implication. -/
theorem large_value_transport {ι : Type*} (s : Finset ι) (c φ : ι → ℂ)
    (Z : ℂ) (err L U : ℝ) (hU : 0 ≤ U)
    (happrox : ‖Z - ∑ i ∈ s, c i * φ i‖ ≤ err)
    (hc : (∑ i ∈ s, ‖c i‖) ≤ L) (hlarge : err + L * U < ‖Z‖) :
    ∃ i ∈ s, U < ‖φ i‖ := by
  classical
  by_contra hno
  push Not at hno
  have hsum := weighted_phase_le s c φ U hno
  have htriangle : ‖Z‖ ≤ ‖Z - ∑ i ∈ s, c i * φ i‖ + ‖∑ i ∈ s, c i * φ i‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (Z - ∑ i ∈ s, c i * φ i) (∑ i ∈ s, c i * φ i)
  have hc' := mul_le_mul_of_nonneg_right hc hU
  linarith

/-- P0082 page370 displays40 and41, finite transport with exact powers of E.
The approximation remains an explicit input. -/
theorem large_value_transport_rpow {ι : Type*} (s : Finset ι) (c φ : ι → ℂ)
    (Z : ℂ) (E C a b : ℝ) (N : ℕ) (hE : 0 < E) (_hC : 0 ≤ C)
    (happrox : ‖Z - ∑ i ∈ s, c i * φ i‖ ≤ N * E ^ (-a))
    (hc : (∑ i ∈ s, ‖c i‖) ≤ C * E ^ b)
    (hlarge : (C + 1) * N * E ^ (-a) < ‖Z‖) :
    ∃ i ∈ s, (N : ℝ) * E ^ (-(a + b)) < ‖φ i‖ := by
  apply large_value_transport s c φ Z (N * E ^ (-a)) (C * E ^ b)
    (N * E ^ (-(a + b))) (by positivity) happrox hc
  have he : E ^ b * E ^ (-(a + b)) = E ^ (-a) := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  convert hlarge using 1
  calc
    _ = N * E ^ (-a) + C * N * (E ^ b * E ^ (-(a + b))) := by ring
    _ = _ := by rw [he]; ring

/-- P0082 page370 display40, finite symmetric Fourier tail.
The two signs each use Mathlib's inverse square tail estimate. -/
theorem paired_fourier_tail (c φ : ℤ → ℂ) (H K : ℕ) (A Δ B : ℝ)
    (hA : 0 ≤ A) (hΔ : 0 < Δ) (hB : 0 ≤ B)
    (hcpos : ∀ h ∈ Finset.Ioo H K, ‖c h‖ ≤ A / (Δ * (h : ℝ) ^ 2))
    (hcneg : ∀ h ∈ Finset.Ioo H K, ‖c (-(h : ℤ))‖ ≤ A / (Δ * (h : ℝ) ^ 2))
    (hφpos : ∀ h ∈ Finset.Ioo H K, ‖φ h‖ ≤ B)
    (hφneg : ∀ h ∈ Finset.Ioo H K, ‖φ (-(h : ℤ))‖ ≤ B) :
    ‖∑ h ∈ Finset.Ioo H K, (c h * φ h + c (-(h : ℤ)) * φ (-(h : ℤ)))‖ ≤
      4 * A * B / (Δ * (H + 1)) := by
  have hterm (h : ℕ) (hh : h ∈ Finset.Ioo H K) :
      ‖c h * φ h + c (-(h : ℤ)) * φ (-(h : ℤ))‖ ≤
        (2 * A * B / Δ) * (((h : ℝ) ^ 2)⁻¹) := by
    calc
      _ ≤ ‖c h * φ h‖ + ‖c (-(h : ℤ)) * φ (-(h : ℤ))‖ := norm_add_le _ _
      _ = ‖c h‖ * ‖φ h‖ + ‖c (-(h : ℤ))‖ * ‖φ (-(h : ℤ))‖ := by simp only [norm_mul]
      _ ≤ (A / (Δ * (h : ℝ) ^ 2)) * B + (A / (Δ * (h : ℝ) ^ 2)) * B := by
        apply add_le_add
        · exact mul_le_mul (hcpos h hh) (hφpos h hh) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hcneg h hh) (hφneg h hh) (norm_nonneg _) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  calc
    _ ≤ ∑ h ∈ Finset.Ioo H K, ‖c h * φ h + c (-(h : ℤ)) * φ (-(h : ℤ))‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Ioo H K, (2 * A * B / Δ) * (((h : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum hterm
    _ = (2 * A * B / Δ) * ∑ h ∈ Finset.Ioo H K, (((h : ℝ) ^ 2)⁻¹) :=
      (Finset.mul_sum ..).symm
    _ ≤ (2 * A * B / Δ) * (2 / (H + 1)) :=
      mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le H K) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- P0082 page370 display40, the finite symmetric coefficient mass.
The zero coefficient and both inverse square tails cost at most five A over Delta. -/
theorem symmetric_coefficient_mass (c : ℤ → ℂ) (K : ℕ) (A Δ : ℝ)
    (hA : 0 ≤ A) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hc0 : ‖c 0‖ ≤ A)
    (hcpos : ∀ h ∈ Finset.Ioo 0 K, ‖c h‖ ≤ A / (Δ * (h : ℝ) ^ 2))
    (hcneg : ∀ h ∈ Finset.Ioo 0 K, ‖c (-(h : ℤ))‖ ≤ A / (Δ * (h : ℝ) ^ 2)) :
    ‖c 0‖ + (∑ h ∈ Finset.Ioo 0 K, (‖c h‖ + ‖c (-(h : ℤ))‖)) ≤ 5 * A / Δ := by
  have h0 : A ≤ A / Δ := (le_div_iff₀ hΔ).mpr (by nlinarith)
  have htail : (∑ h ∈ Finset.Ioo 0 K, (‖c h‖ + ‖c (-(h : ℤ))‖)) ≤ 4 * A / Δ := by
    calc
      _ ≤ ∑ h ∈ Finset.Ioo 0 K, (2 * A / Δ) * (((h : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ ≤ A / (Δ * (h : ℝ) ^ 2) + A / (Δ * (h : ℝ) ^ 2) :=
            add_le_add (hcpos h hh) (hcneg h hh)
          _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = (2 * A / Δ) * ∑ h ∈ Finset.Ioo 0 K, (((h : ℝ) ^ 2)⁻¹) := (Finset.mul_sum ..).symm
      _ ≤ (2 * A / Δ) * (2 / ((0 : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 K)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ A / Δ + 4 * A / Δ := add_le_add (hc0.trans h0) htail
    _ = _ := by ring

end LeanLab.ExceptionalSet.FourierTransport553
