/-
Holder interpolation in Shao 1206.6139v2 page 14, Lemma 4.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset

namespace LeanLab.DensityGoldbach.Holder408

/-- Shao page 14, Holder step in Lemma 4.3.
Weighted arithmetic geometric mean supplies the three exponents. -/
theorem young_three (a b d q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hq : 2 < q) :
    a * b * d ^ (q - 2) ≤ (a ^ q + b ^ q + (q - 2) * d ^ q) / q := by
  have hq0 : 0 < q := by linarith
  have hw : 1 / q + 1 / q + (q - 2) / q = 1 := by field_simp; ring
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1 / q) (w₂ := 1 / q) (w₃ := (q - 2) / q)
    (p₁ := a ^ q) (p₂ := b ^ q) (p₃ := d ^ q)
    (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hw
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x ^ q) ^ (1 / q) = x := by
    rw [one_div, Real.rpow_rpow_inv hx hq0.ne']
  have hdq : (d ^ q) ^ ((q - 2) / q) = d ^ (q - 2) := by
    rw [← Real.rpow_mul hd]
    congr 1
    field_simp
  rw [hpow a ha, hpow b hb, hdq] at h
  convert h using 1 <;> ring

/-- Shao page 14, interpolation before and after the Holder step.
A uniform bound on d gives the power epsilon to 3 - q. -/
theorem product_sum_le {ι : Type*} (s : Finset ι) (a b d : ι → ℝ) (q ε K : ℝ)
    (hq2 : 2 < q) (hq3 : q < 3) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hsup : ∀ i ∈ s, d i ≤ ε)
    (hsa : ∑ i ∈ s, a i ^ q ≤ K) (hsb : ∑ i ∈ s, b i ^ q ≤ K)
    (hsd : ∑ i ∈ s, d i ^ q ≤ K) :
    ∑ i ∈ s, a i * b i * d i ≤ ε ^ (3 - q) * K := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 ≤ q - 2 := by linarith
  have hpoint : ∀ i ∈ s, a i * b i * d i ≤ ε ^ (3 - q) *
      ((a i ^ q + b i ^ q + (q - 2) * d i ^ q) / q) := by
    intro i hi
    have hid : d i = d i ^ (3 - q) * d i ^ (q - 2) := by
      rw [← Real.rpow_add' (hd i hi) (by linarith), show 3 - q + (q - 2) = 1 by ring,
        Real.rpow_one]
    calc
      a i * b i * d i = d i ^ (3 - q) * (a i * b i * d i ^ (q - 2)) := by
        conv_lhs => rw [hid]
        ring
      _ ≤ ε ^ (3 - q) * ((a i ^ q + b i ^ q + (q - 2) * d i ^ q) / q) :=
        mul_le_mul (Real.rpow_le_rpow (hd i hi) (hsup i hi) (by linarith))
          (young_three _ _ _ _ (ha i hi) (hb i hi) (hd i hi) hq2)
          (mul_nonneg (mul_nonneg (ha i hi) (hb i hi)) (Real.rpow_nonneg (hd i hi) _))
          (Real.rpow_nonneg hε _)
  calc
    (∑ i ∈ s, a i * b i * d i) ≤ ∑ i ∈ s, ε ^ (3 - q) *
        ((a i ^ q + b i ^ q + (q - 2) * d i ^ q) / q) := sum_le_sum hpoint
    _ = ε ^ (3 - q) * (((∑ i ∈ s, a i ^ q) + (∑ i ∈ s, b i ^ q) +
        (q - 2) * ∑ i ∈ s, d i ^ q) / q) := by
      rw [← mul_sum, ← sum_div, sum_add_distrib, sum_add_distrib, ← mul_sum]
    _ ≤ ε ^ (3 - q) * ((K + K + (q - 2) * K) / q) := by
      gcongr
    _ = ε ^ (3 - q) * K := by
      congr 1
      field_simp
      <;> ring

end LeanLab.DensityGoldbach.Holder408

#print axioms LeanLab.DensityGoldbach.Holder408.young_three
#print axioms LeanLab.DensityGoldbach.Holder408.product_sum_le
