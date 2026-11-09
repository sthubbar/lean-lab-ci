import LeanLab.LanguascoPerelli1996.FiniteEnergy108

/-!
Derived interpolation step for P0071 page 355 display 13.
The second frequency moment uses symmetric height cutoffs.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Interpolation318
open Complex Real MeasureTheory

/-- Page 355 display 13, derived notation for the full weighted squared mass. -/
noncomputable def mass {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) : ℝ :=
  ∫ v : ℝ, ‖∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
    Real.exp (-2 * |v|)

/-- Page 355 display 13, derived positivity of the weighted squared mass. -/
theorem mass_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    0 ≤ mass s c γ :=
  integral_nonneg fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- Page 355 display 13, derived kernel calculation for interpolation.
The weight satisfies t squared times w of t equals four minus four w of t. -/
theorem kernel_interpolation (x y r : ℝ) :
    (((x ^ 2 - r) * (y ^ 2 - r)) * w (x - y)) =
      x ^ 2 * y ^ 2 * w (x - y) + (r ^ 2 + 4 * r) * w (x - y) -
        2 * r * (x * y * w (x - y)) - 4 * r := by
  unfold w
  have h : 4 + (x - y) ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Page 355 display 13, derived finite kernel identity.
The nonnegative square on the left removes the signed frequency obstacle. -/
theorem mass_interpolation_identity {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (γ : ι → ℝ) (r : ℝ) :
    mass s (fun i => ((γ i ^ 2 - r : ℝ) : ℂ) * c i) γ =
      mass s (fun i => (γ i : ℂ) ^ 2 * c i) γ + (r ^ 2 + 4 * r) * mass s c γ -
        2 * r * mass s (fun i => (γ i : ℂ) * c i) γ -
          4 * r * ‖∑ i ∈ s, c i‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have h0 := (FiniteEnergy108.finite_energy_identity s c γ).2
  have h1 := (FiniteEnergy108.finite_energy_identity s (fun i => (γ i : ℂ) * c i) γ).2
  have h2 := (FiniteEnergy108.finite_energy_identity s (fun i => (γ i : ℂ) ^ 2 * c i) γ).2
  have hr := (FiniteEnergy108.finite_energy_identity s
    (fun i => ((γ i ^ 2 - r : ℝ) : ℂ) * c i) γ).2
  change (mass s c γ : ℂ) = _ at h0
  change (mass s (fun i => (γ i : ℂ) * c i) γ : ℂ) = _ at h1
  change (mass s (fun i => (γ i : ℂ) ^ 2 * c i) γ : ℂ) = _ at h2
  change (mass s (fun i => ((γ i ^ 2 - r : ℝ) : ℂ) * c i) γ : ℂ) = _ at hr
  push_cast at hr ⊢
  have hn (z : ℂ) : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hns : (‖∑ i ∈ s, c i‖ : ℂ) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) := by
    rw [hn, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hr, h2, h0, h1, hns]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal]
  have hk := congrArg (fun t : ℝ => (t : ℂ)) (kernel_interpolation (γ i) (γ j) r)
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat] at hk
  linear_combination (c i * starRingEnd ℂ (c j)) * hk

/-- Page 355 display 13, derived weighted interpolation inequality.
Only the zeroth and second frequency moments occur on the right. -/
theorem mass_interpolation {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (γ : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    2 * r * mass s (fun i => (γ i : ℂ) * c i) γ ≤
      mass s (fun i => (γ i : ℂ) ^ 2 * c i) γ + (r ^ 2 + 4 * r) * mass s c γ := by
  have hid := mass_interpolation_identity s c γ r
  have hp := mass_nonneg s (fun i => ((γ i ^ 2 - r : ℝ) : ℂ) * c i) γ
  nlinarith [sq_nonneg ‖∑ i ∈ s, c i‖]

/-- Page 355 display 13, derived first moment bound from symmetric even moments. -/
theorem mass_first_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ)
    {T M : ℝ} (hT : 1 ≤ T) (hM : 0 ≤ M)
    (h0 : mass s c γ ≤ M)
    (h2 : mass s (fun i => (γ i : ℂ) ^ 2 * c i) γ ≤ 4 * T ^ 4 * M) :
    mass s (fun i => (γ i : ℂ) * c i) γ ≤ 5 * T ^ 2 * M := by
  have ht : 1 ≤ T ^ 2 := by nlinarith
  have hp := mass_interpolation s c γ (r := T ^ 2) (sq_nonneg T)
  have hmul := mul_le_mul_of_nonneg_left h0 (show 0 ≤ (T ^ 2) ^ 2 + 4 * T ^ 2 by positivity)
  have habs : T ^ 2 * M ≤ T ^ 4 * M := by
    have hh := mul_le_mul_of_nonneg_right (show T ^ 2 ≤ T ^ 4 by nlinarith [sq_nonneg (T ^ 2 - 1)]) hM
    exact hh
  have hb : 2 * T ^ 2 * mass s (fun i => (γ i : ℂ) * c i) γ ≤
      (2 * T ^ 2) * (5 * T ^ 2 * M) := by
    nlinarith [mul_nonneg (show 0 ≤ T ^ 4 by positivity) hM]
  exact le_of_mul_le_mul_left hb (by positivity)

end LeanLab.LanguascoPerelli1996.Interpolation318

#print axioms LeanLab.LanguascoPerelli1996.Interpolation318.mass_nonneg
#print axioms LeanLab.LanguascoPerelli1996.Interpolation318.kernel_interpolation
#print axioms LeanLab.LanguascoPerelli1996.Interpolation318.mass_interpolation_identity
#print axioms LeanLab.LanguascoPerelli1996.Interpolation318.mass_interpolation

#print axioms LeanLab.LanguascoPerelli1996.Interpolation318.mass_first_le
