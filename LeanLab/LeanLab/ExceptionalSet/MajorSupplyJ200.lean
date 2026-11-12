import LeanLab.ExceptionalSet.Decomp404b

/-!
Upstream supply of the major arc Fourier identity for `DecompJ200.leaf_major_identity`.
Source: P0082, Brüdern and Perelli 1998, https://doi.org/10.5802/aif.1621, page 357 displays 7
and 8, specialized on page 364 display 23.
The proofs are copies of `Decomp371a.Sp_periodic`, `Decomp371a.majorArcs_periodic` and of
`Decomp404a.major_periodic` to `Decomp404a.major_integral_formula`, placed here so that
`DecompJ200` can import them without an import cycle. They use only the explicit kernel.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.MajorSupplyJ200

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.U1539

/-- P0082 page 357, the prime sum preceding display 6, is periodic with period one. -/
theorem Sp_periodic (P X : ℝ) : Function.Periodic (Sp P X) 1 := by
  intro α
  unfold Sp
  apply Finset.sum_congr rfl
  intro p hp
  have he : eC ((α + 1) * (p : ℝ)) = eC (α * (p : ℝ)) := by
    unfold eC
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (((α : ℂ) + 1) * (p : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I * ((α : ℂ) * (p : ℂ)) + (p : ℂ) * (2 * Real.pi * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [he]

/-- P0082 page 357 major arc definition: translation by one preserves the major arcs. -/
theorem majorArcs_periodic (P X : ℝ) : Function.Periodic (majorArcs P X) 1 := by
  intro α
  apply propext
  constructor
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a - q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_sub_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring
  · rintro ⟨q, a, hq, hqP, hcop, hclose⟩
    refine ⟨q, a + q, hq, hqP, ?_, ?_⟩
    · simpa only [Int.gcd_add_self_left] using hcop
    · convert hclose using 1 <;> push_cast <;> congr 1 <;> ring

/-- P0082 page 357 display 8. The major arc indicator times S squared
has period one. -/
theorem major_periodic (P X : ℝ) :
    Function.Periodic ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) 1 := by
  classical
  intro α
  have hmem : α + 1 ∈ majorArcs P X ↔ α ∈ majorArcs P X := by
    exact Iff.of_eq (majorArcs_periodic P X α)
  simp only [Set.indicator_apply, hmem, Sp_periodic P X α]

/-- P0082 page 357 display 8. The major arc indicator times S squared
is integrable on one period. -/
theorem major_intervalIntegrable (P X : ℝ) :
    IntervalIntegrable ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) volume 0 1 := by
  have hc : Continuous (fun α : ℝ => Sp P X α ^ 2) := by
    unfold Sp eC
    fun_prop
  exact ⟨(hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (PrimeKernel264.measurableSet_majorArcs P X),
    by simp⟩

/-- P0082 page 357 display 7. The Fourier coefficient of the indicated
prime square is precisely R1 with the same integer frequency. -/
theorem major_hcheck (P X : ℝ) (m : ℤ) :
    hcheck ((majorArcs P X).indicator (fun α => Sp P X α ^ 2)) m = R1 P X m := by
  classical
  unfold hcheck R1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : (fun α : ℝ => (majorArcs P X).indicator (fun α => Sp P X α ^ 2) α *
      eC (-(α * m))) = (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * eC (-(α * m))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [hα]
  rw [he, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (PrimeKernel264.measurableSet_majorArcs P X), Set.inter_comm]

/-- P0082 page 357 display 8. The weighted major integral is the sum
of its two adjacent integer coefficients times the explicit trapezoid weights. -/
theorem major_integral_formula (P X Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∫ α in majorArcs P X, Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) =
      (KernelTransform264.weight Δ (Int.fract v) : ℂ) * R1 P X ⌊v⌋ +
        (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) * R1 P X (⌊v⌋ + 1) := by
  classical
  let h : ℝ → ℂ := (majorArcs P X).indicator (fun α => Sp P X α ^ 2)
  let K : ℝ → ℂ := fun α => (Kfun Δ α : ℂ)
  have hmeas := PrimeKernel264.measurableSet_majorArcs P X
  have he : (fun α : ℝ => h α * K α * eC (-(α * v))) =
      (majorArcs P X).indicator (fun α => Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) := by
    ext α
    by_cases hα : α ∈ majorArcs P X <;> simp [h, K, hα]
  have hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v))) := by
    rw [he]
    exact (PrimeKernel264.total_integrable hΔ hΔ1 P X v).indicator hmeas
  have hfold := Decomp404b.fold_of_integrable h K (major_periodic P X) v hg
  rw [he, integral_indicator hmeas] at hfold
  rw [hfold]
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
    apply (major_intervalIntegrable P X).mul_continuousOn
    unfold eC
    fun_prop
  calc
    _ = ∫ α in (0 : ℝ)..1,
        (h α * eC (-(α * (⌊v⌋ : ℝ)))) * (KernelTransform264.weight Δ (Int.fract v) : ℂ) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) *
            (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only [K]
      rw [Decomp404b.poisson_kernel Δ v α hΔ hΔ1]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (KernelTransform264.weight Δ (Int.fract v) : ℂ))
        (hg1.mul_const (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ)),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      change hcheck h ⌊v⌋ * _ + hcheck h (⌊v⌋ + 1) * _ = _
      rw [major_hcheck, major_hcheck]
      ring

end LeanLab.ExceptionalSet.MajorSupplyJ200
