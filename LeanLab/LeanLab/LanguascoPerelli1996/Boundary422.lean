import LeanLab.LanguascoPerelli1996.Window422

/-!
P0071 page 359, the need to retain both clipped Gallagher boundaries.
These are exact instances of the existing stopped remainder.
They are not counterexamples to any theorem of the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Boundary422
open Real MeasureTheory intervalIntegral

/-- Page 359 boundary correction, derived exact instance.
At X equal to four and Y equal to one, the leading and trailing window
masses are both one and the interior mass is zero. -/
theorem boundary_values :
    Window422.leadingMass 4 1 1 1 2 = 1 ∧
      Window422.interiorMass 4 1 1 1 2 = 0 ∧
        Window422.trailingMass 4 1 1 1 2 = 1 := by
  norm_num [Window422.leadingMass, Window422.interiorMass, Window422.trailingMass,
    LeanLab.PNTPort.Gallagher.win, Window422.coeff, muPhi, Finset.sum_filter, Finset.sum_range_succ]

/-- Page 359 boundary correction, derived obstruction.
No uniform multiple of the interior mass alone bounds all three masses.
This rules out deleting the two boundary obligations in Decomp422a. -/
theorem no_interior_only_transfer :
    ¬ ∃ C : ℝ, ∀ X Y : ℝ, ∀ q a L : ℕ,
      Window422.leadingMass X Y q a L + Window422.interiorMass X Y q a L +
        Window422.trailingMass X Y q a L ≤ C * Window422.interiorMass X Y q a L := by
  rintro ⟨C, hC⟩
  have h := hC 4 1 1 1 2
  rcases boundary_values with ⟨h1, h2, h3⟩
  rw [h1, h2, h3] at h
  norm_num at h

/-- Page 358 display 21, a genuine nonzero stopped remainder.
Its mass is twice the positive arc radius, even though the integer
interior window mass in boundary_values vanishes. -/
theorem single_term_mass (ξ : ℝ) :
    (∫ t in (-ξ)..ξ, ‖Decomp381a.partialR 4 1 t 1 1‖ ^ 2) = 2 * ξ := by
  have he (t : ℝ) : ‖e t‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  have hp (t : ℝ) : ‖Decomp381a.partialR 4 1 t 1 1‖ ^ 2 = 1 := by
    norm_num [Decomp381a.partialR, muPhi, he]
  simp_rw [hp]
  simp
  <;> ring

/-- Derived nonzero interior instance for page 356 display 14.
The single interior coefficient at n equal to two is log two minus one. -/
theorem interior_value :
    Window422.interiorMass 4 2 1 1 1 = (Real.log 2 - 1) ^ 2 := by
  have he : e 2 = 1 := by
    unfold e
    convert Complex.exp_nat_mul_two_pi_mul_I 2 using 1 <;> push_cast <;> ring
  norm_num [Window422.interiorMass, LeanLab.PNTPort.Gallagher.win,
    Window422.coeff, muPhi, Finset.sum_filter, Finset.sum_range_succ,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, he]
  have hl : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hl]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Derived vacuity check for the interior leaf from page 356 display 14.
The interior mass can be strictly positive for the actual arithmetic coefficients. -/
theorem interior_positive : 0 < Window422.interiorMass 4 2 1 1 1 := by
  rw [interior_value]
  have hh : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr hh.ne)

end LeanLab.LanguascoPerelli1996.Boundary422

#print axioms LeanLab.LanguascoPerelli1996.Boundary422.boundary_values
#print axioms LeanLab.LanguascoPerelli1996.Boundary422.no_interior_only_transfer
#print axioms LeanLab.LanguascoPerelli1996.Boundary422.single_term_mass
#print axioms LeanLab.LanguascoPerelli1996.Boundary422.interior_value
#print axioms LeanLab.LanguascoPerelli1996.Boundary422.interior_positive
