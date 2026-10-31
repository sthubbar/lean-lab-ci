import LeanLab.LanguascoPerelli1996.Statements

/-!
The exponential weight Fourier identity used in P0071 page 354 display 11.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Kernel108
open Complex Real MeasureTheory Set

/-- LEAF. Page 354 display 11. The Fourier integral of exp of minus twice
the absolute value is exactly the Montgomery weight 4 divided by 4 plus t squared. -/
theorem integral_weight (t : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (Complex.I * t * v) * (Real.exp (-2 * |v|) : ℂ)) ∧
      (∫ v : ℝ, Complex.exp (Complex.I * t * v) * (Real.exp (-2 * |v|) : ℂ)) = (w t : ℂ) := by
  let k : ℝ → ℂ := fun v => Complex.exp (Complex.I * t * v) * (Real.exp (-2 * |v|) : ℂ)
  have hleft : EqOn k (fun v : ℝ => Complex.exp ((2 + Complex.I * t) * v)) (Iic 0) := by
    intro v hv
    dsimp [k]
    rw [abs_of_nonpos hv, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright : EqOn k (fun v : ℝ => Complex.exp ((Complex.I * t - 2) * v)) (Ioi 0) := by
    intro v hv
    dsimp [k]
    rw [abs_of_pos hv, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hl : IntegrableOn k (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (a := 2 + Complex.I * t) (by simp) 0).congr_fun
      hleft.symm measurableSet_Iic
  have hr : IntegrableOn k (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := Complex.I * t - 2) (by simp) 0).congr_fun
      hright.symm measurableSet_Ioi
  have hi : Integrable k := by
    have hh := integrableOn_union.mpr ⟨hl, hr⟩
    simpa only [Iic_union_Ioi, integrableOn_univ] using hh
  refine ⟨hi, ?_⟩
  change (∫ v : ℝ, k v) = (w t : ℂ)
  rw [← intervalIntegral.integral_Iic_add_Ioi hl hr]
  have hel : (∫ v : ℝ in Iic 0, k v) = 1 / (2 + Complex.I * t) := by
    calc
      _ = ∫ v : ℝ in Iic 0, Complex.exp ((2 + Complex.I * t) * v) :=
        setIntegral_congr_fun measurableSet_Iic hleft
      _ = _ := by simpa using integral_exp_mul_complex_Iic (a := 2 + Complex.I * t) (by simp) 0
  have her : (∫ v : ℝ in Ioi 0, k v) = -1 / (Complex.I * t - 2) := by
    calc
      _ = ∫ v : ℝ in Ioi 0, Complex.exp ((Complex.I * t - 2) * v) :=
        setIntegral_congr_fun measurableSet_Ioi hright
      _ = _ := by simpa using integral_exp_mul_complex_Ioi (a := Complex.I * t - 2) (by simp) 0
  rw [hel, her]
  have hp : (2 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hn : (Complex.I * t - 2 : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hreal : (4 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hc : (4 + (t : ℂ) ^ 2 : ℂ) ≠ 0 := by exact_mod_cast hreal
  unfold w
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq] <;> ring

end LeanLab.LanguascoPerelli1996.Kernel108
