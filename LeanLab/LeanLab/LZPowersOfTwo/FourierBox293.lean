/-
A box-transform input for the Fourier identity in P0079 display 11.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.KernelBounds293

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, display 11. The elementary centered-box transform is
eta times sinc of pi eta alpha. This is an input to the squared-kernel identity. -/
theorem character_interval293 (η α : ℝ) :
    (∫ u in -(η / 2)..(η / 2), character293 (u * α)) =
      ((η * Real.sinc (Real.pi * η * α) : ℝ) : ℂ) := by
  by_cases hα : α = 0
  · simp [hα, character293, intervalIntegral.integral_const]

  let c : ℝ := 2 * Real.pi * α
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα
  have heq : (fun u : ℝ => character293 (u * α)) =
      (fun u : ℝ => Complex.exp ((c * u : ℝ) * Complex.I)) := by
    funext u
    unfold character293
    rw [show 2 * Real.pi * (u * α) = c * u by dsimp [c]; ring]
  rw [heq, intervalIntegral.integral_comp_mul_left (fun u : ℝ => Complex.exp (u * Complex.I)) hc]
  rw [show c * -(η / 2) = -(c * (η / 2)) by ring, integral_exp_mul_I_eq_sinc]
  have harg : c * (η / 2) = Real.pi * η * α := by dsimp [c]; ring
  rw [harg]
  have hcoeff : c⁻¹ * (2 * (Real.pi * η * α)) = η := by
    dsimp [c]
    field_simp

  rw [Complex.real_smul]
  have hcoeff' := congrArg (fun r : ℝ => (r : ℂ)) hcoeff
  push_cast at hcoeff' ⊢
  linear_combination hcoeff' * (Real.sinc (Real.pi * η * α) : ℂ)

/-- P0079 page 4, the kernel definition. The kernel is the squared norm of
the centered-box transform. -/
theorem kernel_eq_box_norm_sq293 (η α : ℝ) :
    kernel293 η α = ‖∫ u in -(η / 2)..(η / 2), character293 (u * α)‖ ^ 2 := by
  rw [character_interval293, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

/-- P0079 page 4, display 11. The overlap of two centered boxes is the tent
function. This is the real convolution calculation behind the kernel identity. -/
theorem box_overlap293 (η t : ℝ) :
    (∫ u : ℝ, (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) u *
      (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) (t - u)) =
      max 0 (η - |t|) := by
  have hid : (fun u : ℝ => (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) u *
      (Set.Icc (-(η / 2)) (η / 2)).indicator (fun _ => (1 : ℝ)) (t - u)) =
      (Set.Icc (max (-(η / 2)) (t - η / 2)) (min (η / 2) (t + η / 2))).indicator
        (fun _ => (1 : ℝ)) := by
    funext u
    have hcond : (u ∈ Set.Icc (-(η / 2)) (η / 2) ∧ t - u ∈ Set.Icc (-(η / 2)) (η / 2)) ↔
        u ∈ Set.Icc (max (-(η / 2)) (t - η / 2)) (min (η / 2) (t + η / 2)) := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> constructor <;> constructor <;> linarith
    simp only [Set.indicator_apply, ← hcond]
    by_cases ha : u ∈ Set.Icc (-(η / 2)) (η / 2) <;>
      by_cases hb : t - u ∈ Set.Icc (-(η / 2)) (η / 2) <;> simp [ha, hb]
  rw [hid, integral_indicator_const (1 : ℝ) measurableSet_Icc, smul_eq_mul, mul_one,
    Real.volume_real_Icc]
  rcases le_total 0 t with ht | ht
  · rw [min_eq_left (show η / 2 ≤ t + η / 2 by linarith),
      max_eq_right (show -(η / 2) ≤ t - η / 2 by linarith), abs_of_nonneg ht, max_comm]
    congr 1
    ring
  · rw [min_eq_right (show t + η / 2 ≤ η / 2 by linarith),
      max_eq_left (show t - η / 2 ≤ -(η / 2) by linarith), abs_of_nonpos ht, max_comm]
    congr 1
    ring

end LeanLab.LZPowersOfTwo
