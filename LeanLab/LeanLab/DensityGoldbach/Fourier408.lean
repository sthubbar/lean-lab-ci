/-
The unnormalized Fourier convention of Shao 1206.6139v2 page 13.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.AlsetriTransfer

open Finset

namespace LeanLab.DensityGoldbach.Fourier408

/-- Shao page 13, the displayed Fourier transform. This identifies the
exponential in the sealed definition with Mathlib's standard character. -/
theorem fourier_character {N : ℕ} [NeZero N] (f : ZMod N → ℝ) (r : ZMod N) :
    fourierZN N f r = ∑ n : ZMod N, (f n : ℂ) * ZMod.stdAddChar (r * n) := by
  apply sum_congr rfl
  intro n _
  congr 1
  have hrn : (((r.val * n.val : ℕ) : ℤ) : ZMod N) = r * n := by simp
  rw [← hrn, ZMod.stdAddChar_coe]
  push_cast
  rfl

/-- Shao page 13, orthogonality used in the Fourier inversion step.
Mathlib AddChar.sum_mulShift proves the full character sum. -/
theorem orthogonality {N : ℕ} [NeZero N] (x : ZMod N) :
    ∑ r : ZMod N, ZMod.stdAddChar (r * x) = if x = 0 then (N : ℂ) else 0 := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)]
  simp [ZMod.card]

/-- Shao page 13, Fourier definition at a constant function.
This supplies nonzero instances for the transfer leaves. -/
theorem constant_transform {N : ℕ} [NeZero N] (a : ℝ) (r : ZMod N) :
    fourierZN N (fun _ => a) r = if r = 0 then (N : ℂ) * (a : ℂ) else 0 := by
  rw [fourier_character, ← mul_sum]
  have he : (∑ n : ZMod N, ZMod.stdAddChar (r * n)) =
      if r = 0 then (N : ℂ) else 0 := by
    simpa only [mul_comm r] using orthogonality r
  rw [he]
  split_ifs <;> ring

/-- Shao page 13, Fourier inversion for the unnormalized positive transform. -/
theorem inversion {N : ℕ} [NeZero N] (f : ZMod N → ℝ) (x : ZMod N) :
    (f x : ℂ) = (1 / (N : ℂ)) * ∑ r : ZMod N,
      fourierZN N f r * ZMod.stdAddChar (-(r * x)) := by
  simp_rw [fourier_character, sum_mul]
  rw [sum_comm]
  have he (y r : ZMod N) :
      ((f y : ℂ) * ZMod.stdAddChar (r * y)) * ZMod.stdAddChar (-(r * x)) =
      (f y : ℂ) * ZMod.stdAddChar (r * (y - x)) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [he, ← mul_sum, orthogonality, sub_eq_zero]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]

/-- Shao page 13, convolution definition and its Fourier product identity. -/
theorem convolution_transform {N : ℕ} [NeZero N] (f g : ZMod N → ℝ) (r : ZMod N) :
    fourierZN N (fun x => ∑ y, f y * g (x - y)) r =
      fourierZN N f r * fourierZN N g r := by
  simp_rw [fourier_character]
  push_cast
  simp_rw [sum_mul]
  rw [sum_comm]
  have he (x y : ZMod N) :
      ((f y : ℂ) * (g (x - y) : ℂ)) * ZMod.stdAddChar (r * x) =
      ((f y : ℂ) * ZMod.stdAddChar (r * y)) *
        ((g (x - y) : ℂ) * ZMod.stdAddChar (r * (x - y))) := by
    have hc : ZMod.stdAddChar (r * x) =
        ZMod.stdAddChar (r * y) * ZMod.stdAddChar (r * (x - y)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hc]
    ring
  simp_rw [he, ← mul_sum]
  have hshift (y : ZMod N) :
      (∑ x : ZMod N, (g (x - y) : ℂ) * ZMod.stdAddChar (r * (x - y))) =
      ∑ x : ZMod N, (g x : ℂ) * ZMod.stdAddChar (r * x) :=
    Equiv.sum_comp (Equiv.subRight y) (fun x => (g x : ℂ) * ZMod.stdAddChar (r * x))
  simp_rw [hshift]

/-- Shao page 14, Fourier identity in the proof of Lemma 4.3. -/
theorem triple_inversion {N : ℕ} [NeZero N] (f g h : ZMod N → ℝ) (x : ZMod N) :
    ((∑ y : ZMod N, ∑ z : ZMod N, f y * g z * h (x - y - z) : ℝ) : ℂ) =
      (1 / (N : ℂ)) * ∑ r : ZMod N, fourierZN N f r * fourierZN N g r *
        fourierZN N h r * ZMod.stdAddChar (-(r * x)) := by
  have hid : (∑ y : ZMod N, ∑ z : ZMod N, f y * g z * h (x - y - z)) =
      ∑ y : ZMod N, f y * ∑ z : ZMod N, g z * h (x - y - z) := by
    simp_rw [mul_sum, mul_assoc]
  rw [hid]
  have hi := inversion (fun w => ∑ y : ZMod N, f y * ∑ z : ZMod N, g z * h (w - y - z)) x
  rw [hi]
  congr 1
  apply sum_congr rfl
  intro r _
  change fourierZN N (fun w => ∑ y, f y *
    (fun v => ∑ z, g z * h (v - z)) (w - y)) r * _ = _
  rw [convolution_transform f (fun v => ∑ z, g z * h (v - z)) r,
    convolution_transform g h r]
  ring

end LeanLab.DensityGoldbach.Fourier408

#print axioms LeanLab.DensityGoldbach.Fourier408.fourier_character
#print axioms LeanLab.DensityGoldbach.Fourier408.orthogonality
#print axioms LeanLab.DensityGoldbach.Fourier408.inversion
#print axioms LeanLab.DensityGoldbach.Fourier408.convolution_transform
#print axioms LeanLab.DensityGoldbach.Fourier408.triple_inversion

#print axioms LeanLab.DensityGoldbach.Fourier408.constant_transform
