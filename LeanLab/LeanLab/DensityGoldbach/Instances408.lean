/-
Concrete nonzero domains for the task408 supply leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Fourier408
import LeanLab.DensityGoldbach.Counting408

open Finset

namespace LeanLab.DensityGoldbach.Instances408

/-- Shao page 13, the Fourier transform of the uniform probability weight.
Every prime N supports the pseudorandomness hypothesis with zero error. -/
theorem uniform_fourier {N : ℕ} [NeZero N] (r : ZMod N) :
    fourierZN N (fun _ => (1 : ℝ) / N) r = if r = 0 then 1 else 0 := by
  rw [Fourier408.constant_transform]
  split_ifs
  · push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]
  · rfl

/-- Shao page 13, display 25 at the uniform weight.
The Fourier q norm equals 1 for every q positive. -/
theorem uniform_norm {N : ℕ} [NeZero N] (q : ℝ) (hq : 0 < q) :
    (∑ r : ZMod N, ‖fourierZN N (fun _ => (1 : ℝ) / N) r‖ ^ q) ^ (1 / q) = 1 := by
  simp_rw [uniform_fourier]
  have hq0 : q ≠ 0 := hq.ne'
  simp_rw [apply_ite (fun z : ℂ => ‖z‖ ^ q)]
  simp [hq0]

/-- Shao page 13, display 23 at the uniform triple, delta = 1/8.
Every individual mass is 1 and the sum of masses minus 1 is 2. -/
theorem uniform_masses {N : ℕ} [NeZero N] :
    (∀ i : Fin 3, (1 : ℝ) / 8 ≤ ∑ _x : ZMod N, (1 : ℝ) / N) ∧
    (1 : ℝ) / 8 ≤ (∑ _x : ZMod N, (1 : ℝ) / N) +
      (∑ _x : ZMod N, (1 : ℝ) / N) + (∑ _x : ZMod N, (1 : ℝ) / N) - 1 := by
  have hm : (∑ _x : ZMod N, (1 : ℝ) / N) = 1 := by
    simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast NeZero.ne N]
  simp only [hm]
  norm_num

/-- Shao page 15, nonempty superlevel sets for dense counting.
The uniform triple has a strictly positive convolution at every point. -/
theorem uniform_convolution {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ _y : ZMod N, ∑ _z : ZMod N, ((1 : ℝ) / N) * (1 / N) * (1 / N)) = 1 / N := by
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

end LeanLab.DensityGoldbach.Instances408

#print axioms LeanLab.DensityGoldbach.Instances408.uniform_fourier
#print axioms LeanLab.DensityGoldbach.Instances408.uniform_norm
#print axioms LeanLab.DensityGoldbach.Instances408.uniform_masses
#print axioms LeanLab.DensityGoldbach.Instances408.uniform_convolution
