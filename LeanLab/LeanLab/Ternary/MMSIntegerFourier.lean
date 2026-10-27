/-
P0028, arXiv 1610.02017, section 4.3, pages 9 and 10.
Fourier transforms of finitely supported functions on the integers.
This interface retains the mass outside the original interval after smoothing.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSRestriction

namespace LeanLab.Ternary.MMS
open Finset

/-- The Fourier transform on all integers, with the same sign as fhat. -/
noncomputable def intHat (f : ℤ →₀ ℝ) (γ : ℝ) : ℂ :=
  Finsupp.linearCombination ℝ (fun n : ℤ => e (-(n : ℝ) * γ)) f

/-- A translation sends the mass at n to n + t. -/
noncomputable def intShift (t : ℤ) (f : ℤ →₀ ℝ) : ℤ →₀ ℝ :=
  Finsupp.mapDomain (fun n => n + t) f

/-- Embed an interval function by extending it by zero on the integers. -/
noncomputable def intervalLift (N : ℕ) (f : ℕ → ℝ) : ℤ →₀ ℝ :=
  ∑ n ∈ Icc 1 N, Finsupp.single (n : ℤ) (f n)

/-- The additive character takes sums to products. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fourier transformation preserves addition. -/
theorem intHat_add (f g : ℤ →₀ ℝ) (γ : ℝ) :
    intHat (f + g) γ = intHat f γ + intHat g γ := by
  simp [intHat]

/-- Fourier transformation preserves real scalar multiplication. -/
theorem intHat_smul (a : ℝ) (f : ℤ →₀ ℝ) (γ : ℝ) :
    intHat (a • f) γ = (a : ℂ) * intHat f γ := by
  simp [intHat, Algebra.smul_def]

/-- Fourier transformation preserves finite sums. -/
theorem intHat_sum {ι : Type*} (S : Finset ι) (f : ι → ℤ →₀ ℝ) (γ : ℝ) :
    intHat (∑ i ∈ S, f i) γ = ∑ i ∈ S, intHat (f i) γ := by
  simp [intHat]

/-- Transform of a point mass. -/
theorem intHat_single (n : ℤ) (a γ : ℝ) :
    intHat (Finsupp.single n a) γ = (a : ℂ) * e (-(n : ℝ) * γ) := by
  simp [intHat, Algebra.smul_def]

/-- A translation multiplies the transform by its phase. -/
theorem intHat_shift (t : ℤ) (f : ℤ →₀ ℝ) (γ : ℝ) :
    intHat (intShift t f) γ = intHat f γ * e (-(t : ℝ) * γ) := by
  unfold intHat intShift
  simp only [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index
    (h := fun (n : ℤ) (a : ℝ) => a • e (-(n : ℝ) * γ))
    (fun _ => by simp) (fun _ a b => by simp [add_smul])]
  unfold Finsupp.sum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have he : -((n + t : ℤ) : ℝ) * γ = -(n : ℝ) * γ + -(t : ℝ) * γ := by
    push_cast
    ring
  dsimp only
  rw [he, e_add]
  simp only [Algebra.smul_def]
  ring

/-- The integer transform agrees with the existing transform before smoothing. -/
theorem intHat_intervalLift (N : ℕ) (f : ℕ → ℝ) (γ : ℝ) :
    intHat (intervalLift N f) γ = fhat N f γ := by
  unfold intervalLift
  rw [intHat_sum]
  unfold fhat
  apply Finset.sum_congr rfl
  intro n hn
  rw [intHat_single]
  simp only [Int.cast_natCast]
  unfold e
  congr 2
  push_cast
  ring

end LeanLab.Ternary.MMS
