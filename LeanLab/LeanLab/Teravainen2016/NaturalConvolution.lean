/-
P0076, Section 2, pages 6 to 7. Natural representatives and periodic smooth convolution.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.BohrFourier

open Finset
open scoped Classical ZMod

namespace LeanLab.Teravainen2016

/-- The natural subtraction used by conv represents subtraction on Z_N. -/
theorem cyclic_sub_val {N : ℕ} [NeZero N] (n k : ℕ) (hk : k < N) :
    ((n : ZMod N) - (k : ZMod N)).val = (n + N - k) % N := by
  have hle : k ≤ n + N := by omega
  have he : ((n + N - k : ℕ) : ZMod N) = (n : ZMod N) - k := by
    rw [Nat.cast_sub hle]
    simp
  rw [← he, ZMod.val_natCast]

/-- The existing conv agrees with complex cyclic convolution. -/
theorem conv_eq_cyclicConv (N : ℕ) [NeZero N] (f g : ℕ → ℝ) (n : ℕ) :
    (conv N f g n : ℂ) = cyclicConv (fun k : ZMod N => (f k.val : ℂ))
      (fun k : ZMod N => (g k.val : ℂ)) n := by
  unfold conv cyclicConv
  push_cast
  congr 1
  have he : ∀ k : ZMod N,
      (f k.val : ℂ) * g (((n : ZMod N) - k).val) =
      (f k.val : ℂ) * g ((n + N - k.val) % N) := by
    intro k
    rw [← ZMod.natCast_zmod_val k, cyclic_sub_val n k.val (ZMod.val_lt k)]
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt k)]
  rw [sum_congr rfl (fun k _ => he k),
    sum_zmod_val (fun k => (f k : ℂ) * g ((n + N - k) % N))]

/-- The exact convolution theorem for the fhat used by Prop21With. -/
theorem fhat_conv (N : ℕ) [NeZero N] (f g : ℕ → ℝ) (ξ : ℕ) :
    fhat N (conv N f g) ξ = fhat N f ξ * fhat N g ξ := by
  rw [fhat_eq_normalizedDFT, fhat_eq_normalizedDFT, fhat_eq_normalizedDFT]
  have he : (fun n : ZMod N => (conv N f g n.val : ℂ)) =
      cyclicConv (fun k : ZMod N => (f k.val : ℂ)) (fun k : ZMod N => (g k.val : ℂ)) := by
    funext n
    rw [conv_eq_cyclicConv, ZMod.natCast_zmod_val]
  rw [he, normalizedDFT_conv]

/-- Parseval and Fourier multiplication for the exact natural definitions. -/
theorem conv_energy (N : ℕ) [NeZero N] (f g : ℕ → ℝ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, conv N f g n ^ 2 =
      ∑ ξ ∈ range N, ‖fhat N f ξ * fhat N g ξ‖ ^ 2 := by
  rw [fhat_parseval]
  simp_rw [fhat_conv]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

/-- An integer periodic function takes the same value on every representative. -/
theorem periodic_emod {N : ℕ} {χ : ℤ → ℝ} (hper : ∀ n, χ (n + N) = χ n) (n : ℤ) :
    χ (n % N) = χ n := by
  have hp : Function.Periodic χ (N : ℤ) := hper
  rw [Int.emod_def]
  simpa [mul_comm] using hp.sub_int_mul_eq (x := n) (n / N)

/-- The periodic cutoff convolution is convChi. -/
theorem conv_cutoff_eq (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ) (χ : ℤ → ℝ)
    (hper : ∀ n, χ (n + N) = χ n) (n : ℕ) :
    conv N f (fun k => χ k) n = convChi N f χ n := by
  unfold conv convChi
  congr 1
  apply sum_congr rfl
  intro k hk
  congr 1
  have hkN := mem_range.mp hk
  have he : (((n + N - k) % N : ℕ) : ℤ) = ((n : ℤ) - k) % N := by
    rw [Int.natCast_mod, Nat.cast_sub (by omega : k ≤ n + N)]
    push_cast
    rw [show (n : ℤ) + N - k = (n : ℤ) - k + N by ring]
    simp
  dsimp only
  rw [he, periodic_emod hper]

/-- Nonnegativity of normalized convolution. -/
theorem conv_nonneg (N : ℕ) (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ conv N f g n := by
  unfold conv
  apply mul_nonneg (by positivity)
  exact sum_nonneg (fun k _ => mul_nonneg (hf k) (hg _))

/-- Subtraction in the second convolution factor. -/
theorem conv_sub_right (N : ℕ) (f g h : ℕ → ℝ) (n : ℕ) :
    conv N f (fun k => g k - h k) n = conv N f g n - conv N f h n := by
  unfold conv
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  ring

/-- Fourier transforms commute with real scalar multiplication. -/
theorem fhat_real_smul (N : ℕ) (f : ℕ → ℝ) (c : ℝ) (ξ : ℕ) :
    fhat N (fun n => c * f n) ξ = (c : ℂ) * fhat N f ξ := by
  unfold fhat
  push_cast
  simp_rw [mul_assoc, ← mul_sum]
  ring

/-- Fourier transforms commute with real subtraction. -/
theorem fhat_sub (N : ℕ) (f g : ℕ → ℝ) (ξ : ℕ) :
    fhat N (fun n => f n - g n) ξ = fhat N f ξ - fhat N g ξ := by
  unfold fhat
  simp_rw [Complex.ofReal_sub, sub_mul]
  rw [sum_sub_distrib]
  ring

example : conv 1 (fun _ => 1) (fun _ => 1) 1 = 1 := by simp [conv]

#print axioms cyclic_sub_val
#print axioms conv_eq_cyclicConv
#print axioms fhat_conv
#print axioms conv_energy
#print axioms periodic_emod
#print axioms conv_cutoff_eq
#print axioms conv_nonneg
#print axioms conv_sub_right
#print axioms fhat_real_smul
#print axioms fhat_sub

end LeanLab.Teravainen2016
