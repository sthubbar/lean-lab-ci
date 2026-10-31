/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
Full integer convolution keeps all the mass created by smoothing.
Nonnegative structured parts dominate their interval restrictions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSIntervalConvolution
namespace LeanLab.Ternary.MMS
open Finset
noncomputable def fullConv3 (f g h : ℤ →₀ ℝ) (m : ℤ) : ℝ :=
  ∑ a ∈ f.support, ∑ b ∈ g.support, f a * g b * h (m - a - b)

theorem fullConv3_nonneg (f g h : ℤ →₀ ℝ) (m : ℤ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n) :
    0 ≤ fullConv3 f g h m := by
  exact sum_nonneg fun a ha => sum_nonneg fun b hb =>
    mul_nonneg (mul_nonneg (hf a) (hg b)) (hh _)

theorem fullConv3_mono_left (f f' g h : ℤ →₀ ℝ) (m : ℤ)
    (hf : ∀ n, f n ≤ f' n) (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n) :
    fullConv3 f g h m ≤ fullConv3 f' g h m := by
  unfold fullConv3
  change f.sum (fun a r => ∑ b ∈ g.support, r * g b * h (m - a - b)) ≤
    f'.sum (fun a r => ∑ b ∈ g.support, r * g b * h (m - a - b))
  apply Finsupp.sum_le_sum_index hf
  · intro a ha r s hrs
    apply sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrs (hg b)) (hh _)
  · intro a ha
    simp

theorem fullConv3_mono_middle (f g g' h : ℤ →₀ ℝ) (m : ℤ)
    (hg : ∀ n, g n ≤ g' n) (hf : ∀ n, 0 ≤ f n) (hh : ∀ n, 0 ≤ h n) :
    fullConv3 f g h m ≤ fullConv3 f g' h m := by
  unfold fullConv3
  apply sum_le_sum
  intro a ha
  change g.sum (fun b r => f a * r * h (m - a - b)) ≤
    g'.sum (fun b r => f a * r * h (m - a - b))
  apply Finsupp.sum_le_sum_index hg
  · intro b hb r s hrs
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrs (hf a)) (hh _)
  · intro b hb
    simp

theorem fullConv3_mono_right (f g h h' : ℤ →₀ ℝ) (m : ℤ)
    (hh : ∀ n, h n ≤ h' n) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    fullConv3 f g h m ≤ fullConv3 f g h' m := by
  exact sum_le_sum fun a ha => sum_le_sum fun b hb =>
    mul_le_mul_of_nonneg_left (hh _) (mul_nonneg (hf a) (hg b))

theorem fullConv3_add_left (f f' g h : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 (f + f') g h m = fullConv3 f g h m + fullConv3 f' g h m := by
  unfold fullConv3
  change (f + f').sum (fun a r => ∑ b ∈ g.support, r * g b * h (m - a - b)) = _
  rw [Finsupp.sum_add_index]
  · rfl
  · intro a ha
    simp
  · intro a ha r s
    simp [add_mul, sum_add_distrib]

theorem fullConv3_add_middle (f g g' h : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 f (g + g') h m = fullConv3 f g h m + fullConv3 f g' h m := by
  unfold fullConv3
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  change (g + g').sum (fun b r => f a * r * h (m - a - b)) = _
  rw [Finsupp.sum_add_index]
  · rfl
  · intro b hb
    simp
  · intro b hb r s
    simp [mul_add, add_mul]

theorem fullConv3_add_right (f g h h' : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 f g (h + h') m = fullConv3 f g h m + fullConv3 f g h' m := by
  simp [fullConv3, Finsupp.add_apply, mul_add, sum_add_distrib]

theorem fullConv3_telescoping (g₁ g₂ g₃ h₁ h₂ h₃ : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 (g₁ + h₁) (g₂ + h₂) (g₃ + h₃) m =
      fullConv3 g₁ g₂ g₃ m + fullConv3 h₁ (g₂ + h₂) (g₃ + h₃) m +
        fullConv3 g₁ h₂ (g₃ + h₃) m + fullConv3 g₁ g₂ h₃ m := by
  rw [fullConv3_add_left, fullConv3_add_middle g₁,
    fullConv3_add_right g₁ g₂]
  ring
theorem fullConv3_intervalLift (N n : ℕ) (f g h : ℕ → ℝ) :
    fullConv3 (intervalLift N f) (intervalLift N g) (intervalLift N h) n = conv3 N f g h n :=
  int_triple_intervalLift N n f g h

theorem intervalLift_restrict_le (N : ℕ) (f : ℤ →₀ ℝ) (hf : ∀ n, 0 ≤ f n) (n : ℤ) :
    intervalLift N (fun k => f k) n ≤ f n := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with k
    rw [intervalLift_apply_nat]
    split_ifs
    · exact le_rfl
    · exact hf _
  · rw [intervalLift_apply_neg N _ n (lt_of_not_ge hn)]
    exact hf _

theorem conv3_le_fullConv3 (N n : ℕ) (f g h : ℤ →₀ ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n) :
    conv3 N (fun k => f k) (fun k => g k) (fun k => h k) n ≤ fullConv3 f g h n := by
  have hfl := intervalLift_nonneg N (fun k => f k) (fun k _ => hf k)
  have hgl := intervalLift_nonneg N (fun k => g k) (fun k _ => hg k)
  have hhl := intervalLift_nonneg N (fun k => h k) (fun k _ => hh k)
  rw [← fullConv3_intervalLift]
  calc _ ≤ fullConv3 f (intervalLift N (fun k => g k)) (intervalLift N (fun k => h k)) n :=
      fullConv3_mono_left _ _ _ _ _ (intervalLift_restrict_le N f hf) hgl hhl
    _ ≤ fullConv3 f g (intervalLift N (fun k => h k)) n :=
      fullConv3_mono_middle _ _ _ _ _ (intervalLift_restrict_le N g hg) hf hhl
    _ ≤ fullConv3 f g h n := fullConv3_mono_right _ _ _ _ _ (intervalLift_restrict_le N h hh) hf hg

theorem fullConv3_fourier (f g h : ℤ →₀ ℝ) (m : ℤ) :
    (∫ γ in (0 : ℝ)..1, intHat f γ * intHat g γ * intHat h γ * e ((m : ℝ) * γ)) =
      (fullConv3 f g h m : ℂ) := intHat_triple_integral f g h m

theorem fullConv3_swap_left (f g h : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 f g h m = fullConv3 g f h m := by
  apply Complex.ofReal_injective
  rw [← fullConv3_fourier, ← fullConv3_fourier]
  congr 1
  funext γ
  ring

theorem fullConv3_swap_right (f g h : ℤ →₀ ℝ) (m : ℤ) :
    fullConv3 f g h m = fullConv3 f h g m := by
  apply Complex.ofReal_injective
  rw [← fullConv3_fourier, ← fullConv3_fourier]
  congr 1
  funext γ
  ring

theorem fullConv3_ge_of_three_errors (g₁ g₂ g₃ h₁ h₂ h₃ : ℤ →₀ ℝ) (m : ℤ) (E : ℝ)
    (he₁ : |fullConv3 h₁ (g₂ + h₂) (g₃ + h₃) m| ≤ E)
    (he₂ : |fullConv3 g₁ h₂ (g₃ + h₃) m| ≤ E)
    (he₃ : |fullConv3 g₁ g₂ h₃ m| ≤ E) :
    fullConv3 g₁ g₂ g₃ m - 3 * E ≤ fullConv3 (g₁ + h₁) (g₂ + h₂) (g₃ + h₃) m := by
  rw [fullConv3_telescoping]
  have h₁ := (abs_le.mp he₁).1
  have h₂ := (abs_le.mp he₂).1
  have h₃ := (abs_le.mp he₃).1
  linarith

theorem conv3_ge_of_integer_decomposition (N n : ℕ) (f₁ f₂ f₃ : ℕ → ℝ)
    (g₁ g₂ g₃ h₁ h₂ h₃ : ℤ →₀ ℝ) (E : ℝ)
    (hd₁ : intervalLift N f₁ = g₁ + h₁)
    (hd₂ : intervalLift N f₂ = g₂ + h₂)
    (hd₃ : intervalLift N f₃ = g₃ + h₃)
    (hg₁ : ∀ n, 0 ≤ g₁ n) (hg₂ : ∀ n, 0 ≤ g₂ n) (hg₃ : ∀ n, 0 ≤ g₃ n)
    (he₁ : |fullConv3 h₁ (g₂ + h₂) (g₃ + h₃) n| ≤ E)
    (he₂ : |fullConv3 g₁ h₂ (g₃ + h₃) n| ≤ E)
    (he₃ : |fullConv3 g₁ g₂ h₃ n| ≤ E) :
    conv3 N (fun k => g₁ k) (fun k => g₂ k) (fun k => g₃ k) n - 3 * E ≤
      conv3 N f₁ f₂ f₃ n := by
  have hmain := conv3_le_fullConv3 N n g₁ g₂ g₃ hg₁ hg₂ hg₃
  have herr := fullConv3_ge_of_three_errors g₁ g₂ g₃ h₁ h₂ h₃ n E he₁ he₂ he₃
  rw [← hd₁, ← hd₂, ← hd₃, fullConv3_intervalLift] at herr
  linarith

end LeanLab.Ternary.MMS
