/-
P0028, arXiv 1610.02017, section 4.3, page 9.
A telescoping alternative to the eight term expansion.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS
open Finset

/-- Additivity in the first input. -/
theorem conv3_add_left (N n : ℕ) (f g u v : ℕ → ℝ) :
    conv3 N (fun a => f a + g a) u v n = conv3 N f u v n + conv3 N g u v n := by
  unfold conv3
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  split_ifs <;> ring

/-- Additivity in the second input. -/
theorem conv3_add_middle (N n : ℕ) (f g u v : ℕ → ℝ) :
    conv3 N u (fun a => f a + g a) v n = conv3 N u f v n + conv3 N u g v n := by
  unfold conv3
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  split_ifs <;> ring

/-- Additivity in the third input. -/
theorem conv3_add_right (N n : ℕ) (f g u v : ℕ → ℝ) :
    conv3 N u v (fun a => f a + g a) n = conv3 N u v f n + conv3 N u v g n := by
  unfold conv3
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  split_ifs <;> ring

/-- Three error terms suffice when the other inputs retain the original f values. -/
theorem conv3_telescoping (N n : ℕ) (g₁ g₂ g₃ h₁ h₂ h₃ : ℕ → ℝ) :
    conv3 N (fun a => g₁ a + h₁ a) (fun a => g₂ a + h₂ a)
      (fun a => g₃ a + h₃ a) n =
    conv3 N g₁ g₂ g₃ n +
    conv3 N h₁ (fun a => g₂ a + h₂ a) (fun a => g₃ a + h₃ a) n +
    conv3 N g₁ h₂ (fun a => g₃ a + h₃ a) n + conv3 N g₁ g₂ h₃ n := by
  rw [conv3_add_left, conv3_add_middle N n g₂ h₂ g₁,
    conv3_add_right N n g₃ h₃ g₁ g₂]
  ring

/-- Absolute bounds on the three mixed terms give a one-sided error of 3E. -/
theorem conv3_ge_of_three_errors (N n : ℕ) (g₁ g₂ g₃ h₁ h₂ h₃ : ℕ → ℝ) (E : ℝ)
    (he₁ : |conv3 N h₁ (fun a => g₂ a + h₂ a) (fun a => g₃ a + h₃ a) n| ≤ E)
    (he₂ : |conv3 N g₁ h₂ (fun a => g₃ a + h₃ a) n| ≤ E)
    (he₃ : |conv3 N g₁ g₂ h₃ n| ≤ E) :
    conv3 N g₁ g₂ g₃ n - 3 * E ≤
      conv3 N (fun a => g₁ a + h₁ a) (fun a => g₂ a + h₂ a)
        (fun a => g₃ a + h₃ a) n := by
  rw [conv3_telescoping]
  have h₁ := (abs_le.mp he₁).1
  have h₂ := (abs_le.mp he₂).1
  have h₃ := (abs_le.mp he₃).1
  linarith

end LeanLab.Ternary.MMS
