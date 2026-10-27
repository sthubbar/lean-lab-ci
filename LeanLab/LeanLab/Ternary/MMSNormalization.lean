/-
P0028, arXiv 1610.02017, section 4.3, page 9.
The normalization step before applying Proposition 3.2.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS
open Finset

/-- Division by a positive constant commutes with the progression average. -/
theorem avg_div (f : ℕ → ℝ) (P : Finset ℕ) (s : ℝ) :
    avg (fun n => f n / s) P = avg f P / s := by
  simp only [avg, div_eq_mul_inv, ← Finset.sum_mul]
  ring

/-- A structured part bounded by 1 + ε/4 becomes unit valued after normalization. -/
theorem unitValued_normalize {N : ℕ} {ε : ℝ} {g : ℕ → ℝ}
    (hε : 0 ≤ ε)
    (hg : ∀ n ∈ Icc 1 N, 0 ≤ g n ∧ g n ≤ 1 + ε / 4) :
    UnitValued N (fun n => g n / (1 + ε / 4)) := by
  have hs : 0 < 1 + ε / 4 := by linarith
  intro n hn
  exact ⟨div_nonneg (hg n hn).1 hs.le, (div_le_one hs).mpr (hg n hn).2⟩

/-- The density loss in the renormalization used on page 9.
A margin ε/2 before division leaves a margin ε/4 afterwards. -/
theorem denseOnAPs_normalize {N : ℕ} {η ε : ℝ} {g : ℕ → ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (hg : DenseOnAPs N η (ε / 2) g) :
    DenseOnAPs N η (ε / 4) (fun n => g n / (1 + ε / 4)) := by
  intro P hP hlen
  rw [avg_div]
  have hs : 0 < 1 + ε / 4 := by linarith
  apply (le_div_iff₀ hs).mpr
  have hd := hg P hP hlen
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  nlinarith

/-- Three scalar divisions pull out of the triple convolution. -/
theorem conv3_div (N n : ℕ) (f₁ f₂ f₃ : ℕ → ℝ) (s : ℝ) :
    conv3 N (fun a => f₁ a / s) (fun a => f₂ a / s) (fun a => f₃ a / s) n =
      conv3 N f₁ f₂ f₃ n / s ^ 3 := by
  unfold conv3
  simp_rw [sum_div]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  split_ifs <;> ring

end LeanLab.Ternary.MMS
