/-
P0087 Akeno 2026 page 6, the Type II correlation expansion.
These finite identities precede all analytic estimates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Cauchy86

namespace LeanLab.Akeno2026.Correlation86
open Finset
/-- LEAF. Page 6 second display, exact expansion before taking real parts. -/
theorem correlation_identity {ι κ : Type*} (s : Finset ι) (t : Finset κ) (B : κ → ℂ) (Z : ι → κ → ℂ) :
    (∑ m ∈ s, (∑ n ∈ t, B n * Z m n) * star (∑ n ∈ t, B n * Z m n)) =
      ∑ n₁ ∈ t, ∑ n₂ ∈ t, B n₁ * star (B n₂) *
        ∑ m ∈ s, Z m n₁ * star (Z m n₂) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n₁ hn₁
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n₂ hn₂
  apply sum_congr rfl
  intro m hm
  ring

/-- LEAF. Page 6 second display, the correlation bound after removing bounded coefficients. -/
theorem correlation_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ) (B : κ → ℂ) (Z : ι → κ → ℂ)
    (hB : ∀ n ∈ t, ‖B n‖ ≤ 1) :
    (∑ m ∈ s, ‖∑ n ∈ t, B n * Z m n‖ ^ 2) ≤
      ∑ n₁ ∈ t, ∑ n₂ ∈ t, ‖∑ m ∈ s, Z m n₁ * star (Z m n₂)‖ := by
  have heq := correlation_identity s t B Z
  have hre : (∑ m ∈ s, ‖∑ n ∈ t, B n * Z m n‖ ^ 2) =
      (∑ n₁ ∈ t, ∑ n₂ ∈ t, B n₁ * star (B n₂) *
        ∑ m ∈ s, Z m n₁ * star (Z m n₂)).re := by
    rw [← heq, Complex.re_sum]
    apply sum_congr rfl
    intro m hm
    change ‖∑ n ∈ t, B n * Z m n‖ ^ 2 =
      ((∑ n ∈ t, B n * Z m n) * (starRingEnd ℂ) (∑ n ∈ t, B n * Z m n)).re
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  calc
    _ = _ := hre
    _ ≤ ‖∑ n₁ ∈ t, ∑ n₂ ∈ t, B n₁ * star (B n₂) *
        ∑ m ∈ s, Z m n₁ * star (Z m n₂)‖ := Complex.re_le_norm _
    _ ≤ ∑ n₁ ∈ t, ∑ n₂ ∈ t, ‖B n₁ * star (B n₂) *
        ∑ m ∈ s, Z m n₁ * star (Z m n₂)‖ := by
      apply (norm_sum_le t _).trans
      exact sum_le_sum (fun _ _ => norm_sum_le t _)
    _ ≤ _ := by
      apply sum_le_sum
      intro n₁ hn₁
      apply sum_le_sum
      intro n₂ hn₂
      rw [norm_mul, norm_mul, norm_star]
      have hc : ‖B n₁‖ * ‖B n₂‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (hB n₁ hn₁) (hB n₂ hn₂) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      exact mul_le_of_le_one_left (norm_nonneg _) hc

/-- LEAF. Page 6 the two finite Type II inequalities assembled without analytic inputs. -/
theorem bilinear_bound {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : ι → ℂ) (B : κ → ℂ) (Z : ι → κ → ℂ)
    (hA : ∀ m ∈ s, ‖A m‖ ≤ 1) (hB : ∀ n ∈ t, ‖B n‖ ≤ 1) :
    ‖∑ m ∈ s, ∑ n ∈ t, A m * B n * Z m n‖ ^ 2 ≤
      (s.card : ℝ) * ∑ n₁ ∈ t, ∑ n₂ ∈ t, ‖∑ m ∈ s, Z m n₁ * star (Z m n₂)‖ := by
  have hc := Cauchy86.finite_cauchy s A (fun m => ∑ n ∈ t, B n * Z m n) hA
  have hr := correlation_bound s t B Z hB
  have hh := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ s.card by positivity)
  apply (le_trans ?_ hh)
  simpa only [Finset.mul_sum, mul_assoc] using hc

end LeanLab.Akeno2026.Correlation86
