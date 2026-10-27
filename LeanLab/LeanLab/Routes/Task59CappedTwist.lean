/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The elementary capped variant requested by the U1465 next action.
The sufficient cap condition is stated without division.
-/
import LeanLab.Routes.U1465TwistLP

namespace LeanLab.Routes.Task59

open Finset

/-- The twisted candidate still bounds an LP with an upper cap of 1. -/
theorem lp_le_twisted_capped {α ι κ : Type*} [DecidableEq α]
    (S P : Finset α) (J : Finset ι) (R : ι → Finset κ)
    (B : ι → κ → α → ℝ) (σ : ι → ℝ) (lam a : α → ℝ) (β s : ℝ)
    (hβ : ∀ z : α → ℝ, (∀ n ∈ S, 0 ≤ z n ∧ z n ≤ 1) →
      (∀ j ∈ J, ∑ m ∈ R j, |∑ n ∈ S, B j m n * (z n - a n)| ≤ σ j) →
      β ≤ ∑ n ∈ S ∩ P, z n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : ∀ n ∈ S, 0 ≤ a n)
    (hcap : ∀ n ∈ S, (1 + s) * a n ≤ 1)
    (hlam : ∀ n ∈ S, lam n = 1 ∨ lam n = -1)
    (hP : ∀ n ∈ S ∩ P, lam n = -1)
    (hfeas : ∀ j ∈ J, s * ∑ m ∈ R j, |∑ n ∈ S, B j m n * (lam n * a n)| ≤ σ j) :
    β ≤ (1 - s) * ∑ n ∈ S ∩ P, a n := by
  have hbox : ∀ n ∈ S, 0 ≤ (1 + s * lam n) * a n ∧
      (1 + s * lam n) * a n ≤ 1 := by
    intro n hn
    have ha0 := ha n hn
    have hc := hcap n hn
    rcases hlam n hn with h | h
    · simp only [h, mul_one]
      exact ⟨mul_nonneg (by linarith) ha0, hc⟩
    · simp only [h, mul_neg_one]
      refine ⟨mul_nonneg (by linarith) ha0, ?_⟩
      exact (mul_le_mul_of_nonneg_right (by linarith : 1 + -s ≤ 1 + s) ha0).trans hc
  have hdata : ∀ j ∈ J,
      ∑ m ∈ R j, |∑ n ∈ S, B j m n * ((1 + s * lam n) * a n - a n)| ≤ σ j := by
    intro j hj
    calc (∑ m ∈ R j, |∑ n ∈ S, B j m n * ((1 + s * lam n) * a n - a n)|)
        = s * ∑ m ∈ R j, |∑ n ∈ S, B j m n * (lam n * a n)| := by
          rw [mul_sum]
          apply sum_congr rfl
          intro m _
          rw [← abs_of_nonneg hs0, ← abs_mul, abs_of_nonneg hs0, mul_sum]
          congr 1
          exact sum_congr rfl (fun n _ => by ring)
      _ ≤ σ j := hfeas j hj
  calc β ≤ ∑ n ∈ S ∩ P, (1 + s * lam n) * a n := hβ _ hbox hdata
    _ = ∑ n ∈ S ∩ P, (1 - s) * a n :=
      sum_congr rfl (fun n hn => by rw [hP n hn]; ring)
    _ = (1 - s) * ∑ n ∈ S ∩ P, a n := by rw [mul_sum]

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.lp_le_twisted_capped
