/-
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- The Euler factor of the generalized singular series at a prime `p`. -/
noncomputable def eulerFactorGen {r₁ r₂ : ℕ} (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (p : ℕ) : ℂ :=
  ∑' k : ℕ, if h : p ^ k = 0 then 0 else @Aq r₁ r₂ χ₁ χ₂ N (p ^ k) ⟨h⟩

/-- The Euler factor of the ordinary singular series at a prime `p`. -/
noncomputable def eulerFactorSing (N : ℕ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, (((ArithmeticFunction.moebius (p ^ k) : ℤ) : ℝ) ^ 2 / (Nat.totient (p ^ k) : ℝ) ^ 2) * (ramanujan (p ^ k) N).re

/-- LEAF page 23. The ordinary singular series converges to the product of its Euler factors. -/
theorem euler_sing_eq (N : ℕ) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p) atTop (𝓝 (singular N)) := by
  sorry

/-- LEAF page 23. The generalized singular series converges to the product of its Euler factors. -/
theorem euler_gen_eq {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen χ₁ χ₂ N p) atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  sorry

/-- LEAF page 23. For any prime `p`, the norm of the generalized Euler factor is at most the ordinary Euler factor. -/
theorem local_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℕ) (p : ℕ) :
    ‖eulerFactorGen χ₁ χ₂ N p‖ ≤ eulerFactorSing N p := by
  sorry

/-- LEAF page 23. If local factors satisfy the bound and the global series converge, then the limit norms satisfy the bound. -/
theorem prod_bound {F : ℕ → ℂ} {f : ℕ → ℝ} {L : ℂ} {l : ℝ}
    (hF : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, F p) atTop (𝓝 L))
    (hf : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, f p) atTop (𝓝 l))
    (h_bound : ∀ p, ‖F p‖ ≤ f p) : ‖L‖ ≤ l := by
  have H : ∀ X : ℕ, ‖∏ p ∈ (Finset.range X).filter Nat.Prime, F p‖ ≤ ∏ p ∈ (Finset.range X).filter Nat.Prime, f p := by
    intro X
    induction' Finset.filter Nat.Prime (Finset.range X) using Finset.induction with a s ha ih
    · simp
    · rw [Finset.prod_insert ha, Finset.prod_insert ha]
      calc
        ‖F a * ∏ p ∈ s, F p‖ = ‖F a‖ * ‖∏ p ∈ s, F p‖ := by rw [norm_mul]
        _ ≤ f a * ∏ p ∈ s, f p := by
          apply mul_le_mul (h_bound a) ih (norm_nonneg _)
          exact le_trans (norm_nonneg _) (h_bound a)
  exact le_of_tendsto_of_tendsto' hF.norm hf H

/-- The assembly theorem for `bound65` (Pintz's Main Lemma on page 23). -/
theorem bound65_decomposed : Bound65 := by
  intro r₁ r₂ _ _ χ₁ χ₂ _ _ N _
  apply prod_bound (euler_gen_eq χ₁ χ₂ N) (euler_sing_eq N) (local_bound χ₁ χ₂ N)

end LeanLab.BhowmikGrimmelt2026
