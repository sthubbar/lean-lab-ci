import LeanLab.ExceptionalSet.Lu2010Gauss

/-!
P0029 page 11 display 3.6, including imprimitive Dirichlet characters.
The existing complete period Parseval identity supplies the estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset ZMod
open LeanLab.ExceptionalSet.Lu2010Gauss

/-- Every Dirichlet character has Gauss sum squared norm at most its modulus.
Source: P0029 page 11 display 3.6. -/
theorem gauss_norm_sq_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖G χ 1‖ ^ 2 ≤ (q : ℝ) := by
  have hG1 : G χ 1 = gaussSum χ stdAddChar := by simp [G, gaussSum]
  have hterm (k : ZMod q) :
      ‖χ k‖ ^ 2 * ‖G χ 1‖ ^ 2 ≤ ‖G χ k‖ ^ 2 := by
    by_cases hk : IsUnit k
    · obtain ⟨u, rfl⟩ := hk
      have ht := gaussSum_mulShift_eq χ stdAddChar u
      rw [← G_eq_gaussSum, ← hG1] at ht
      rw [ht, norm_mul]
      simp
    · rw [χ.map_nonunit hk]
      simp
  have h := sum_le_sum (fun k (_hk : k ∈ (univ : Finset (ZMod q))) => hterm k)
  rw [← sum_mul, character_energy, G_energy] at h
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  nlinarith

/-- The square root modulus bound in P0029 page 11 display 3.6.
No primitive character hypothesis is needed. -/
theorem gauss_norm_le_sqrt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖G χ 1‖ ≤ Real.sqrt q := by
  have h := gauss_norm_sq_le χ
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) q)
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  nlinarith [norm_nonneg (G χ 1)]

/-- The two Gauss factors in Lu page 2379 display 63 satisfy the required product bound.
This is also a direct consequence of P0029 page 11 display 3.6. -/
theorem gauss_pair_norm_sq_le {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) :
    ‖G χ₁ 1 * G χ₂ 1‖ ^ 2 ≤ (q : ℝ) ^ 2 := by
  rw [norm_mul, mul_pow, pow_two (q : ℝ)]
  exact mul_le_mul (gauss_norm_sq_le χ₁) (gauss_norm_sq_le χ₂)
    (sq_nonneg _) (Nat.cast_nonneg _)

/-- The one modulus complete period kernel bound has no remaining Gauss norm assumption.
Source: Lu page 2379 display 63, the finite kernel factor before the zero sums.
This is not the analytic bound in display 86. -/
theorem kernel_pair_mean_le {q : ℕ} [NeZero q]
    (χ χ₁ χ₂ : DirichletCharacter ℂ q) :
    (∑ k : ZMod q, ‖kernel χ (G χ₁ 1 * G χ₂ 1) k‖ ^ 2) / q ≤
      ((q : ℝ) / q.totient) ^ 3 / q :=
  kernel_mean_le χ (gauss_pair_norm_sq_le χ₁ χ₂)

end LeanLab.ExceptionalSet.BG2026.Supply385
