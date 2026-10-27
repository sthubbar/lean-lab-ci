/-
AI wrote this Lean code for CODEX task51.
P0074 pages 9 and 10, Cauchy's inequality for the Gauss-weighted character error.
The local analytic character second moments remain inputs.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.GaussExpansion

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The Gauss-weighted error attached to a finite set of characters. -/
noncomputable def gaussError {q : ℕ} [NeZero q] (A : Finset (DirichletCharacter ℂ q))
    (r : ZMod q) (D : DirichletCharacter ℂ q → ℂ) : ℂ :=
  (1 / (q.totient : ℂ)) * ∑ χ ∈ A, gaussSum χ⁻¹ ZMod.stdAddChar * χ r * D χ

/-- Cauchy's inequality retains the size of an arbitrary exceptional character set. -/
theorem gaussError_sq_le {q : ℕ} [NeZero q] (A : Finset (DirichletCharacter ℂ q))
    (r : ZMod q) (D : DirichletCharacter ℂ q → ℂ) :
    ‖gaussError A r D‖ ^ 2 ≤
      (q : ℝ) * A.card / (q.totient : ℝ) ^ 2 * ∑ χ ∈ A, ‖D χ‖ ^ 2 := by
  let c : DirichletCharacter ℂ q → ℂ := fun χ => gaussSum χ⁻¹ ZMod.stdAddChar * χ r
  have hc : ∀ χ, ‖c χ‖ ^ 2 ≤ (q : ℝ) := by
    intro χ
    have hg := gauss_norm_le_sqrt χ⁻¹
    have hn := χ.norm_le_one r
    have hb : ‖c χ‖ ≤ Real.sqrt q := by
      dsimp only [c]
      rw [norm_mul]
      calc
        _ ≤ Real.sqrt q * 1 := mul_le_mul hg hn (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = _ := mul_one _
    have hs := pow_le_pow_left₀ (norm_nonneg (c χ)) hb 2
    simpa only [Real.sq_sqrt (Nat.cast_nonneg q)] using hs
  have hnorm : ‖∑ χ ∈ A, c χ * D χ‖ ≤ ∑ χ ∈ A, ‖c χ‖ * ‖D χ‖ := by
    simpa only [norm_mul] using norm_sum_le A (fun χ => c χ * D χ)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun χ => ‖c χ‖) (fun χ => ‖D χ‖)
  have hsumc : ∑ χ ∈ A, ‖c χ‖ ^ 2 ≤ (q : ℝ) * A.card := by
    calc
      _ ≤ ∑ _χ ∈ A, (q : ℝ) := Finset.sum_le_sum (fun χ hχ => hc χ)
      _ = _ := by simp [mul_comm]
  have hsums : 0 ≤ ∑ χ ∈ A, ‖D χ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : ‖∑ χ ∈ A, c χ * D χ‖ ^ 2 ≤
      (q : ℝ) * A.card * ∑ χ ∈ A, ‖D χ‖ ^ 2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (hcs.trans (mul_le_mul_of_nonneg_right hsumc hsums))
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  unfold gaussError
  change ‖(1 / (q.totient : ℂ)) * ∑ χ ∈ A, c χ * D χ‖ ^ 2 ≤ _
  rw [norm_mul, mul_pow, norm_div, norm_one, Complex.norm_natCast, div_pow, one_pow]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2) * ((q : ℝ) * A.card * ∑ χ ∈ A, ‖D χ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- Summing over all characters replaces the character count by the totient. -/
theorem gaussError_univ_sq_le {q : ℕ} [NeZero q]
    (r : ZMod q) (D : DirichletCharacter ℂ q → ℂ) :
    ‖gaussError Finset.univ r D‖ ^ 2 ≤
      (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q, ‖D χ‖ ^ 2 := by
  have h := gaussError_sq_le Finset.univ r D
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [hcard] at h
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  convert h using 1 <;> field_simp

/-- A partition of characters partitions the error exactly. -/
theorem gaussError_split {q : ℕ} [NeZero q] (A : Finset (DirichletCharacter ℂ q))
    (r : ZMod q) (D : DirichletCharacter ℂ q → ℂ) :
    gaussError Finset.univ r D = gaussError A r D + gaussError (Finset.univ \ A) r D := by
  unfold gaussError
  rw [← mul_add]
  congr 1
  exact (Finset.sum_add_sum_compl A _).symm

/-- Squaring the two error pieces costs at most twice their individual squared norms. -/
theorem gaussError_split_sq_le {q : ℕ} [NeZero q] (A : Finset (DirichletCharacter ℂ q))
    (r : ZMod q) (D : DirichletCharacter ℂ q → ℂ) :
    ‖gaussError Finset.univ r D‖ ^ 2 ≤
      2 * ‖gaussError A r D‖ ^ 2 + 2 * ‖gaussError (Finset.univ \ A) r D‖ ^ 2 := by
  rw [gaussError_split A]
  have ht := norm_add_le (gaussError A r D) (gaussError (Finset.univ \ A) r D)
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖gaussError A r D‖ - ‖gaussError (Finset.univ \ A) r D‖)]

#print axioms gaussError_sq_le
#print axioms gaussError_univ_sq_le
#print axioms gaussError_split
#print axioms gaussError_split_sq_le
end LeanLab.Grimmelt2019.MainTerm
