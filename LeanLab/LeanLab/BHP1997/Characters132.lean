/-
P0069, page 4, proof of Theorem 3 I. This is the residue-class selector
obtained by character orthogonality. Mathlib already proves the required
orthogonality theorem, so only finite sum rearrangement is needed here.
AI wrote the Lean code. CODEX task132, 2026-10-26. Goldbach is open.
-/
import LeanLab.BHP1997.Statements

namespace LeanLab.BHP1997.Characters132
open Classical Complex

/-- Page 4, the character selector used to pick out a reduced residue
class. No coprimality restriction is needed on the summation index. -/
theorem ap_sum_characters {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q)
    (I : Finset ℕ) (f : ℕ → ℂ) :
    (q.totient : ℂ) * (∑ n ∈ I.filter (fun n => n % q = a % q), f n) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
        ∑ n ∈ I, f n * χ (n : ZMod q) := by
  have hchar (n : ℕ) :
      (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) =
        if n % q = a % q then (q.totient : ℂ) else 0 := by
    simpa only [ZMod.natCast_eq_natCast_iff', eq_comm] using
      (DirichletCharacter.sum_char_inv_mul_char_eq ℂ
        ((ZMod.isUnit_iff_coprime a q).mpr ha) (n : ZMod q))
  symm
  calc
    (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
        ∑ n ∈ I, f n * χ (n : ZMod q)) =
        ∑ n ∈ I, f n * (∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = (q.totient : ℂ) * (∑ n ∈ I.filter (fun n => n % q = a % q), f n) := by
      simp_rw [hchar]
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmod : n % q = a % q <;> simp [hmod, mul_comm]


/-- Page 4, character selection detail: Phi of q times the norm of the reduced residue class sum is at most the sum of the norms of the character-twisted sums. -/
theorem ap_norm_le_character_norms {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q)
    (I : Finset ℕ) (f : ℕ → ℂ) :
    (q.totient : ℝ) * ‖∑ n ∈ I.filter (fun n => n % q = a % q), f n‖ ≤
      ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, f n * χ (n : ZMod q)‖ := by
  calc
    (q.totient : ℝ) * ‖∑ n ∈ I.filter (fun n => n % q = a % q), f n‖ =
        ‖∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) *
          ∑ n ∈ I, f n * χ (n : ZMod q)‖ := by
      simpa only [norm_mul, Complex.norm_natCast] using congrArg norm (ap_sum_characters a ha I f)
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ ((a : ZMod q)⁻¹) *
          ∑ n ∈ I, f n * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, f n * χ (n : ZMod q)‖ := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- Page 4, character selection detail: If every character-twisted sum has norm at most E, then the reduced residue class sum also has norm at most E. -/
theorem ap_norm_le_of_uniform {q : ℕ} [NeZero q] (a : ℕ) (ha : a.Coprime q)
    (I : Finset ℕ) (f : ℕ → ℂ) (E : ℝ)
    (h : ∀ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, f n * χ (n : ZMod q)‖ ≤ E) :
    ‖∑ n ∈ I.filter (fun n => n % q = a % q), f n‖ ≤ E := by
  have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hsum : (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ I, f n * χ (n : ZMod q)‖) ≤
      (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, E := Finset.sum_le_sum (fun χ _ => h χ)
      _ = (q.totient : ℝ) * E := by simp [hc]
  have hp : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hb := ap_norm_le_character_norms a ha I f
  nlinarith

end LeanLab.BHP1997.Characters132
