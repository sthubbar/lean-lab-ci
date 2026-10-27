import LeanLab.HardyLittlewood1923.CharacterExpansion
import LeanLab.HardyLittlewood1923.WeightedContour

/-!
AI wrote this Lean code for CODEX task52.
P0004 page 8, the unit restricted exponential series and its character expansion.
-/

open ZMod Finset

namespace LeanLab.HardyLittlewood1923.Task52

lemma character_inverse_at_unit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ZMod q} (hn : IsUnit n) :
    χ⁻¹ n = χ n⁻¹ := by
  obtain ⟨u, rfl⟩ := hn
  rw [MulChar.inv_apply, Ring.inverse_unit]
  simp

noncomputable def unitWeightedSum {q : ℕ} (e : AddChar (ZMod q) ℂ) (z : ℂ) : ℂ := by
  classical
  exact ∑' n : ℕ, if IsUnit (n : ZMod q) then
    (e (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
      Complex.exp (-(n : ℂ) * z) else 0

lemma weighted_character_expansion {q : ℕ} [NeZero q]
    (e : AddChar (ZMod q) ℂ) {z : ℂ} (hz : 0 < z.re) :
    unitWeightedSum e z = ∑ χ : DirichletCharacter ℂ q,
      (gaussSum χ e / (q.totient : ℂ)) * weightedSum χ⁻¹ z := by
  classical
  have hs (χ : DirichletCharacter ℂ q) : Summable (fun n : ℕ =>
      (gaussSum χ e / (q.totient : ℂ)) *
        ((χ⁻¹ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          Complex.exp (-(n : ℂ) * z))) :=
    (summable_weightedSum χ⁻¹ hz).mul_left _
  unfold weightedSum unitWeightedSum
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ (_ : χ ∈ (univ : Finset (DirichletCharacter ℂ q))) => hs χ)]
  apply tsum_congr
  intro n
  by_cases hn : IsUnit (n : ZMod q)
  · rw [if_pos hn]
    have he := additive_character_expansion_div e hn
    rw [he]
    simp_rw [character_inverse_at_unit _ hn]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [MulChar.map_nonunit _ hn]
    simp

#print axioms character_inverse_at_unit
#print axioms weighted_character_expansion

end LeanLab.HardyLittlewood1923.Task52
