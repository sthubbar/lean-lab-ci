/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 175 to 177, Lemma 4. Reuse the proved scalar cutoff and tail bounds.
-/
import LeanLab.PlattTrudgian2014.Decomp380a
import LeanLab.PlattTrudgian2014.Decomp421b

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- P0026 page 176 display 4.16, obtained from the middle term and the scalar bound. -/
theorem even_moment_sqrt_proved421 (t : ℝ) (ht : 0 ≤ t) (L j : ℕ) :
    (∫ x : ℝ in 0..1, (t * ‖G L x‖) ^ (2 * j)) ≤
      2 * Real.sqrt ((j : ℝ) + 1) *
        (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) := by
  have hc : (0 : ℝ) < Nat.centralBinom j := by exact_mod_cast Nat.centralBinom_pos j
  have hp : 0 ≤ ∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    exact pow_nonneg (sq_nonneg (t * (G L x).re)) j |>.trans_eq (by rw [pow_mul])
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ (4 : ℝ) ^ j * (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) :=
      even_middle_moment_decomposed421 t ht L j
    _ ≤ (2 * Real.sqrt ((j : ℝ) + 1) * (Nat.centralBinom j : ℝ)) *
        (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) :=
      mul_le_mul_of_nonneg_right (central_binomial_sqrt380 j) hp
    _ = _ := by ring

/-- P0026 pages 175 to 177 display 4.13, exactly the existing norm comparison.
All four inputs are discharged by proved bridges or existing clean proofs. -/
theorem norm_real_moment_comparison_proved421 (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        C * (1 + Real.sqrt (t * L)) *
          (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) := by
  obtain ⟨B, hB, htail⟩ := factorial_tail_bounded380
  refine ⟨8 + B, by positivity, fun L => ?_⟩
  let A : ℝ := t * L
  let K : ℕ := 2 * ⌊A⌋₊ + 1
  let E : ℝ := ∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)
  have hA : 0 ≤ A := mul_nonneg ht (Nat.cast_nonneg L)
  have hK : A ≤ (K : ℝ) := by
    have hf := Nat.lt_floor_add_one A
    dsimp [K]
    push_cast
    have hn : (0 : ℝ) ≤ ⌊A⌋₊ := Nat.cast_nonneg _
    linarith
  have hE : 1 ≤ E := real_exp_moment_one_le380 t L
  have hsum : (∑ j ∈ range K,
      (∫ x : ℝ in 0..1, (t * ‖G L x‖) ^ (2 * j)) / (2 * j).factorial) ≤
        2 * Real.sqrt (K : ℝ) * E := by
    calc
      _ ≤ ∑ j ∈ range K, (2 * Real.sqrt (K : ℝ)) *
          ((∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) / (2 * j).factorial) := by
        apply sum_le_sum
        intro j hj
        have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast mem_range.mp hj
        have hp : 0 ≤ ∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j) := by
          apply intervalIntegral.integral_nonneg (by norm_num)
          intro x _
          exact pow_nonneg (sq_nonneg (t * (G L x).re)) j |>.trans_eq (by rw [pow_mul])
        have hm := (even_moment_sqrt_proved421 t ht L j).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hjK) (by norm_num)) hp)
        simpa [mul_div_assoc] using div_le_div_of_nonneg_right hm
          (Nat.cast_nonneg (2 * j).factorial)
      _ = (2 * Real.sqrt (K : ℝ)) * (∑ j ∈ range K,
          (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) / (2 * j).factorial) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_even_real_sum_decomposed421 t ht L K) (by positivity)
  have hc := norm_exp_cutoff380 t ht L K hK
  have hb := htail A hA
  have hs : Real.sqrt (K : ℝ) ≤ 2 * (1 + Real.sqrt A) := cutoff_sqrt380 A hA
  have hR : 1 ≤ 1 + Real.sqrt A := by linarith [Real.sqrt_nonneg A]
  have hRE : 1 ≤ (1 + Real.sqrt A) * E := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hs (show 0 ≤ E by linarith)
  have hBm := mul_le_mul_of_nonneg_left hRE hB
  change (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤ (8 + B) * (1 + Real.sqrt A) * E
  change 4 * A ^ (2 * K) / (2 * K).factorial ≤ B at hb
  nlinarith

set_option format.width 240
#print axioms even_moment_sqrt_proved421
#print axioms norm_real_moment_comparison_proved421

end LeanLab.PlattTrudgian2014
