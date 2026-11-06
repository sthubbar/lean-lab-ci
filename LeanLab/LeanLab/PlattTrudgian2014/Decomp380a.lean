/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 175 to 177, the written proof of Lemma 4 specialized to t G.
The four open leaves contain no norm exponential comparison conclusion.
-/
import LeanLab.PlattTrudgian2014.Decomp281a
import LeanLab.PlattTrudgian2014.Scalars380
import LeanLab.PlattTrudgian2014.Taylor380
import LeanLab.PlattTrudgian2014.RealMoments380

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- LEAF. P0026 page 176, the middle binomial term immediately before display 4.16.
All integrated mixed powers have nonnegative coefficients. Retain the middle term.
This compares a single even moment, not an exponential moment. -/
theorem even_middle_moment380 (t : ℝ) (ht : 0 ≤ t) (L j : ℕ) :
    (Nat.centralBinom j : ℝ) * (∫ x : ℝ in 0..1, (t * ‖G L x‖) ^ (2 * j)) ≤
      (4 : ℝ) ^ j * (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) := by
  sorry

/-- LEAF. P0026 page 176, the finite sum estimate below display 4.17.
Every power of the real trigonometric sum has nonnegative integral.
Its finite even Taylor sum is bounded by the full real exponential moment. -/
theorem finite_even_real_sum380 (t : ℝ) (ht : 0 ≤ t) (L K : ℕ) :
    (∑ j ∈ range K,
      (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) / (2 * j).factorial) ≤
        ∫ x : ℝ in 0..1, Real.exp (t * (G L x).re) := by
  sorry

/-- LEAF. P0026 page 176 display 4.15 and page 177, geometric tail below 4.17.
Truncate the even exponential series and bound the remaining norm powers by tL.
Only the finite norm moments and the scalar factorial tail remain. -/
theorem norm_exp_cutoff380 (t : ℝ) (ht : 0 ≤ t) (L K : ℕ)
    (hK : t * L ≤ K) :
    (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
      2 * (∑ j ∈ range K,
        (∫ x : ℝ in 0..1, (t * ‖G L x‖) ^ (2 * j)) / (2 * j).factorial) +
          4 * (t * L) ^ (2 * K) / (2 * K).factorial := by
  have hf : Continuous (fun x : ℝ => Real.exp (t * ‖G L x‖)) := by fun_prop
  have hg : Continuous (fun x : ℝ =>
      2 * (∑ j ∈ range K, (t * ‖G L x‖) ^ (2 * j) / (2 * j).factorial) +
        4 * (t * L) ^ (2 * K) / (2 * K).factorial) := by fun_prop
  have hm := intervalIntegral.integral_mono (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
    (fun x => norm_even_taylor_cutoff380 (t * ‖G L x‖) (t * L)
      (mul_nonneg ht (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_G_le L x) ht) K hK)
  have hs : IntervalIntegrable (fun x : ℝ =>
      2 * ∑ j ∈ range K, (t * ‖G L x‖) ^ (2 * j) / (2 * j).factorial) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ =>
      2 * ∑ j ∈ range K, (t * ‖G L x‖) ^ (2 * j) / (2 * j).factorial)).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun _ : ℝ =>
      4 * (t * L) ^ (2 * K) / (2 * K).factorial) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hs hb, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum] at hm
  · simpa only [intervalIntegral.integral_div, intervalIntegral.integral_const,
      sub_zero, one_smul] using hm
  · intro j _
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (t * ‖G L x‖) ^ (2 * j) / (2 * j).factorial)).intervalIntegrable _ _

/-- LEAF. P0026 page 177, last sentence of the Lemma 4 proof.
At cutoff K = twice floor A plus one the scalar factorial remainder is uniformly bounded.
This statement has no trigonometric sum or integral. -/
theorem factorial_tail_bounded380 :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 ≤ A →
      4 * A ^ (2 * (2 * ⌊A⌋₊ + 1)) / (2 * (2 * ⌊A⌋₊ + 1)).factorial ≤ B := by
  refine ⟨4, by norm_num, fun A hA => ?_⟩
  let K : ℕ := 2 * ⌊A⌋₊ + 1
  have hKpos : 0 < K := by dsimp [K]; omega
  have hfp : (0 : ℝ) < (2 * K).factorial := by positivity
  change 4 * A ^ (2 * K) / (2 * K).factorial ≤ 4
  rw [div_le_iff₀ hfp]
  suffices hh : A ^ (2 * K) ≤ ((2 * K).factorial : ℝ) by linarith
  by_cases hf : ⌊A⌋₊ = 0
  · have hA1 : A ≤ 1 := by
      have hx := Nat.lt_floor_add_one A
      rw [hf] at hx
      norm_num at hx
      exact hx.le
    have hK : K = 1 := by simp [K, hf]
    rw [hK]
    norm_num
    nlinarith [mul_self_le_mul_self hA hA1]
  · have hK3 : 3 ≤ K := by dsimp [K]; omega
    have hAupper : A ≤ (2 * K : ℕ) / Real.exp 1 := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      have hfloor := Nat.lt_floor_add_one A
      have hcast : (3 : ℝ) ≤ K := by exact_mod_cast hK3
      have hKA : 3 * A ≤ 2 * (K : ℝ) := by
        dsimp [K] at *
        push_cast at *
        linarith
      have hmul := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hA
      push_cast
      linarith
    have hroot : 1 ≤ Real.sqrt (2 * Real.pi * (2 * K : ℕ)) := by
      apply Real.le_sqrt_of_sq_le
      have hn : (1 : ℝ) ≤ (2 * K : ℕ) := by exact_mod_cast (show 1 ≤ 2 * K by omega)
      nlinarith [Real.pi_gt_three]
    calc
      _ ≤ ((2 * K : ℕ) / Real.exp 1 : ℝ) ^ (2 * K) := pow_le_pow_left₀ hA hAupper _
      _ ≤ Real.sqrt (2 * Real.pi * (2 * K : ℕ)) *
          ((2 * K : ℕ) / Real.exp 1 : ℝ) ^ (2 * K) := by
        exact le_mul_of_one_le_left (by positivity) hroot
      _ ≤ _ := Stirling.le_factorial_stirling (2 * K)

/-- P0026 page 176 display 4.16, obtained from the middle term and the scalar bound. -/
theorem even_moment_sqrt380 (t : ℝ) (ht : 0 ≤ t) (L j : ℕ) :
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
      even_middle_moment380 t ht L j
    _ ≤ (2 * Real.sqrt ((j : ℝ) + 1) * (Nat.centralBinom j : ℝ)) *
        (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) :=
      mul_le_mul_of_nonneg_right (central_binomial_sqrt380 j) hp
    _ = _ := by ring

/-- P0026 pages 175 to 177 display 4.13, exactly the existing norm comparison.
CONDITIONAL ON the four smaller leaves in this file. -/
theorem norm_real_moment_comparison_decomposed380 (t : ℝ) (ht : 0 ≤ t) :
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
        have hm := (even_moment_sqrt380 t ht L j).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hjK) (by norm_num)) hp)
        simpa [mul_div_assoc] using div_le_div_of_nonneg_right hm
          (Nat.cast_nonneg (2 * j).factorial)
      _ = (2 * Real.sqrt (K : ℝ)) * (∑ j ∈ range K,
          (∫ x : ℝ in 0..1, (t * (G L x).re) ^ (2 * j)) / (2 * j).factorial) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (finite_even_real_sum380 t ht L K) (by positivity)
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
#print axioms even_middle_moment380
#print axioms finite_even_real_sum380
#print axioms norm_exp_cutoff380
#print axioms factorial_tail_bounded380
#print axioms even_moment_sqrt380
#print axioms norm_real_moment_comparison_decomposed380

end LeanLab.PlattTrudgian2014
