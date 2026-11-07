/-
Numerical Rankin decomposition of the weighted smooth reciprocal tail.
Source https://arxiv.org/abs/0801.0130 page 14 below display 50.
The finite moment and the real parameter absorption are separate leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp447c
import LeanLab.KumchevLiu2007.Rankin447

namespace LeanLab.KumchevLiu2007.Task447b

open Real Task129b Task292c Task438d
open scoped BigOperators

/-- LEAF. Page 14 below display 50, derived weighted Euler product input.
The primary proof cites Lemma 3.5 on page 12 and Tenenbaum Section III.5.
The weight has one factor 64 per distinct prime, so the unweighted smooth
count cannot be applied without a further argument. This leaf isolates
that argument as a fractional reciprocal moment. There is no tail cutoff,
x, y, epsilon or prescribed decay exponent. -/
theorem smooth_fractional_moment :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (Q : ℝ) (M : ℕ), 0 < Q →
      (∑ q ∈ Finset.Icc 1 M,
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  exact Task447c.smooth_fractional_moment

/-- LEAF. Page 14 last estimate below display 50, derived parameter step.
Only real powers and logarithms remain. This leaf contains no arithmetic
function, smooth indicator, prime, modulus sum or A3 coefficient. -/
theorem rankin_parameter_absorption (D B ε : ℝ) (hD : 0 ≤ D)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) ≤
          C / Real.log x ^ B := by
  exact Rankin447.rankin_parameter_absorption D B ε hD hB hε

/-- Page 14 below display 50, derived finite Rankin inequality.
A nonnegative reciprocal tail is at most its fractional moment divided
by the cutoff to the fractional exponent. -/
theorem weighted_rankin_tail (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 ≤ δ) (M : ℕ) :
    (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
  have hpow : 0 < T ^ δ := Real.rpow_pos_of_pos hT δ
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ M, (w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqT : T < (q : ℝ) := (Nat.floor_lt hT.le).mp (Finset.mem_Ioc.mp hq).1
      have hq0 : (0 : ℝ) < q := hT.trans hqT
      have hp : T ^ δ ≤ (q : ℝ) ^ δ := Real.rpow_le_rpow hT.le hqT.le hδ
      have he : (q : ℝ) ^ (1 - δ) * (q : ℝ) ^ δ = q := by
        rw [← Real.rpow_add hq0]
        simp
      calc
        _ = (w q / (q : ℝ) ^ (1 - δ)) / (q : ℝ) ^ δ := by
          rw [div_div, he]
        _ ≤ _ := div_le_div_of_nonneg_left (div_nonneg (hw q) (Real.rpow_nonneg hq0.le _)) hpow hp
    _ = (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hpow.le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hq).1; omega,
          (Finset.mem_Ioc.mp hq).2⟩
      · intro q hq hn
        exact div_nonneg (hw q) (Real.rpow_nonneg (by positivity) _)

/-- Page 14 below display 50. Exact Task438j.smooth_reciprocal_tail target.
It follows from the fractional smooth moment, finite Rankin inequality
and real parameter absorption. Both smaller inputs have clean proofs. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  obtain ⟨C, D, hC, hD, hm⟩ := smooth_fractional_moment
  obtain ⟨K, x0, hK, hx0, hk⟩ := rankin_parameter_absorption D (A / 2) ε hD (by linarith) hε
  refine ⟨C * K, x0, mul_pos hC hK, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
  have hT : 0 < y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hδ : 0 ≤ 1 / (2 * max 1 (Real.log Q)) := by positivity
  have hw (q : ℕ) : 0 ≤ smoothWeight q Q * coefficientMajorant q := by
    have hsw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
    exact mul_nonneg hsw (by unfold coefficientMajorant; positivity)
  calc
    _ = ∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q * coefficientMajorant q) / (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      weighted_rankin_tail _ hw _ _ hT hδ _
    _ ≤ (C * (max 1 (Real.log Q)) ^ D) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      div_le_div_of_nonneg_right (hm Q _ hQpos) (by positivity)
    _ = C * ((max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q)))) := by ring
    _ ≤ C * (K / Real.log x ^ (A / 2)) :=
      mul_le_mul_of_nonneg_left (hk x y Q hx hy hyx hQpos hQ) hC.le
    _ = _ := by ring

#print axioms smooth_fractional_moment
#print axioms rankin_parameter_absorption
#print axioms weighted_rankin_tail
#print axioms smooth_reciprocal_tail

end LeanLab.KumchevLiu2007.Task447b
