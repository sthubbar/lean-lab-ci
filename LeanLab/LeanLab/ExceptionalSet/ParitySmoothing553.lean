import LeanLab.ExceptionalSet.ParityAudit467
import LeanLab.ExceptionalSet.Fejer467

/-!
P0082 page370 display41, the corrected parity periodization already on main.
The literal printed formula retains the existing ParityAudit467 QUESTION.
These lemmas use correctedParityPeriodization without changing its definition.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.ParitySmoothing553
open Real Finset
open LeanLab.ExceptionalSet.KernelTransform264
open LeanLab.ExceptionalSet.ParityAudit467

/-- P0082 page370 display41, derived pointwise identity for the existing
corrected periodization. The floor parity selects the trapezoid weight. -/
theorem corrected_at_half_argument (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    correctedParityPeriodization Δ (v / 2) =
      if Even ⌊v⌋ then weight Δ (2 * Int.fract v - 1) else 0 := by
  classical
  let n : ℤ := ⌊v⌋
  let k : ℤ := n / 2
  have hlo : 2 * k ≤ n := by dsimp [k]; omega
  have hhi : n < 2 * k + 2 := by dsimp [k]; omega
  have hvl : 2 * (k : ℝ) ≤ v := by
    have hh : (n : ℝ) ≤ v := Int.floor_le v
    have hkR : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    exact hkR.trans hh
  have hvh : v < 2 * (k : ℝ) + 2 := by
    have hh : v < (n : ℝ) + 1 := Int.lt_floor_add_one v
    have hn : (n : ℝ) + 1 ≤ 2 * (k : ℝ) + 2 := by exact_mod_cast (show n + 1 ≤ 2 * k + 2 by omega)
    exact hh.trans_le hn
  unfold correctedParityPeriodization
  simp only [show (2 : ℝ) * (v / 2) = v by ring]
  rw [tsum_eq_single k]
  · by_cases he : Even ⌊v⌋
    · rw [if_pos he]
      have hn : n = 2 * k := by
        rcases he with ⟨j, hj⟩
        dsimp [n, k]
        omega
      have hnR : (n : ℝ) = 2 * (k : ℝ) := by exact_mod_cast hn
      have ha : 2 * (2 * (k : ℝ) - v) + 1 = -(2 * Int.fract v - 1) := by
        unfold Int.fract
        change 2 * (2 * (k : ℝ) - v) + 1 = -(2 * (v - (n : ℝ)) - 1)
        rw [hnR]
        ring
      rw [ha]
      simp only [weight, neg_div, abs_neg]
    · rw [if_neg he]
      have hnne : n ≠ 2 * k := by
        intro hn
        apply he
        exact ⟨k, by change n = k + k; omega⟩
      have hn : 2 * k + 1 ≤ n := by omega
      have hv : 2 * (k : ℝ) + 1 ≤ v := by
        have hh : (n : ℝ) ≤ v := Int.floor_le v
        have hkR : 2 * (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
        exact hkR.trans hh
      apply weight_zero hΔ hΔ1
      rw [le_abs]
      right
      linarith
  · intro j hj
    apply weight_zero hΔ hΔ1
    have hc : j ≤ k - 1 ∨ k + 1 ≤ j := by omega
    rw [le_abs]
    rcases hc with hj | hj
    · right
      have hjR : (j : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast hj
      linarith
    · left
      have hjR : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
      linarith

/-- P0082 page370 display41, derived global bounds for the existing
corrected parity weight at a half argument. -/
theorem corrected_half_bounds (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    0 ≤ correctedParityPeriodization Δ (v / 2) ∧
      correctedParityPeriodization Δ (v / 2) ≤ 1 := by
  rw [corrected_at_half_argument Δ v hΔ hΔ1]
  split_ifs
  · exact weight_bounds hΔ hΔ1 _
  · norm_num

/-- P0082 page370 display41, derived first smoothing error step.
Only indices within Delta over two of a fractional endpoint can contribute.
This holds on any finite block and requires no discrepancy theorem. -/
theorem finite_parity_smoothing_error (s : Finset ℕ) (v : ℕ → ℝ) (f : ℕ → ℂ)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hf : ∀ n ∈ s, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ s.filter (fun n => Even ⌊v n⌋), f n) -
      ∑ n ∈ s, (correctedParityPeriodization Δ (v n / 2) : ℂ) * f n‖ ≤
        ((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
          1 - Δ / 2 < Int.fract (v n))).card : ℝ) := by
  classical
  let bad := fun n => Int.fract (v n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (v n)
  have hpoint (n : ℕ) (hn : n ∈ s) :
      ‖(if Even ⌊v n⌋ then f n else 0) -
          (correctedParityPeriodization Δ (v n / 2) : ℂ) * f n‖ ≤
        if bad n then (1 : ℝ) else 0 := by
    rw [corrected_at_half_argument Δ (v n) hΔ hΔ1]
    by_cases he : Even ⌊v n⌋
    · simp only [he, ite_true]
      let w := weight Δ (2 * Int.fract (v n) - 1)
      change ‖f n - (w : ℂ) * f n‖ ≤ if bad n then 1 else 0
      have hw : 0 ≤ w ∧ w ≤ 1 := weight_bounds hΔ hΔ1 _
      by_cases hb : bad n
      · rw [if_pos hb]
        rw [show f n - (w : ℂ) * f n = ((1 - w : ℝ) : ℂ) * f n by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ 1 - w by linarith [hw.2])]
        calc
          _ ≤ (1 - w) * 1 := mul_le_mul_of_nonneg_left (hf n hn) (by linarith [hw.2])
          _ ≤ 1 := by linarith [hw.1]
      · rw [if_neg hb]
        have hl : Δ / 2 ≤ Int.fract (v n) :=
          le_of_not_gt (fun h => hb (Or.inl h))
        have hr : Int.fract (v n) ≤ 1 - Δ / 2 :=
          le_of_not_gt (fun h => hb (Or.inr h))
        have hp : |2 * Int.fract (v n) - 1| ≤ 1 - Δ :=
          abs_le.mpr ⟨by linarith, by linarith⟩
        have hw1 : w = 1 := weight_one hΔ hΔ1 hp
        rw [hw1]
        simp
    · simp only [he, ite_false, Complex.ofReal_zero, zero_mul, sub_self, norm_zero]
      split_ifs <;> norm_num
  calc
    _ = ‖∑ n ∈ s, ((if Even ⌊v n⌋ then f n else 0) -
        (correctedParityPeriodization Δ (v n / 2) : ℂ) * f n)‖ := by
      rw [Finset.sum_filter, Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ s, ‖(if Even ⌊v n⌋ then f n else 0) -
        (correctedParityPeriodization Δ (v n / 2) : ℂ) * f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, if bad n then (1 : ℝ) else 0 := Finset.sum_le_sum hpoint
    _ = _ := by simp [← Finset.sum_filter, bad]

/-- P0082 page369 cognate odd case and page370 display41.
An integer shift selects either parity and leaves the boundary count unchanged. -/
theorem finite_shifted_parity_smoothing_error (s : Finset ℕ) (v : ℕ → ℝ)
    (f : ℕ → ℂ) (j : ℤ) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hf : ∀ n ∈ s, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), f n) -
      ∑ n ∈ s, (correctedParityPeriodization Δ ((v n + j) / 2) : ℂ) * f n‖ ≤
        ((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
          1 - Δ / 2 < Int.fract (v n))).card : ℝ) := by
  simpa only [Int.floor_add_intCast, Int.fract_add_intCast] using
    finite_parity_smoothing_error s (fun n => v n + j) f Δ hΔ hΔ1 hf

end LeanLab.ExceptionalSet.ParitySmoothing553
