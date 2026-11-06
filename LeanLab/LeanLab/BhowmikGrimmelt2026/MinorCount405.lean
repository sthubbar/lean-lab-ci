/-
The minor arc counting step on P0029 page 17.
The source itself cites Montgomery and Vaughan 1975, page 367, section 8.
The major arc input stays OPEN. Prove the minor moment counting step.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

/-- Nine logarithms are absorbed into half the positive power saving.
Derived bookkeeping for P0029 page 17 and Montgomery Vaughan page 367 display 8.2. -/
theorem log_nine_power405 {x ϑ : ℝ} (hx : 1 ≤ x) (hϑ : 0 < ϑ) :
    Real.log x ^ 9 ≤ (18 / ϑ) ^ 9 * x ^ (ϑ / 2) := by
  have hxp : 0 < x := by linarith
  have ha : 0 < ϑ / 18 := by positivity
  have hl := Real.log_le_rpow_div hxp.le ha
  have hl' : Real.log x ≤ (18 / ϑ) * x ^ (ϑ / 18) := by
    convert hl using 1 <;> field_simp <;> ring
  have hp := pow_le_pow_left₀ (Real.log_nonneg hx) hl' 9
  have he : (x ^ (ϑ / 18)) ^ 9 = x ^ (ϑ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
    congr 1
    ring
  simpa only [mul_pow, he] using hp

/-- The proved minor second moment at the actual real outer scale has a power saving.
Flooring the prime sum length preserves the original cutoff R equal to X to theta. -/
theorem minor_moment_power405 (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 4 ≤ X →
      ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ^ 2 ≤
        C * X ^ (3 - ϑ / 2) := by
  let D : ℝ := 12 * (48600 : ℝ) ^ 2
  refine ⟨2 * D * (18 / ϑ) ^ 9, by dsimp [D]; positivity, ?_⟩
  intro X hX
  have hx : 1 ≤ X := by linarith
  have hxp : 0 < X := by linarith
  have hK : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hxp.le
  have hK2 : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by linarith : (2 : ℝ) ≤ X)
  have hR1 : 1 ≤ X ^ ϑ := Real.one_le_rpow hx hϑ.le
  have hRp : 0 < X ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hsqrt2 : 2 ≤ Real.sqrt X := by
    have hh := Real.sqrt_le_sqrt hX
    norm_num at hh
    exact hh
  have hsqrt : Real.sqrt X ≤ X - 1 := by nlinarith [Real.sq_sqrt hxp.le]
  have hRX : X ^ ϑ ≤ (⌊X⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one X
    calc
      _ ≤ Real.sqrt X := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ ≤ X - 1 := hsqrt
      _ ≤ _ := by linarith
  have hm := minor_second_moment84 hK2 hR1 hRX
  have hmono : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ^ 2 ≤
      D * (X ^ 2 / X ^ ϑ + X ^ (8 / 5 : ℝ)) * X * Real.log X ^ 9 := by
    apply hm.trans
    dsimp [D]
    have hlogK : 0 ≤ Real.log (⌊X⌋₊ : ℝ) := Real.log_natCast_nonneg _
    gcongr
  have he1 : X ^ 2 / X ^ ϑ * X * X ^ (ϑ / 2) = X ^ (3 - ϑ / 2) := by
    rw [show 3 - ϑ / 2 = (2 - ϑ) + 1 + ϑ / 2 by ring,
      Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_sub hxp,
      Real.rpow_two, Real.rpow_one]
  have he2 : X ^ (8 / 5 : ℝ) * X * X ^ (ϑ / 2) = X ^ (13 / 5 + ϑ / 2) := by
    rw [show (13 / 5 + ϑ / 2 : ℝ) = (8 / 5 + 1) + ϑ / 2 by ring,
      Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_one]
  have hp : X ^ (13 / 5 + ϑ / 2) ≤ X ^ (3 - ϑ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    _ ≤ D * (X ^ 2 / X ^ ϑ + X ^ (8 / 5 : ℝ)) * X * Real.log X ^ 9 := hmono
    _ ≤ D * (X ^ 2 / X ^ ϑ + X ^ (8 / 5 : ℝ)) * X *
        ((18 / ϑ) ^ 9 * X ^ (ϑ / 2)) :=
      mul_le_mul_of_nonneg_left (log_nine_power405 hx hϑ) (by dsimp [D]; positivity)
    _ = D * (18 / ϑ) ^ 9 * (X ^ (3 - ϑ / 2) + X ^ (13 / 5 + ϑ / 2)) := by
      rw [← he1, ← he2]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hp (by dsimp [D]; positivity : 0 ≤ D * (18 / ϑ) ^ 9)
      nlinarith only [hh]

/-- Chebyshev gives the real scale exceptional count after the logarithms are absorbed.
This uses the proved logarithm power nine and does not claim the printed power five. -/
theorem minor_large_count405 (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 5)
    (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 4 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => c * X ≤ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖)).card : ℝ) ≤
        C * X ^ (1 - ϑ / 2) := by
  classical
  obtain ⟨C, hC, hm⟩ := minor_moment_power405 ϑ hϑ hϑ'
  refine ⟨C / c ^ 2, by positivity, fun X hX => ?_⟩
  have hxp : 0 < X := by linarith
  have hcard := card_le_of_sum_sq (f := fun N => ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖)
    (show 0 < c * X by positivity) (hm X hX)
  simp only [abs_norm] at hcard
  apply hcard.trans_eq
  have hp : X ^ (3 - ϑ / 2) = X ^ (1 - ϑ / 2) * X ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hxp]
    congr 1
    ring
  rw [hp]
  field_simp
  <;> ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.log_nine_power405
#print axioms LeanLab.BhowmikGrimmelt2026.minor_moment_power405
#print axioms LeanLab.BhowmikGrimmelt2026.minor_large_count405
