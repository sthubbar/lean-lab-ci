/-
Split of the sealed model comparison at the principal arc, unit
Linnik1951/Decomp520a, theorem principal_model520.

The sealed bound compares the short arc principal square integral with the full
period square of the model series, and carries two error terms: one inverse of
q times the seventh root of N, and one inverse of the square root of the same
quantity. The cut gives one leaf per term. The first leaf replaces the principal
square by the model square on the short arc. The second leaf extends that short
arc to a full period, which is where the square root term is lost. The assembly
adds the two bounds with the triangle inequality and adds the constants.
-/
import LeanLab.Linnik1951.Decomp520a
import LeanLab.Linnik1951.PrincipalTail491

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- Range facts the assembly needs: on this range the seventh root of N is
positive, N is positive and the logarithm of N is nonnegative. -/
private theorem split_range520 {N : ℕ} (hN : 3 < N) :
    1 ≤ N ∧ (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) ∧ 0 < (N : ℝ) ∧ 0 ≤ Real.log N := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  exact ⟨hN1, Real.rpow_pos_of_pos hNpos _, hNpos, Real.log_nonneg (by exact_mod_cast hN1)⟩

/-- LEAF. First error term, displays 6.1 to 6.3 of the surrounding development:
on the short arc the principal square is replaced by the square of the full
period model series, and the difference is charged to the arc length, giving
the term inverse of q times the seventh root of N. -/
theorem short_arc_model_replace520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C, hC, N0, h⟩ := principal_model520 hG
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hb := h N hN0 q hq hqQ n hn
  exact hb

/-- The two spellings of the phase on the short arc give the same integral. -/
private lemma arc_phase_order520 (N q : ℕ) (n : ℤ) :
    (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  apply intervalIntegral.integral_congr
  intro z _
  simp only []
  rw [show ((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I by push_cast; ring]

/-- LEAF. Second error term, displays 6.1 to 6.3 of the surrounding development:
the short arc integral of the model square is extended to a full period, and
the loss is the square root saving, the term inverse of the square root of q
times the seventh root of N. -/
theorem short_arc_extend_period520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          logFourier520 N z ^ 2 *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C, hC, N0, h⟩ := logFourier_arc_convolution491
  refine ⟨C, hC, max N0 1, ?_⟩
  intro N hN q hq hqQ n hn
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by have := le_max_right N0 1; omega
  have hb := h N hN0 q hq hqQ n
  rw [arc_phase_order520 N q n]
  rw [logFourier_square_integral520 N hN1 n]
  have hconv : ∀ m : ℕ, logConvolution520 m = logConvolution1622 m := fun m => rfl
  rw [hconv]
  have hconst : ((Real.exp (-(n : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
    by_cases hn0 : 0 ≤ n
    · have hc : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
      rw [hc]
    · have hz : n.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [hz]
      simp [logConvolution1622]
  rw [hconst]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hRpos : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hR1 : 1 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    nlinarith
  have hsq : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hle : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by nlinarith
    have h2 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_mul_self hRpos.le] at h2
  have hnum : 0 ≤ C * (N : ℝ) * Real.log N ^ 13 := by positivity
  exact hb.trans (div_le_div_of_nonneg_left hnum (Real.sqrt_pos.mpr hRpos) hsq)


/-- The sealed statement of the unit, assembled from the two leaves by the
triangle inequality and the addition of the constants. -/
theorem principal_model520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, M1, hleaf1⟩ := short_arc_model_replace520 hG
  obtain ⟨C2, hC2, M2, hleaf2⟩ := short_arc_extend_period520 hG
  refine ⟨C1 + C2, by linarith, M1 + M2 + 3, ?_⟩
  intro N hN q hq hqQ n hn
  have hM1 : M1 < N := by omega
  have hM2 : M2 < N := by omega
  have hN3 : 3 < N := by omega
  obtain ⟨-, hT, hNpos, hlog⟩ := split_range520 hN3
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqT : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hT
  have hA0 : 0 ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hB0 : 0 ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hX0 : 0 ≤ (N : ℝ) * Real.log N ^ 13 :=
    mul_nonneg hNpos.le (pow_nonneg hlog 13)
  have h1 := hleaf1 N hM1 q hq hqQ n hn
  have h2 := hleaf2 N hM2 q hq hqQ n hn
  have htri :
      ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
        C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have heq : principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (principalIntegral520 N q n -
          (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) +
          ((∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
            (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have hA2 : C2 * (N : ℝ) * Real.log N ^ 13 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
      = C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    ring
  have e1 : C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hA0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  have e2 : C2 * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hB0
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hlog 13)
    refine mul_le_mul_of_nonneg_right ?_ hNpos.le
    linarith
  calc
    ‖principalIntegral520 N q n -
        (∫ z in (0 : ℝ)..1, logFourier520 N z ^ 2 *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖
        ≤ C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            C2 * (N : ℝ) * Real.log N ^ 13 /
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := htri
    _ = C1 * (N : ℝ) * Real.log N ^ 13 * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          C2 * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        rw [hA2]
    _ ≤ (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add e1 e2
    _ = (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        ring

end LeanLab.Linnik1951
