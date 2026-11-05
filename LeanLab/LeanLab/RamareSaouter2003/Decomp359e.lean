import LeanLab.RamareSaouter2003.Decomp290a
import LeanLab.RamareSaouter2003.Decomp359b

/-!
P0099 p. 20, the far part of display 15.
Summability of the weighted ordinate tail is separated from comparison of sums.
The per-zero estimate is already proved in Decomp1531a.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359e

open Real Smooth L3Zeta L3Zeros Decomp290c

/-- LEAF. P0099 pp. 14 and 20, Lemma 2 and the far sum in display 15.
Only the nonnegative weighted reciprocal ordinate tail is summed here.
There are no smoothed zero terms and no comparison of total sums. -/
theorem weighted_tail_summable (m : ℕ) (X T : ℝ) (hm : 1 ≤ m)
    (hX : 1 ≤ X) (hT : 1000 ≤ T) :
    Summable (fun i : ZI => if T < |gZ i| then
      X ^ bZ i / |gZ i| ^ (m + 1) else 0) := by
  have ht := Decomp359b.reciprocal_tail_summable m hm
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (ht.mul_left X)
  · change 0 ≤ if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0
    split_ifs <;> positivity
  · change (if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0) ≤
      X * (if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0)
    by_cases hi : T < |gZ i|
    · have h1000 : (1000 : ℝ) < |gZ i| := lt_of_le_of_lt hT hi
      simp only [if_pos hi, if_pos h1000]
      have hx : X ^ bZ i ≤ X := by
        calc _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (bZ_mem i).2
             _ = X := Real.rpow_one X
      convert div_le_div_of_nonneg_right hx (by positivity : 0 ≤ |gZ i| ^ (m + 1)) using 1 <;> ring
    · simp only [if_neg hi]
      split_ifs <;> positivity

/-- The exact far_sum_le target of Decomp290a.
P0099 p. 20, displays 14 and 15. CONDITIONAL ON weighted_tail_summable. -/
theorem far_sum_le (hN : L1Zeta.Lemma1N) (m : ℕ) (X u T : ℝ)
    (hm : 2 ≤ m) (hX : 10 ^ 12 ≤ X) (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (hT : 1000 ≤ T) :
    farSum m X u T ≤ (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
      (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m * ZsF gZ bZ m T X := by
  let K := (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
    (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m
  let W : ZI → ℝ := fun i => if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0
  let R : ZI → ℝ := fun i => if T < |gZ i| then (zeroTerm m X u i).re else 0
  have hW : Summable W := weighted_tail_summable m X T (by omega) (by linarith) hT
  have hδ : 0 < (m : ℝ) * u := by
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hbound (i : ZI) : ‖R i‖ ≤ K * W i := by
    by_cases hi : T < |gZ i|
    · have hγ : ((i.1 : ℂ)).im ≠ 0 := by
        change gZ i ≠ 0
        intro hh
        simp [hh] at hi
        linarith
      have hb := Decomp1531a.far_zero_term_le (bZ_mem i).1 (bZ_mem i).2 hγ hu.le hδ
        (by linarith : 0 < X) m
      change ‖if T < |gZ i| then (zeroTerm m X u i).re else 0‖ ≤
        K * (if T < |gZ i| then X ^ bZ i / |gZ i| ^ (m + 1) else 0)
      rw [if_pos hi, if_pos hi, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm (zeroTerm m X u i)).trans hb
    · simp [R, W, hi]
  have hR : Summable R := Summable.of_norm_bounded (hW.mul_left K) hbound
  have hle : (∑' i, R i) ≤ ∑' i, K * W i :=
    hR.tsum_le_tsum (fun i => (le_abs_self (R i)).trans (by simpa [Real.norm_eq_abs] using hbound i))
      (hW.mul_left K)
  simpa only [R, W, K, farSum, ZsF, tsum_mul_left] using hle

end LeanLab.RamareSaouter2003.Decomp359e

#print axioms LeanLab.RamareSaouter2003.Decomp359e.weighted_tail_summable
#print axioms LeanLab.RamareSaouter2003.Decomp359e.far_sum_le
