import LeanLab.RieselVaughan1983.Stieltjes1Enclosure

/-!
The error comparison in equation 3.7 on page 50.
AI wrote the Lean code. Binary Goldbach is OPEN.
Application to the paper's g still requires its weighted absolute convergence.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Real

lemma error_scale (y : ℝ) (hy : 0 < y) (m : ℕ) (hm : 0 < m) :
    (y / m) ^ (-(1 / 3 : ℝ)) = y ^ (-(1 / 3 : ℝ)) * (m : ℝ) ^ (1 / 3 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.div_rpow hy.le hm0.le, div_eq_mul_inv,
    ← Real.rpow_neg hm0.le, neg_neg]

lemma error_term_bound (f : ℕ → ℝ) (hf0 : f 0 = 0) (y : ℝ) (hy : 0 < y) (m : ℕ) :
    |f m * lem1E stieltjes1 (y / m)| ≤
      (1641 / 1000 * y ^ (-(1 / 3 : ℝ))) * (|f m| * (m : ℝ) ^ (1 / 3 : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hf0]
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h := StieltjesCert.lemma1_stieltjes1_unconditional (y / m) (by positivity)
    rw [error_scale y hy m hm] at h
    rw [abs_mul]
    calc |f m| * |lem1E stieltjes1 (y / m)| ≤
          |f m| * (1641 / 1000 * (y ^ (-(1 / 3 : ℝ)) * (m : ℝ) ^ (1 / 3 : ℝ))) := by
            gcongr
      _ = _ := by ring

/-- The strict error estimate once the absolute majorant is summable. -/
theorem weighted_error_bound (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 ≠ 0)
    (hs : Summable (fun m : ℕ => |f m| * (m : ℝ) ^ (1 / 3 : ℝ)))
    (y : ℝ) (hy : 0 < y) :
    |∑' m : ℕ, f m * lem1E stieltjes1 (y / m)| <
      1641 / 1000 * y ^ (-(1 / 3 : ℝ)) *
        ∑' m : ℕ, |f m| * (m : ℝ) ^ (1 / 3 : ℝ) := by
  let c : ℝ := 1641 / 1000 * y ^ (-(1 / 3 : ℝ))
  have hmajor := hs.mul_left c
  have hle := error_term_bound f hf0 y hy
  have habs : Summable (fun m : ℕ => |f m * lem1E stieltjes1 (y / m)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hmajor
  have hstrict : |f 1 * lem1E stieltjes1 (y / (1 : ℕ))| <
      c * (|f 1| * ((1 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) := by
    have h := StieltjesCert.lemma1_stieltjes1_unconditional y hy
    have hf : 0 < |f 1| := abs_pos.mpr hf1
    simpa [c, abs_mul, mul_comm] using mul_lt_mul_of_pos_left h hf
  calc |∑' m : ℕ, f m * lem1E stieltjes1 (y / m)| ≤
        ∑' m : ℕ, |f m * lem1E stieltjes1 (y / m)| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
            (f := fun m : ℕ => f m * lem1E stieltjes1 (y / m))
            (by simpa only [Real.norm_eq_abs] using habs)
    _ < ∑' m : ℕ, c * (|f m| * (m : ℝ) ^ (1 / 3 : ℝ)) :=
      Summable.tsum_lt_tsum hle hstrict habs hmajor
    _ = _ := by rw [tsum_mul_left]

end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.error_scale
#print axioms LeanLab.RieselVaughan1983.Lemma2.error_term_bound
#print axioms LeanLab.RieselVaughan1983.Lemma2.weighted_error_bound
