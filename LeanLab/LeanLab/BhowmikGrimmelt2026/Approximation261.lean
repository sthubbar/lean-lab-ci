/-
A proved optimized approximation with logarithm power ten.
Source: P0029 page 27 display 7.9.
The cutoff retains its actual N dependent scale in every coefficient.
The printed power five remains open.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.MinorFamily261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- Above the smallest permitted scale, logarithm power ten absorbs logarithm power one. -/
theorem log_one_to_ten261 {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X : ℝ) ≤ 512 * Real.log X ^ 10 := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 9
  have hh := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ Real.log (X : ℝ))
  norm_num at hh
  nlinarith only [hh]

/-- The minor arc size budget has the two powers in display 7.9. -/
theorem optimized_minor_powers261 {x : ℝ} (hx : 0 < x) (ϑ : ℝ) :
    (x ^ 2 / x ^ ϑ + x ^ (8 / 5 : ℝ)) * x = x ^ (3 - ϑ) + x ^ (13 / 5 : ℝ) := by
  have hfirst : x ^ 2 / x ^ ϑ * x = x ^ (3 - ϑ) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_sub hx]
    calc
      _ = x ^ ((2 : ℝ) - ϑ) * x ^ (1 : ℝ) := by simp only [Real.rpow_one, Nat.cast_ofNat]
      _ = x ^ (2 - ϑ + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  have hsecond : x ^ (8 / 5 : ℝ) * x = x ^ (13 / 5 : ℝ) := by
    calc
      _ = x ^ (8 / 5 : ℝ) * x ^ (1 : ℝ) := by simp only [Real.rpow_one, Nat.cast_ofNat]
      _ = x ^ ((8 / 5 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [add_mul, hfirst, hsecond]

/-- Display 7.9 with the actual varying smoothing, proved with logarithm power ten. -/
theorem optimized_approximation_log10_261 {ϕ G : ℝ → ℝ}
    (hϕ : IsPhi ϕ) (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
          Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
              ee (-(N * α))‖ ^ 2 ≤
          C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 10 := by
  obtain ⟨C₁, hC₁, hmajor⟩ := major_family_optimized261 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, hminor⟩ := minor_family_optimized_log10_261 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (512 * C₁ + C₂), by positivity, ?_⟩
  intro X hX hscale
  let η : ℝ := ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hη : 0 < η := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hXpos ϑ) _
  have hsum :
      (∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
          Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
            (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
    calc
      _ ≤ ∑ N ∈ Finset.Icc 1 X,
          2 * (‖majorError150 ϕ G X N ϑ η‖ ^ 2 + ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro N hN
        rw [error_split150 hG hX N ϑ hη]
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
      _ = _ := by rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hmaj := hmajor X hX hscale
  have hmin := hminor X hX hscale
  have hmaj10 : (∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) ≤
      512 * C₁ * (X : ℝ) ^ (3 - ϑ) * Real.log X ^ 10 := by
    apply hmaj.trans
    nlinarith [mul_le_mul_of_nonneg_left (log_one_to_ten261 hX)
      (by positivity : 0 ≤ C₁ * (X : ℝ) ^ (3 - ϑ))]
  have hp := optimized_minor_powers261 hXpos ϑ
  have hmin10 : (∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) ≤
      C₂ * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 10 := by
    convert hmin using 1
    nlinarith only [congrArg (fun z : ℝ => C₂ * z * Real.log X ^ 10) hp]
  apply hsum.trans
  nlinarith [mul_nonneg (by positivity : 0 ≤ 512 * C₁)
    (by positivity : 0 ≤ (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 10)]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.log_one_to_ten261
#print axioms LeanLab.BhowmikGrimmelt2026.optimized_minor_powers261
#print axioms LeanLab.BhowmikGrimmelt2026.optimized_approximation_log10_261
