/-
P0093 pages 157 and 158 equations 4.4 to 4.7. Separate the contour estimate from two real kernels.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357a
import LeanLab.Linnik1951.KernelBounds376

namespace LeanLab.Linnik1951

/-- P0093 page 158 after equation 4.6. The reciprocal difference kernel
integrated over the square frequency box of radius T. -/
noncomputable def differenceKernel376 (T : ℝ) : ℝ :=
  ∫ t in -T..T, ∫ u in -T..T, 1 / (1 + |t - u|)

/-- P0093 page 158 negative frequency sum case before equation 4.7.
The exponentially decreasing sum kernel on the same square box. -/
noncomputable def sumKernel376 (T : ℝ) : ℝ :=
  ∫ t in -T..T, ∫ u in -T..T, Real.exp (-(Real.pi / 4) * |t + u|)

/-- LEAF. P0093 page 158 positive frequency sum case after equation
4.6. Integrating the reciprocal difference kernel costs a factor
T log of 2T plus 1. The constant eight enlarges the elementary bound. -/
theorem difference_kernel_le376 (T : ℝ) (hT : 1 ≤ T) :
    differenceKernel376 T ≤ 8 * T * Real.log (2 * T + 1) := by
  let f : ℝ → ℝ := fun x => 1 / (1 + |x|)
  have hf : Continuous f :=
    continuous_const.div (continuous_const.add continuous_abs) (fun x => ne_of_gt (by positivity))
  have hchange : differenceKernel376 T = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hh := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => 1 / (1 + |t + u|)) (a := -T) (b := T)
    simpa only [neg_neg, sub_eq_add_neg] using hh
  have hbox := kernel_box_bound376 f hf (fun x => by dsimp [f]; positivity) T (by linarith)
  calc
    _ = ∫ t in -T..T, ∫ u in -T..T, f (t + u) := hchange
    _ ≤ 2 * T * (∫ v in -(2 * T)..(2 * T), f v) := hbox
    _ = 4 * T * Real.log (2 * T + 1) := by
      rw [show (∫ v in -(2 * T)..(2 * T), f v) = 2 * Real.log (2 * T + 1) from
        reciprocal_abs_integral376 (2 * T) (by linarith)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))

/-- LEAF. P0093 page 158 negative frequency sum case before equation
4.7. Integrating the decaying sum kernel costs a factor T. The constant
sixteen enlarges the full line exponential integral estimate. -/
theorem sum_kernel_le376 (T : ℝ) (hT : 1 ≤ T) :
    sumKernel376 T ≤ 16 * T := by
  have hf : Continuous (fun x : ℝ => Real.exp (-(Real.pi / 4) * |x|)) := by fun_prop
  have hbox := kernel_box_bound376 _ hf (fun x => (Real.exp_pos _).le) T (by linarith)
  have he := exp_abs_integral_le376 (Real.pi / 4) (2 * T) (by positivity) (by linarith)
  have hp : 2 / (Real.pi / 4) ≤ 8 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi / 4)).mpr
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ 2 * T * (∫ v in -(2 * T)..(2 * T), Real.exp (-(Real.pi / 4) * |v|)) := hbox
    _ ≤ 2 * T * 8 := mul_le_mul_of_nonneg_left (he.trans hp) (by linarith)
    _ = _ := by ring

/-- LEAF. P0093 pages 157 and 158 equation 4.4 through the two estimates after
4.6, transferred by page 159 equation 5.1. Retain the two real frequency
kernels rather than estimating them. The final constant term absorbs
the exponentially small contour truncation remainder. -/
theorem outer_to_kernels376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * Real.log N ^ 6 * differenceKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) +
              B * Real.log N ^ 7 * sumKernel376
                ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 3) + B := by
  sorry

/-- P0093 page 158 substitution before equation 4.7. When the frequency
radius is at most N log cubed N, its logarithm is at most 5 log N. -/
theorem frequency_window_log376 (x R : ℝ) (hx : 3 ≤ x) (hR : 0 ≤ R) (hRx : R ≤ x) :
    Real.log (2 * (R * Real.log x ^ 3) + 1) ≤ 5 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x)]
  have hT : R * Real.log x ^ 3 ≤ x ^ 4 := by
    calc
      _ ≤ x * x ^ 3 := mul_le_mul hRx (pow_le_pow_left₀ hlog0 hlog 3) (by positivity) (by linarith)
      _ = _ := by ring
  have hp : 1 ≤ x ^ 4 := one_le_pow₀ hx1
  have hcut : 2 * (R * Real.log x ^ 3) + 1 ≤ x ^ 5 := by
    calc
      _ ≤ 2 * x ^ 4 + 1 := by linarith
      _ ≤ 3 * x ^ 4 := by linarith
      _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = _ := by ring
  have hh := Real.log_le_log (by positivity : 0 < 2 * (R * Real.log x ^ 3) + 1) hcut
  rwa [Real.log_pow] at hh

/-- P0093 page 158 equation 4.7 with its frequency radius substitution.
Exact mellin_positive_far357 statement. CONDITIONAL only on the contour
comparison. Both explicit real kernel bounds are proved. -/
theorem mellin_positive_far_decomposed376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨B, hB, N0, hb⟩ := outer_to_kernels376 hG
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨57 * B, by positivity, max 3 (max N0 L), ?_⟩
  intro N hN q hq hqt χ hχ
  have h3 : 3 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    have hh := Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
    simpa only [Real.log_exp] using hh
  let D := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)
  let R := (N : ℝ) / D
  let T := R * Real.log N ^ 3
  have htau : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le hqR htau
  have hDpos : 0 < D := by linarith
  have hDN : D ≤ N := by
    calc
      D ≤ (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right hqt (by positivity)
      _ = (N : ℝ) ^ (2 / 7 : ℝ) := by rw [← Real.rpow_add hNp]; congr 1; norm_num
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one _
  have hR1 : 1 ≤ R := (le_div_iff₀ hDpos).mpr (by simpa using hDN)
  have hRN : R ≤ N := (div_le_iff₀ hDpos).mpr (by
    simpa using mul_le_mul_of_nonneg_left hD1 hNp.le)
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have hdiff := difference_kernel_le376 T hT1
  have hsum := sum_kernel_le376 T hT1
  have hwindow := frequency_window_log376 N R (by exact_mod_cast h3.le) (by linarith) hRN
  have hsmall : 1 ≤ R * Real.log N ^ 10 := one_le_mul_of_one_le_of_one_le hR1 (one_le_pow₀ hlog)
  have h := hb N hN0 q hq hqt χ hχ
  change _ ≤ B * Real.log N ^ 6 * differenceKernel376 T +
    B * Real.log N ^ 7 * sumKernel376 T + B at h
  have hd : B * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (hdiff.trans (mul_le_mul_of_nonneg_left hwindow (by positivity))) (by positivity)
      _ = _ := by dsimp [T]; ring
  have hs : B * Real.log N ^ 7 * sumKernel376 T ≤
      16 * B * R * Real.log N ^ 10 := by
    calc
      _ ≤ B * Real.log N ^ 7 * (16 * T) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [T]; ring
  have hconst : B ≤ B * R * Real.log N ^ 10 := by
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hsmall hB.le
  calc
    _ ≤ 57 * B * R * Real.log N ^ 10 := by linarith
    _ = _ := by dsimp [R, D]; ring

end LeanLab.Linnik1951
