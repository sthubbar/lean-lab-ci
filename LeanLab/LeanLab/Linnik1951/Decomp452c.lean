/-
Original page 157 equation 4.4 and its angular gap.
These lower estimates audit the absolute kernel split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp452a
import LeanLab.Linnik1951.Decomp452b

namespace LeanLab.Linnik1951
open MeasureTheory Filter
open scoped Topology

/-- On a fixed outer frequency interval, the absolute kernel stays uniformly positive
up to Mellin frequency N. This retains the N dependent angular gap. -/
theorem mellin_kernel_lower452 (N : ℕ) (hN : 9 ≤ N) (α t : ℝ)
    (ha : α ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : t ∈ Set.Icc 1 (N : ℝ)) :
    Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1) ≤
      ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t))) * Complex.Gamma (mellinLine1622 N t)‖ := by
  have hn : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hexp : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlog : 2 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) (hexp.le.trans hn)
  have hinv : 1 / Real.log N ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hlog
  let s := mellinLine1622 N t
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hsre : s.re = 1 / 2 + 1 / Real.log N := by
    simp only [s, mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : s.im = t := by
    simp only [s, mellinLine1622, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  have hzre : z.re = 1 / (N : ℝ) := by simp [z]
  have hzim : z.im = 2 * Real.pi * α := by simp [z]
  have hre : 0 < z.re := by rw [hzre]; positivity
  have him1 : 1 ≤ z.im := by
    rw [hzim]
    nlinarith [Real.pi_gt_three, ha.1]
  have him : 0 < z.im := by linarith
  have hz1 : 1 ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    rw [abs_of_pos him] at hh
    exact him1.trans hh
  have hzK : ‖z‖ ≤ 1 + 2 * Real.pi := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre, abs_of_pos him, hzre, hzim] at hh
    have h1 : 1 / (N : ℝ) ≤ 1 := (div_le_one hnp).mpr (by linarith)
    nlinarith [ha.2, Real.pi_pos]
  have hratio : z.re / z.im ≤ 1 / (N : ℝ) := by
    rw [div_le_iff₀ him, hzre]
    exact le_mul_of_one_le_right (by positivity) him1
  have hgap : (Real.pi / 2 - z.arg) * s.im ≤ 1 := by
    rw [hsim]
    calc (Real.pi / 2 - z.arg) * t ≤ (1 / (N : ℝ)) * t :=
          mul_le_mul_of_nonneg_right ((angular_gap_le_ratio452 z hre him).trans hratio)
            (by linarith [ht.1])
         _ = t / (N : ℝ) := by ring
         _ ≤ 1 := (div_le_one hnp).mpr ht.2
  exact kernel_lower_of_gap452 s z (1 + 2 * Real.pi)
    (by rw [hsre]; exact le_add_of_nonneg_right (by positivity))
    (by rw [hsre]; linarith) (by rw [hsim]; exact ht.1) hz1 hzK hgap

/-- The absolute kernel mass has a linear lower bound on a fixed outer interval. -/
theorem outer_mass_lower452 (N : ℕ) (hN : 9 ≤ N) (α : ℝ)
    (ha : α ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1)) *
      ((N : ℝ) - 1) * Real.log N ^ 3 ≤
    ∫ t : ℝ,
      ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t))) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  have hn : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  let c : ℝ := Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1)
  let f : ℝ → ℝ := fun t =>
      ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t))) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h4 : 4 / (N : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hnp]; linarith
  have hi : Integrable f := outer_kernel_integrable442 N (by omega) 1 (by norm_num)
    α ⟨h4.trans ha.1, by simpa using ha.2⟩
  have hnonneg (t : ℝ) : 0 ≤ f t := by
    apply mul_nonneg (norm_nonneg _)
    apply pow_nonneg
    apply Real.log_nonneg
    nlinarith [abs_nonneg t]
  have hlow : ∀ t ∈ Set.Icc 1 (N : ℝ), c * Real.log N ^ 3 ≤ f t := by
    intro t ht
    have hk := mellin_kernel_lower452 N hN α t ha ht
    have hl : Real.log N ≤ Real.log ((N : ℝ) * (|t| + 2)) := by
      apply Real.log_le_log hnp
      nlinarith [abs_nonneg t]
    exact mul_le_mul hk (pow_le_pow_left₀ hlog hl 3) (pow_nonneg hlog 3) (norm_nonneg _)
  change c * ((N : ℝ) - 1) * Real.log N ^ 3 ≤ ∫ t, f t
  calc
    _ = ∫ t in (1 : ℝ)..(N : ℝ), c * Real.log N ^ 3 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ t in (1 : ℝ)..(N : ℝ), f t :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        hi.intervalIntegrable hlow
    _ ≤ ∫ t, f t := by
      rw [intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ N)]
      exact setIntegral_le_integral hi (ae_of_all _ hnonneg)

/-- Squaring the absolute mass loses a full power of N on a fixed outer interval. -/
theorem outer_mass_square_lower452 (N : ℕ) (hN : 9 ≤ N) :
    ((Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1)) *
      ((N : ℝ) - 1) * Real.log N ^ 3) ^ 2 / 2 ≤
    ∫ α in (4 / (N : ℝ))..(1 : ℝ),
      (∫ t : ℝ,
        ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t))) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 := by
  have hn : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  let c : ℝ := Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1)
  let B : ℝ := c * ((N : ℝ) - 1) * Real.log N ^ 3
  let m : ℝ → ℝ := fun α => ∫ t : ℝ,
        ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t))) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3
  have h4 : 4 / (N : ℝ) ≤ (1 / 2 : ℝ) := by rw [div_le_iff₀ hnp]; linarith
  have hInt : IntervalIntegrable (fun α => m α ^ 2) volume (4 / (N : ℝ)) 1 := by
    simpa only [div_one] using outer_kernel_mass_integrable442 N (by omega) 1
      (by norm_num) (by exact Real.one_le_rpow (by linarith) (by norm_num))
  have hIntSub : IntervalIntegrable (fun α => m α ^ 2) volume (1 / 2 : ℝ) 1 := by
    apply hInt.mono_set
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      Set.uIcc_of_le (h4.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))]
    exact Set.Icc_subset_Icc h4 le_rfl
  have hB : 0 ≤ B := by
    dsimp [B, c]
    apply mul_nonneg
    · exact mul_nonneg (by positivity) (by linarith)
    · exact pow_nonneg (Real.log_nonneg (by linarith)) 3
  change B ^ 2 / 2 ≤ ∫ α in (4 / (N : ℝ))..1, m α ^ 2
  calc
    _ = ∫ α in (1 / 2 : ℝ)..1, B ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ α in (1 / 2 : ℝ)..1, m α ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hIntSub
      intro α ha
      exact pow_le_pow_left₀ hB (outer_mass_lower452 N hN α ha) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval h4 (by norm_num) le_rfl
      (ae_of_all _ (fun α => sq_nonneg (m α))) hInt

/-- The stated kernel right side has only linear N growth times a fixed log power. -/
theorem outer_kernel_rhs_le452 (N : ℕ) (hN : 3 ≤ N) (C : ℝ) (hC : 0 ≤ C) :
    C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) * Real.log N ^ 3) +
      C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) * Real.log N ^ 3) + C ≤
        57 * C * (N : ℝ) * Real.log N ^ 10 := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hl : 1 ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hn)
  let T : ℝ := (N : ℝ) * Real.log N ^ 3
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hl)
  have hd := difference_kernel_le376 T hT
  have hs := sum_kernel_le376 T hT
  have hw := frequency_window_log376 N (N : ℝ) hn (by linarith) le_rfl
  have hdiff : C * Real.log N ^ 6 * differenceKernel376 T ≤
      40 * C * (N : ℝ) * Real.log N ^ 10 := by
    calc _ ≤ C * Real.log N ^ 6 * (8 * T * (5 * Real.log N)) :=
              mul_le_mul_of_nonneg_left
                (hd.trans (mul_le_mul_of_nonneg_left hw (by positivity))) (by positivity)
         _ = _ := by dsimp [T]; ring
  have hsum : C * Real.log N ^ 7 * sumKernel376 T ≤
      16 * C * (N : ℝ) * Real.log N ^ 10 := by
    calc _ ≤ C * Real.log N ^ 7 * (16 * T) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
         _ = _ := by dsimp [T]; ring
  have hconst : C ≤ C * (N : ℝ) * Real.log N ^ 10 := by
    have hh := one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ N)
      (one_le_pow₀ hl (n := 10))
    nlinarith
  change C * Real.log N ^ 6 * differenceKernel376 T +
    C * Real.log N ^ 7 * sumKernel376 T + C ≤ _
  linarith

/-- The absolute kernel mass bound in the split is false.
This is a QUESTION about the formal split, not a paper error. -/
theorem not_outer_kernel_mass_bound452 :
    ¬ (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
          C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + C) := by
  rintro ⟨C, hC, N0, hbound⟩
  let c : ℝ := Real.pi / (3 * Real.sqrt (2 * Real.pi)) / (1 + 2 * Real.pi) * Real.exp (-1)
  have hc : 0 < c := by dsimp [c]; positivity
  have heps : 0 < c ^ 2 / (1000 * C) := by positivity
  have hh := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1)).def heps
  have hnat : ∀ᶠ N : ℕ in atTop,
      ‖Real.log (N : ℝ) ^ (4 : ℝ)‖ ≤
        (c ^ 2 / (1000 * C)) * ‖(N : ℝ) ^ (1 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hh
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hnat
  let N : ℕ := max 9 (max N0 N1) + 1
  have hN : 9 ≤ N := by dsimp [N]; omega
  have hN0 : N0 < N := by dsimp [N]; omega
  have hN1' : N1 ≤ N := by dsimp [N]; omega
  have hn : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hsmall := hN1 N hN1'
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hnp] at hsmall
  rw [abs_of_nonneg (by positivity : 0 ≤ Real.log (N : ℝ) ^ (4 : ℝ))] at hsmall
  norm_cast at hsmall
  have hlo := outer_mass_square_lower452 N hN
  have hup := hbound N hN0 1 (by norm_num)
    (Real.one_le_rpow (by linarith) (by norm_num))
  simp only [div_one] at hup
  have hrhs := outer_kernel_rhs_le452 N (by omega) C hC.le
  have htotal := hlo.trans (hup.trans hrhs)
  have hmain : c ^ 2 * ((N : ℝ) - 1) ^ 2 / 2 ≤
      57 * C * (N : ℝ) * Real.log N ^ 4 := by
    have heq1 : (c * ((N : ℝ) - 1) * Real.log N ^ 3) ^ 2 / 2 =
        (c ^ 2 * ((N : ℝ) - 1) ^ 2 / 2) * Real.log N ^ 6 := by ring
    have heq2 : 57 * C * (N : ℝ) * Real.log N ^ 10 =
        (57 * C * (N : ℝ) * Real.log N ^ 4) * Real.log N ^ 6 := by ring
    change (c * ((N : ℝ) - 1) * Real.log N ^ 3) ^ 2 / 2 ≤ _ at htotal
    rw [heq1, heq2] at htotal
    exact (mul_le_mul_iff_left₀ (pow_pos hl 6)).mp htotal
  have hupper : 57 * C * (N : ℝ) * Real.log N ^ 4 ≤
      (57 / 1000 : ℝ) * c ^ 2 * (N : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ 57 * C * (N : ℝ))
    convert hm using 1
    field_simp
  have hlower : c ^ 2 * (N : ℝ) ^ 2 / 8 ≤ c ^ 2 * ((N : ℝ) - 1) ^ 2 / 2 := by
    have hs : (N : ℝ) ^ 2 / 4 ≤ ((N : ℝ) - 1) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
    nlinarith
  have hpositive : 0 < c ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hcontra := hlower.trans (hmain.trans hupper)
  nlinarith

end LeanLab.Linnik1951
