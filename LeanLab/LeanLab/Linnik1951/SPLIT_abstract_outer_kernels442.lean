/-
Split of the abstract outer Mellin kernel estimate `abstract_outer_kernels442`
into four steps plus one proved norm-integral helper.

The estimate has three layers. First, the coefficient M is removed: the line
bound turns the Mellin integral into the absolute log weighted kernel mass.
Second, the squared kernel mass is integrated over the outer interval of
frequencies, and the two frequency sign regions produce the reciprocal
difference kernel and the exponentially decaying sum kernel at radius N over R
times log cubed N. Third, the small contour remainder is absorbed by the
additive constant. Leaves 1 to 3 record the kernel layer, leaf 4 records the
square integrability of the Mellin integral itself, and the assembly below
combines them through the proved norm integral bound.

Nothing here changes the statement of `abstract_outer_kernels442`; the theorem
`abstract_outer_kernels442_split` restates it character for character and proves
it from the four leaves without using the original theorem.
-/
import LeanLab.Linnik1951.Decomp442b

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 4: the absolute kernel is log weighted integrable. For N at
least three and any frequency in the outer interval, the shifted line puts the
complex power and the Gamma factor on a fixed real part, and Gamma decay
against the exponential from the power leaves an absolutely integrable
logarithm weighted kernel. No coefficient M occurs. -/
theorem outer_kernel_integrable442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (α : ℝ) (hα : α ∈ Set.Icc (4 / (N : ℝ)) (1 / R)) :
    Integrable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  sorry

/-- LEAF. Step 2 of 4: the squared kernel mass is interval integrable in the
frequency over the outer interval. This is the measurable and bounded side of
the square expansion of equation 4.5; it carries no coefficient, no character
and no logarithmic bookkeeping. -/
theorem outer_kernel_mass_integrable442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ)
    (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  sorry

/-- LEAF. Step 3 of 4: the square integral of the absolute kernel mass over the
outer frequency interval. The two frequency sign regions of equations 4.4 to
4.6 give the reciprocal difference kernel with log power six and the decaying
sum kernel with log power seven, both at radius N over R times log cubed N, and
the exponentially small contour remainder of equation 4.3 is absorbed by the
additive constant. The coefficient M does not occur in this step. -/
theorem outer_kernel_mass_bound442 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
          C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + C := by
  sorry

/-- LEAF. Step 4 of 4: the square of the Mellin integral is interval integrable
in the frequency over the outer interval, for every coefficient satisfying the
line bound. This is the integrability half of the target conclusion, separated
from the numerical estimate; it contains no kernel bound. -/
theorem outer_mellin_sq_integrable442 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
          (4 / (N : ℝ)) (1 / R) := by
  sorry

/-- Proved helper, no leaf: a line bound on the coefficient bounds the norm of
the Mellin integral by the absolute log weighted kernel mass. This is the norm
integral inequality applied to the kernel times the coefficient. -/
private theorem norm_integral_le_weighted_mass442 (N : ℕ) (α B0 : ℝ)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M)
    (hI : Integrable (fun t : ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖∫ t : ℝ,
        ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖ ≤
      B0 * ∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  have hb (t : ℝ) :
      ‖((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖ ≤
        B0 * (‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left (hM.2 t)
      (norm_nonneg ((((1 / (N : ℝ) : ℝ) : ℂ) +
        ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)))
    nlinarith
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0) (Filter.Eventually.of_forall hb)
  calc ‖∫ t : ℝ,
        ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t‖
      ≤ ∫ t : ℝ, B0 * (‖(((1 / (N : ℝ) : ℝ) : ℂ) +
            ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := hnorm
    _ = B0 * ∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
        rw [integral_const_mul]

/-- Assembly of `abstract_outer_kernels442` from the four leaves. The line bound
removes the coefficient through the proved norm integral bound, the frequency
integration is monotone in the squared kernel mass, and the constants are
chosen so that one multiple absorbs the difference kernel term, the sum kernel
term and the contour remainder. -/
theorem abstract_outer_kernels442_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
            (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
            A * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            A * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + A := by
  obtain ⟨C, hC, Nm, hBm⟩ := outer_kernel_mass_bound442
  obtain ⟨Ni, hIi⟩ := outer_mellin_sq_integrable442 B0 hB0
  refine ⟨(1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1, ?_, max 8 (max Nm Ni), ?_⟩
  · have hnn : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C := by positivity
    linarith
  intro N hN R hR1 hR2 M hM
  have h8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNm : Nm < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNi : Ni < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have h3 : 3 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRN : R ≤ (N : ℝ) := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR2
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have h4R : 4 * R ≤ (N : ℝ) := by
    have hfour := four_rpow1622 N h8
    nlinarith [hfour, hR2]
  have hle : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRp]
    simpa using h4R
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    have h3r : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h3
    have hexp : Real.exp 1 < (N : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three h3r
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp.le
  have hlog0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hratio : (1 : ℝ) ≤ (N : ℝ) / R := (le_div_iff₀ hRp).mpr (by simpa using hRN)
  have hT1 : (1 : ℝ) ≤ T := one_le_mul_of_one_le_of_one_le hratio (one_le_pow₀ hlog1)
  have hdiff0 : (0 : ℝ) ≤ differenceKernel376 T :=
    le_trans (le_trans zero_le_one hT1) (difference_kernel_lower442 T hT1)
  have hsum0 : (0 : ℝ) ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith : (-T) ≤ T)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun u => (Real.exp_pos _).le)
  have hIu : IntervalIntegrable (fun α : ℝ => ‖mellinU1622 N M α‖ ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := hIi N hNi R hR1 hR2 M hM
  have hIk : IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := outer_kernel_mass_integrable442 N h3 R hR1 hR2
  have hbT : (∫ α in (4 / (N : ℝ))..(1 / R),
        (∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
      C * Real.log N ^ 6 * differenceKernel376 T +
        C * Real.log N ^ 7 * sumKernel376 T + C := by
    simpa only [hT] using hBm N hNm R hR1 hR2
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2) *
        ∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 := by
    have hstep : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
        ∫ α in (4 / (N : ℝ))..(1 / R),
          ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2) *
            (∫ t : ℝ,
              ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                  (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
                Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 := by
      refine intervalIntegral.integral_mono_on hle hIu (hIk.const_mul _) ?_
      intro α hα
      have hI1 := outer_kernel_integrable442 N h3 R hR1 α hα
      have hdom := norm_integral_le_weighted_mass442 N α B0 M hM hI1
      have hmass0 : (0 : ℝ) ≤ ∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
        integral_nonneg (fun t => by
          have h1 : (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t, hNr]
          exact mul_nonneg (norm_nonneg _) (pow_nonneg (Real.log_nonneg h1) 3))
      have hU : mellinU1622 N M α =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t : ℝ,
              ((((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                  (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)) * M t := rfl
      have hnormU : ‖mellinU1622 N M α‖ ≤
          (1 / (2 * Real.pi)) * (B0 * ∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
        rw [hU, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
        exact mul_le_mul_of_nonneg_left hdom (by positivity)
      have hsq := pow_le_pow_left₀ (norm_nonneg (mellinU1622 N M α)) hnormU 2
      have heq : ((1 / (2 * Real.pi)) * (B0 * ∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) ^ 2 =
          ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2) *
            (∫ t : ℝ,
              ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                  (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
                Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 := by ring
      rwa [heq] at hsq
    rw [intervalIntegral.integral_const_mul] at hstep
    exact hstep
  have hCS : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 := by positivity
  have hL6 : (0 : ℝ) ≤ Real.log N ^ 6 * differenceKernel376 T :=
    mul_nonneg (pow_nonneg hlog0 6) hdiff0
  have hL7 : (0 : ℝ) ≤ Real.log N ^ 7 * sumKernel376 T :=
    mul_nonneg (pow_nonneg hlog0 7) hsum0
  have hdC : (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C ≤
      (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1 := by linarith
  have hstep2 : ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2) *
        ∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 ≤
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C) *
        (Real.log N ^ 6 * differenceKernel376 T) +
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C) *
        (Real.log N ^ 7 * sumKernel376 T) +
      (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C := by
    have h := mul_le_mul_of_nonneg_left hbT hCS
    linarith
  refine ⟨hIu, ?_⟩
  have hfinal : (∫ α in (4 / (N : ℝ))..(1 / R), ‖mellinU1622 N M α‖ ^ 2) ≤
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) *
        (Real.log N ^ 6 * differenceKernel376 T) +
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) *
        (Real.log N ^ 7 * sumKernel376 T) +
      (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1 := by
    have ht1 := mul_le_mul_of_nonneg_right hdC hL6
    have ht2 := mul_le_mul_of_nonneg_right hdC hL7
    linarith [hmono, hstep2, ht1, ht2]
  have hshape : ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) *
        (Real.log N ^ 6 * differenceKernel376 T) +
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) *
        (Real.log N ^ 7 * sumKernel376 T) +
      (1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1 =
      ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) * Real.log N ^ 6 *
          differenceKernel376 T +
        ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) * Real.log N ^ 7 *
          sumKernel376 T +
        ((1 / (2 * Real.pi)) ^ 2 * B0 ^ 2 * C + 1) := by ring
  rw [hshape] at hfinal
  simpa only [hT] using hfinal

end LeanLab.Linnik1951
