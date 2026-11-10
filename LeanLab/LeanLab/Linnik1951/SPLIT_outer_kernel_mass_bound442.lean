/-
Split of the abstract outer Mellin kernel mass estimate `outer_kernel_mass_bound442`
into four steps.

The parent statement bounds the square, over the outer frequency interval from
four over N to one over R, of the absolute log weighted Mellin kernel mass, by a
multiple of the log sixth power times the reciprocal difference kernel at radius
N over R times log cubed N, a multiple of the log seventh power times the
exponentially decaying sum kernel at the same radius, and an additive constant.

The steps below are the elementary route through those magnitudes. First the
weighted mass of the kernel is bounded at every frequency of the outer interval
by one constant times the square root of N times the cube of log N, uniformly in
the frequency and in the radius. Second the square of that mass is interval
integrable in the frequency. Third the frequency integral is bounded by the
length of the interval times that uniform bound, which is where the factor one
over R appears. Fourth the resulting crude product is absorbed by the difference
kernel term, whose radius is large enough to dominate every power of log N that
occurs.

Nothing here changes the statement of `outer_kernel_mass_bound442`; the theorem
`outer_kernel_mass_bound442_split` restates it character for character and proves
it from the four leaves without using the parent theorem.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 4, the pointwise mass bound on the outer interval. There is a
positive constant G such that for N at least three, for every radius R in the
admissible range, and for every frequency α between four over N and one over R,
the absolute Mellin kernel weighted by the cube of the logarithm of N times the
sum of absolute t and two has mass at most G times the square root of N times the
cube of log N. The real part of the Mellin line is at most one for N at least
eight, and the frequency lower bound keeps the imaginary part of the logarithm of
the kernel base away from pi over two by a fixed gap, so the Gamma decay survives
the frequency shift. No square of the mass, no integration over α and no kernel
occurs. -/
theorem outer_kernel_pointwise_mass442 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 3 ≤ N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
      ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
        (∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
          G * Real.sqrt (N : ℝ) * Real.log N ^ 3 := by
  sorry

/-- LEAF. Step 2 of 4, the integrability of the squared mass in the frequency.
For N at least three and every admissible radius, the square of the absolute log
weighted Mellin kernel mass is interval integrable over the outer frequency
interval. This is the measure theoretic half of the parent conclusion and
carries no estimate. -/
theorem outer_kernel_mass_sq_intervalIntegrable442 (N : ℕ) (hN : 3 ≤ N)
    (R : ℝ) (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  sorry

/-- LEAF. Step 3 of 4, the frequency integral of a uniform bound. Assume the
weighted mass is at most G times the square root of N times the cube of log N at
every frequency of the outer interval, and assume the square of the mass is
interval integrable there. Then the frequency integral of the squared mass is at
most the square of that bound times the length of the interval, written as one
over R minus four over N. This is the monotonicity of the interval integral
against a constant, and it is the only step where the factor one over R is
produced. -/
theorem outer_kernel_mass_constant_integral442 (N : ℕ) (hN : 8 ≤ N)
    (R : ℝ) (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (G : ℝ) (hG : 0 < G)
    (hmass : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
        G * Real.sqrt (N : ℝ) * Real.log N ^ 3)
    (hInt : IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R)) :
    (∫ α in (4 / (N : ℝ))..(1 / R),
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
      G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) := by
  have hN8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hN1
  -- the exponent comparison `4 N ^ (2/7) ≤ N`, from `4 ≤ N ^ (5/7)`
  have h5 : (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) := by
    have hA : (8 : ℝ) ^ (5 / 7 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) :=
      Real.rpow_le_rpow (x := 8) (y := (N : ℝ)) (z := (5 / 7 : ℝ))
        (by norm_num) hN8 (by norm_num)
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hB : (4 : ℝ) ≤ (8 : ℝ) ^ (5 / 7 : ℝ) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := h4
        _ ≤ (2 : ℝ) ^ (15 / 7 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = ((2 : ℝ) ^ (3 : ℝ)) ^ (5 / 7 : ℝ) := by
              rw [show (15 / 7 : ℝ) = 3 * (5 / 7) by norm_num,
                Real.rpow_mul (x := 2) (by norm_num)]
        _ = (8 : ℝ) ^ (5 / 7 : ℝ) := by rw [h8]
    linarith
  have hsplit : (N : ℝ) ^ (2 / 7 : ℝ) * (N : ℝ) ^ (5 / 7 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNr]
    norm_num
  have h4N : 4 * (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) := by
    calc 4 * (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = (N : ℝ) := by rw [mul_comm]; exact hsplit
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNr hRpos]
    nlinarith [hR2, h4N]
  have hpoint : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2 ≤
        G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 := by
    intro α hα
    have h1 : (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
        G * Real.sqrt (N : ℝ) * Real.log N ^ 3 := hmass α hα
    have hF0 : (0 : ℝ) ≤ (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
      apply MeasureTheory.integral_nonneg
      intro t
      have hlogt : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t])
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hlogt 3)
    calc (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2
        ≤ (G * Real.sqrt (N : ℝ) * Real.log N ^ 3) ^ 2 := pow_le_pow_left₀ hF0 h1 2
      _ = G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 := by
          rw [mul_pow, mul_pow]
          ring
  have hC : (0 : ℝ) ≤ G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 := by positivity
  calc (∫ α in (4 / (N : ℝ))..(1 / R),
        (∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2)
      ≤ ∫ α in (4 / (N : ℝ))..(1 / R), G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 :=
        intervalIntegral.integral_mono_on hab hInt intervalIntegrable_const hpoint
    _ = G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- The reciprocal difference kernel on the square box, as a function of the outer
variable, is continuous: the integrand `1 / (1 + |t - u|)` is bounded by one. -/
private lemma cont_kernel_inner442 (T : ℝ) :
    Continuous fun t : ℝ => ∫ u in (-T)..T, 1 / (1 + |t - u|) := by
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => (1 : ℝ)) (a := -T) (b := T) (μ := volume)
  · intro t
    have hc : Continuous fun u : ℝ => 1 / (1 + |t - u|) :=
      continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity))
    exact hc.aestronglyMeasurable
  · intro t
    filter_upwards with u _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    linarith [abs_nonneg (t - u)]
  · exact intervalIntegrable_const
  · filter_upwards with u _
    exact continuous_const.div (by fun_prop) (fun t => ne_of_gt (by positivity))

/-- The reciprocal difference kernel dominates its own radius once the radius is at
least one half: on the square of radius `T` the bracket is at most `1 + 2 T`, so the
double integral is at least `4 T ^ 2 / (1 + 2 T)`, and that exceeds `T` as soon as
`T ≥ 1/2`. -/
private lemma differenceKernel376_self_le (T : ℝ) (hT : (1 / 2 : ℝ) ≤ T) :
    T ≤ differenceKernel376 T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hden : (0 : ℝ) < 1 + 2 * T := by linarith
  have hinner : ∀ t ∈ Set.Icc (-T) T,
      (2 * T) * (1 / (1 + 2 * T)) ≤ ∫ u in (-T)..T, 1 / (1 + |t - u|) := by
    intro t ht
    have hcont : IntervalIntegrable (fun u : ℝ => 1 / (1 + |t - u|)) volume (-T) T := by
      have hc : Continuous fun u : ℝ => 1 / (1 + |t - u|) :=
        continuous_const.div (by fun_prop) (fun u => ne_of_gt (by positivity))
      exact hc.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun _ : ℝ => 1 / (1 + 2 * T)) (g := fun u : ℝ => 1 / (1 + |t - u|))
      (a := -T) (b := T) (by linarith) intervalIntegrable_const hcont ?_
    · simpa [intervalIntegral.integral_const, smul_eq_mul, two_mul] using hmono
    · intro u hu
      refine one_div_le_one_div_of_le (a := 1 + |t - u|) (b := 1 + 2 * T)
        (by positivity) ?_
      have h1 : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : |u| ≤ T := abs_le.mpr ⟨hu.1, hu.2⟩
      have h3 : |t - u| ≤ 2 * T := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
      linarith
  have hcont2 : IntervalIntegrable (fun t : ℝ => ∫ u in (-T)..T, 1 / (1 + |t - u|))
      volume (-T) T := (cont_kernel_inner442 T).intervalIntegrable _ _
  have houter := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ : ℝ => (2 * T) * (1 / (1 + 2 * T)))
    (g := fun t : ℝ => ∫ u in (-T)..T, 1 / (1 + |t - u|))
    (a := -T) (b := T) (by linarith) intervalIntegrable_const hcont2 hinner
  have hval : (∫ t in (-T)..T, ((2 * T) * (1 / (1 + 2 * T)) : ℝ)) =
      4 * T ^ 2 / (1 + 2 * T) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  have hkey : T ≤ 4 * T ^ 2 / (1 + 2 * T) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg hT0.le (by linarith : (0 : ℝ) ≤ 2 * T - 1)]
  unfold differenceKernel376
  calc T ≤ 4 * T ^ 2 / (1 + 2 * T) := hkey
    _ = ∫ t in (-T)..T, ((2 * T) * (1 / (1 + 2 * T)) : ℝ) := hval.symm
    _ ≤ ∫ t in (-T)..T, ∫ u in (-T)..T, 1 / (1 + |t - u|) := houter

/-- The exponentially decreasing sum kernel is nonnegative. -/
private lemma sumKernel376_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ sumKernel376 T := by
  unfold sumKernel376
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t ht
  apply intervalIntegral.integral_nonneg (by linarith)
  intro u hu
  exact (Real.exp_pos _).le

/-- LEAF. Step 4 of 4, absorption by the difference kernel term. For N at least
three, every admissible radius, and every positive G, the crude bound of step
three is at most one plus the square of G times the log sixth power times the
reciprocal difference kernel at radius N over R times log cubed N, plus the same
multiple of the log seventh power times the sum kernel at that radius, plus one.
The radius is at least one, the difference kernel dominates its own radius there,
and log N is at least one, so the log ninth power supplied by the difference
kernel term covers the log sixth power of the crude bound together with the
factor N over R. The sum kernel term is only used as a nonnegative quantity. -/
theorem outer_kernel_mass_absorb442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (G : ℝ) (hG : 0 < G) :
    G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) ≤
      (G ^ 2 + 1) * Real.log N ^ 6 *
          differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
        (G ^ 2 + 1) * Real.log N ^ 7 *
          sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + (G ^ 2 + 1) := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    exact le_trans (le_of_lt Real.exp_one_lt_three) hN3
  have hlog0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
  have hlog3 : (1 : ℝ) ≤ Real.log N ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ Real.log N ^ 3 := pow_le_pow_left₀ zero_le_one hlog1 3
  have hNdivR1 : (1 : ℝ) ≤ (N : ℝ) / R := by
    rw [le_div_iff₀ hRpos]
    have hpow : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) := by
      calc (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = (N : ℝ) := Real.rpow_one _
    linarith
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hTval
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTval]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (N : ℝ) / R * Real.log N ^ 3 :=
          mul_le_mul hNdivR1 hlog3 zero_le_one (by linarith)
  have hT0 : (0 : ℝ) < T := by linarith
  have hD : T ≤ differenceKernel376 T := differenceKernel376_self_le T (by linarith)
  have hNR : (N : ℝ) / R ≤ T := by
    have h := mul_le_mul_of_nonneg_left hlog3 (by positivity : (0 : ℝ) ≤ (N : ℝ) / R)
    rw [hTval]
    simpa using h
  have hL6 : (0 : ℝ) ≤ Real.log N ^ 6 := by positivity
  have hL7 : (0 : ℝ) ≤ Real.log N ^ 7 := by positivity
  have hS : 0 ≤ sumKernel376 T := sumKernel376_nonneg T hT0.le
  have hsqrt : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hprod : Real.log N ^ 6 * (G ^ 2 * ((N : ℝ) / R)) ≤
      Real.log N ^ 6 * ((G ^ 2 + 1) * differenceKernel376 T) := by
    apply mul_le_mul_of_nonneg_left _ hL6
    exact mul_le_mul (by linarith : G ^ 2 ≤ G ^ 2 + 1) (hNR.trans hD) (by positivity)
      (by positivity)
  have he1 : Real.log N ^ 6 * (G ^ 2 * ((N : ℝ) / R)) =
      G ^ 2 * (N : ℝ) * Real.log N ^ 6 * (1 / R) := by
    rw [div_eq_mul_inv]
    ring
  have he2 : Real.log N ^ 6 * ((G ^ 2 + 1) * differenceKernel376 T) =
      (G ^ 2 + 1) * Real.log N ^ 6 * differenceKernel376 T := by ring
  rw [hsqrt]
  have hstep : G ^ 2 * (N : ℝ) * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) ≤
      G ^ 2 * (N : ℝ) * Real.log N ^ 6 * (1 / R) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
    linarith
  have hzero : (0 : ℝ) ≤ (G ^ 2 + 1) * Real.log N ^ 7 * sumKernel376 T := by
    have : (0 : ℝ) ≤ G ^ 2 + 1 := by positivity
    exact mul_nonneg (mul_nonneg this hL7) hS
  have hG0 : (0 : ℝ) ≤ G ^ 2 + 1 := by positivity
  linarith [hstep, hprod, he1, he2, hzero, hG0]

/-- The parent statement `outer_kernel_mass_bound442`, reassembled from the four
leaves. The constant is one plus the square of the mass constant of step one, and
the threshold is eight so that four over N does not exceed one over R and log N
is at least one. No use of the parent theorem, no sorry. -/
theorem outer_kernel_mass_bound442_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
          C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + C := by
  obtain ⟨G, hG, hmass⟩ := outer_kernel_pointwise_mass442
  refine ⟨G ^ 2 + 1, by positivity, 8, ?_⟩
  intro N hN R hR hR2
  have h3 : 3 ≤ N := by omega
  have hInt := outer_kernel_mass_sq_intervalIntegrable442 N h3 R hR hR2
  have hstep :=
    outer_kernel_mass_constant_integral442 N (by omega) R hR hR2 G hG
      (fun α hα => hmass N h3 R hR hR2 α hα) hInt
  have hbook := outer_kernel_mass_absorb442 N h3 R hR hR2 G hG
  linarith

end LeanLab.Linnik1951
