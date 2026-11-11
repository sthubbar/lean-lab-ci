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

set_option maxHeartbeats 20000000

/-- The imaginary part of the Mellin kernel base. -/
private lemma base_im442 (N : ℕ) (α : ℝ) :
    ((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).im
      = 2 * Real.pi * α := by
  simp

/-- The real part of the Mellin kernel base. -/
private lemma base_re442 (N : ℕ) (α : ℝ) :
    ((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).re
      = 1 / (N : ℝ) := by
  simp

/-- The argument of the Mellin kernel base stays a fixed distance away from both ends of
the upper half axis, uniformly on the outer interval. -/
private lemma base_arg_bounds442 (N : ℕ) (hN : 3 ≤ N) {z : ℂ}
    (hre : z.re = 1 / (N : ℝ)) (him : 0 ≤ z.im) (hzn : ‖z‖ ≤ 1 + 4 * Real.pi) :
    0 ≤ z.arg ∧ z.arg ≤ Real.pi / 2 - 1 / (100 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him
  have hargle : z.arg ≤ Real.pi / 2 := by
    rw [Complex.arg_le_pi_div_two_iff]
    left
    rw [hre]
    positivity
  have hcos : Real.cos z.arg = z.re / ‖z‖ := Complex.cos_arg hz0
  have hstep1 : Real.cos z.arg ≤ Real.pi / 2 - z.arg := by
    rw [← Real.sin_pi_div_two_sub z.arg]
    exact Real.sin_le (by linarith)
  have hznpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hmono : (1 / (N : ℝ)) / (1 + 4 * Real.pi) ≤ (1 / (N : ℝ)) / ‖z‖ :=
    div_le_div_of_nonneg_left (by positivity) hznpos hzn
  have heq : (1 / (N : ℝ)) / (1 + 4 * Real.pi) = 1 / ((N : ℝ) * (1 + 4 * Real.pi)) := by
    field_simp
  rw [heq] at hmono
  have hcmp : 1 / (100 * (N : ℝ)) ≤ 1 / ((N : ℝ) * (1 + 4 * Real.pi)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Real.pi_lt_four, hNr]
  have hlow : 1 / (100 * (N : ℝ)) ≤ Real.cos z.arg := by
    rw [hcos, hre]
    linarith
  refine ⟨harg0, ?_⟩
  linarith

/-- `log y ^ 3 ≤ y ^ 3` for `y ≥ 1`. -/
private lemma log_cube_le_self442 {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 3 ≤ y ^ 3 := by
  have h0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
  exact pow_le_pow_left₀ h0 h1 3

/-- One over `log N` is at most one for `N ≥ 3`. -/
private lemma inv_log_le_one442 (N : ℕ) (hN : 3 ≤ N) : 1 / Real.log N ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hN)
  rw [div_le_one (by linarith)]
  exact hlog1

/-- `1 ≤ log N` for `N ≥ 3`. -/
private lemma one_le_log442 (N : ℕ) (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hN)

/-- The real part of the Mellin line. -/
private lemma mellin_re442 (N : ℕ) (t : ℝ) :
    (mellinLine1622 N t).re = 1 / 2 + 1 / Real.log N := by
  rw [mellinLine1622]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- The imaginary part of the Mellin line. -/
private lemma mellin_im442 (N : ℕ) (t : ℝ) : (mellinLine1622 N t).im = t := by
  rw [mellinLine1622]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring


/-- `‖z‖ ^ (-σ) ≤ N ^ (3/2)` for the Mellin base of the outer interval. -/
private lemma norm_rpow_le442 (N : ℕ) (hN : 3 ≤ N) {z : ℂ}
    (hre : z.re = 1 / (N : ℝ)) :
    ‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) ≤ (N : ℝ) ^ (3 / 2 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log N := by
    have := one_le_log442 N hN
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hznpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hσpos : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hσle : 1 / 2 + 1 / Real.log N ≤ 3 / 2 := by
    have := inv_log_le_one442 N hN
    linarith
  rw [Real.rpow_neg hznpos.le, ← Real.inv_rpow hznpos.le]
  refine le_trans (Real.rpow_le_rpow (by positivity) ?_ hσpos)
    (Real.rpow_le_rpow_of_exponent_le hN1 hσle)
  rw [inv_le_iff_one_le_mul₀ hznpos]
  have hge : 1 / (N : ℝ) ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    rw [hre, abs_of_nonneg (by positivity)] at h
    exact h
  have hmul : (N : ℝ) * (1 / (N : ℝ)) ≤ (N : ℝ) * ‖z‖ := mul_le_mul_of_nonneg_left hge hNr.le
  have hone : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp
  linarith

/-- The crude product estimate that absorbs the polynomial factor into the constant. -/
private lemma step_bound442 (N : ℕ) (t E A : ℝ) (hA : A ≤ (N : ℝ) ^ (3 / 2 : ℝ)) (hE : 0 ≤ E) :
    A * Real.sqrt (2 * Real.pi) * (3 + |t|) * E ≤
      ((N : ℝ) ^ (3 / 2 : ℝ) *
          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
        (1 + |t|) * E := by
  have hD : Real.sqrt (2 * Real.pi) * (3 + |t|) ≤
      (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) * (1 + |t|) := by
    have h1 : Real.sqrt (2 * Real.pi) * (3 + |t|) ≤
        Real.sqrt (2 * Real.pi) * (3 * (1 + |t|)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      linarith [abs_nonneg t]
    have h2 : Real.sqrt (2 * Real.pi) * (3 * (1 + |t|)) ≤
        (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) * (1 + |t|) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2),
        Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/2)]
    linarith
  calc A * Real.sqrt (2 * Real.pi) * (3 + |t|) * E
      = A * (Real.sqrt (2 * Real.pi) * (3 + |t|)) * E := by ring
    _ ≤ (N : ℝ) ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * (3 + |t|)) * E := by gcongr
    _ ≤ (N : ℝ) ^ (3 / 2 : ℝ) *
          ((Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) * (1 + |t|)) * E := by
        gcongr
    _ = ((N : ℝ) ^ (3 / 2 : ℝ) *
          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
        (1 + |t|) * E := by ring

/-- The dominating function is integrable on the whole line: a power of `log` times
`1 + |t|` times an exponential decay. -/
private lemma integrable_dominant442 (N : ℕ) (hN : 3 ≤ N) (K δ : ℝ) (hK : 0 ≤ K)
    (hδ : 0 < δ) :
    Integrable (fun t : ℝ =>
      K * (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ) * |t|)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  set f : ℝ → ℝ := fun t =>
    K * (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-(δ) * |t|) with hfval
  have hlog1 : ∀ t : ℝ, (1 : ℝ) ≤ (N : ℝ) * (|t| + 2) := by
    intro t
    have h2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hfnonneg : ∀ t : ℝ, 0 ≤ f t := by
    intro t
    have hl : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) := Real.log_nonneg (hlog1 t)
    have hp : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := pow_nonneg hl 3
    exact mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) hp) (Real.exp_pos _).le
  have hcont : Continuous f := by
    have hbase : Continuous fun t : ℝ => (N : ℝ) * (|t| + 2) :=
      continuous_const.mul (continuous_abs.add continuous_const)
    have hlog : Continuous fun t : ℝ => Real.log ((N : ℝ) * (|t| + 2)) :=
      hbase.log (fun t => by
        have := hlog1 t
        linarith)
    have hexp : Continuous fun t : ℝ => Real.exp (-(δ) * |t|) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_abs)
    exact ((continuous_const.mul (continuous_const.add continuous_abs)).mul (hlog.pow 3)).mul hexp
  have hT : ∀ᶠ t : ℝ in Filter.atTop,
      t ^ (4 : ℝ) * Real.exp (-(δ / 2) * t) ≤ 1 :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (δ / 2) hhalf).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hO : f =O[Filter.atTop] fun t : ℝ => Real.exp (-(δ / 2) * t) := by
    refine Asymptotics.IsBigO.of_bound (54 * K * (N : ℝ) ^ 3) ?_
    filter_upwards [hT, Filter.eventually_ge_atTop (1 : ℝ)] with t ht hge
    have ht0 : (0 : ℝ) < t := by linarith
    have habs : |t| = t := abs_of_nonneg (by linarith)
    have hlogc : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ ((N : ℝ) * (3 * t)) ^ 3 := by
      have h2 : (N : ℝ) * (|t| + 2) ≤ (N : ℝ) * (3 * t) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [habs]; linarith
      exact (log_cube_le_self442 (hlog1 t)).trans (pow_le_pow_left₀ (by positivity) h2 3)
    have hstep : f t ≤ K * (2 * t) * ((N : ℝ) * (3 * t)) ^ 3 * Real.exp (-(δ * t)) := by
      change K * (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 * Real.exp (-δ * |t|) ≤
        K * (2 * t) * ((N : ℝ) * (3 * t)) ^ 3 * Real.exp (-(δ * t))
      have h1 : (1 + |t|) ≤ 2 * t := by rw [habs]; linarith
      have h4 : Real.exp (-δ * |t|) = Real.exp (-(δ * t)) := by rw [habs]; ring_nf
      rw [h4]
      have s1 : K * (1 + |t|) ≤ K * (2 * t) := mul_le_mul_of_nonneg_left h1 hK
      have s2 : K * (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          K * (2 * t) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
        mul_le_mul_of_nonneg_right s1 (pow_nonneg (Real.log_nonneg (hlog1 t)) 3)
      have hm : K * (2 * t) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          K * (2 * t) * ((N : ℝ) * (3 * t)) ^ 3 :=
        mul_le_mul_of_nonneg_left hlogc (by positivity)
      exact mul_le_mul_of_nonneg_right (s2.trans hm) (Real.exp_pos _).le
    have hpoly : K * (2 * t) * ((N : ℝ) * (3 * t)) ^ 3 * Real.exp (-(δ * t))
        = 54 * K * (N : ℝ) ^ 3 * (t ^ (4 : ℝ) * Real.exp (-(δ / 2) * t)) *
            Real.exp (-(δ / 2) * t) := by
      rw [show t ^ (4 : ℝ) = t ^ 4 by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
      have he : Real.exp (-(δ * t)) = Real.exp (-(δ / 2) * t) * Real.exp (-(δ / 2) * t) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      ring
    have hmain : f t ≤ 54 * K * (N : ℝ) ^ 3 * Real.exp (-(δ / 2) * t) := by
      refine hstep.trans ?_
      rw [hpoly]
      have h54 : (0 : ℝ) ≤ 54 * K * (N : ℝ) ^ 3 * Real.exp (-(δ / 2) * t) := by positivity
      have hmul := mul_le_mul_of_nonneg_left ht h54
      calc 54 * K * (N : ℝ) ^ 3 * (t ^ (4 : ℝ) * Real.exp (-(δ / 2) * t)) *
            Real.exp (-(δ / 2) * t)
          = 54 * K * (N : ℝ) ^ 3 * Real.exp (-(δ / 2) * t) *
              (t ^ (4 : ℝ) * Real.exp (-(δ / 2) * t)) := by ring
        _ ≤ 54 * K * (N : ℝ) ^ 3 * Real.exp (-(δ / 2) * t) * 1 := hmul
        _ = 54 * K * (N : ℝ) ^ 3 * Real.exp (-(δ / 2) * t) := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (hfnonneg t)]
    exact hmain
  have hpos : IntegrableOn f (Set.Ioi 0) :=
    integrable_of_isBigO_exp_neg hhalf hcont.continuousOn hO
  have hio : IntegrableOn f (Set.Iio 0) := by
    have h := IntegrableOn.comp_neg (μ := volume) (s := Set.Ioi 0) hpos
    have hfun : (fun x : ℝ => f (-x)) = f := by
      funext x
      simp only [hfval, abs_neg]
    rw [hfun] at h
    rwa [show -(Set.Ioi (0 : ℝ)) = Set.Iio 0 from by
      ext x; simp [Set.mem_neg]] at h
  have hneg : IntegrableOn f (Set.Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hio
  have hunion : IntegrableOn f (Set.Ioi 0 ∪ Set.Iic 0) := IntegrableOn.union hpos hneg
  have hall : IntegrableOn f Set.univ := by
    rwa [show Set.Ioi (0 : ℝ) ∪ Set.Iic 0 = Set.univ from by
      ext x
      simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
      rcases lt_or_ge x 0 with h | h
      · exact Or.inr h.le
      · rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (le_of_eq h'.symm)] at hunion
  simpa [IntegrableOn] using hall

/-! ## New work for leaf 2: continuity of the integrand, the frequency dependent
argument gap, and the dominated convergence assembly. -/

/-- The Mellin line is continuous in the frequency. -/
private lemma mellinLine_cont442 (N : ℕ) : Continuous (mellinLine1622 N) := by
  unfold mellinLine1622
  fun_prop

private lemma mellinLine_cont_pair442 (N : ℕ) :
    Continuous fun p : ℝ × ℝ => mellinLine1622 N p.2 :=
  (mellinLine_cont442 N).comp continuous_snd

/-- The Mellin kernel base is continuous in the frequency. -/
private lemma base_cont_pair442 (N : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      ((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * p.1 : ℝ) : ℂ) * Complex.I) := by
  fun_prop

/-- The Mellin kernel base avoids the cut of the complex power. -/
private lemma base_slitPlane442 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ∈
      Complex.slitPlane := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := hN
    exact_mod_cast this
  refine Or.inl ?_
  rw [base_re442]
  positivity

/-- The Gamma function is continuous at every point of the right half plane. -/
private lemma gamma_cont_at442 {s : ℂ} (h1 : (1 : ℝ) / 2 ≤ s.re) :
    ContinuousAt Complex.Gamma s := by
  refine Complex.continuousAt_Gamma s ?_
  intro m hm
  have hre : s.re = -(m : ℝ) := by
    rw [hm]
    simp
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The Gamma function is continuous along the Mellin line. -/
private lemma gamma_cont_line442 (N : ℕ) (hN : 3 ≤ N) :
    Continuous fun t : ℝ => Complex.Gamma (mellinLine1622 N t) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hlogpos : (0 : ℝ) < Real.log N := by
    have h := one_le_log442 N hN
    linarith
  have hinv : (0 : ℝ) < 1 / Real.log N := by positivity
  have h1 : (1 : ℝ) / 2 ≤ (mellinLine1622 N t).re := by
    rw [mellin_re442]
    linarith
  exact (gamma_cont_at442 h1).comp (mellinLine_cont442 N).continuousAt

private lemma gamma_cont_pair442 (N : ℕ) (hN : 3 ≤ N) :
    Continuous fun p : ℝ × ℝ => Complex.Gamma (mellinLine1622 N p.2) :=
  (gamma_cont_line442 N hN).comp continuous_snd

/-- The logarithm weight is continuous on the product. -/
private lemma log_factor_cont_pair442 (N : ℕ) (hN : 1 ≤ N) :
    Continuous fun p : ℝ × ℝ => Real.log ((N : ℝ) * (|p.2| + 2)) := by
  apply Continuous.log
  · fun_prop
  · intro p
    have h1 : (1 : ℝ) ≤ |p.2| + 2 := by linarith [abs_nonneg p.2]
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := hN
      exact_mod_cast this
    nlinarith

/-- The uncurried Mellin integrand is continuous on the plane, so it is jointly
strongly measurable and each frequency slice is continuous in the integration variable. -/
private lemma integrand_cont_pair442 (N : ℕ) (hN : 3 ≤ N) :
    Continuous fun p : ℝ × ℝ =>
      ‖((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * p.1 : ℝ) : ℂ) * Complex.I) ^
          (-(mellinLine1622 N p.2)) * Complex.Gamma (mellinLine1622 N p.2)‖ *
        Real.log ((N : ℝ) * (|p.2| + 2)) ^ 3 := by
  have hN1 : 1 ≤ N := by omega
  have hcp : Continuous fun p : ℝ × ℝ =>
      ((((1 / (N : ℝ) : ℝ)) : ℂ) + ((2 * Real.pi * p.1 : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine1622 N p.2)) :=
    (base_cont_pair442 N).cpow (mellinLine_cont_pair442 N).neg
      (fun p => base_slitPlane442 N hN1 p.1)
  exact (hcp.mul (gamma_cont_pair442 N hN)).norm.mul
    ((log_factor_cont_pair442 N hN1).pow 3)

/-- A positive lower bound for the frequency forces a positive lower bound for the
argument of the kernel base, uniform in the frequency. -/
private lemma arg_lower442 (N : ℕ) {z : ℂ} {c : ℝ} (hc0 : 0 ≤ c)
    (him : 2 * Real.pi * c ≤ z.im) (hzn : ‖z‖ ≤ 1 + 4 * Real.pi) (hz0 : z ≠ 0)
    (hc : 1 / (100 * (N : ℝ)) ≤ 2 * Real.pi * c / (1 + 4 * Real.pi)) :
    1 / (100 * (N : ℝ)) ≤ z.arg := by
  have hznpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have h2pic : (0 : ℝ) ≤ 2 * Real.pi * c := by positivity
  have him0 : 0 ≤ z.im := le_trans h2pic him
  have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him0
  have hsin : Real.sin z.arg = z.im / ‖z‖ := Complex.sin_arg z
  have h1 : Real.sin z.arg ≤ z.arg := Real.sin_le harg0
  have hstep1 : 2 * Real.pi * c / (1 + 4 * Real.pi) ≤ 2 * Real.pi * c / ‖z‖ :=
    div_le_div_of_nonneg_left h2pic hznpos hzn
  have hstep2 : 2 * Real.pi * c / ‖z‖ ≤ z.im / ‖z‖ := by
    rw [div_le_div_iff_of_pos_right hznpos]
    exact him
  rw [hsin] at h1
  linarith
private lemma kernel_bound_arg442 (N : ℕ) (hN : 3 ≤ N) {z : ℂ}
    (hre : z.re = 1 / (N : ℝ)) (him : 0 ≤ z.im) (hzn : ‖z‖ ≤ 1 + 4 * Real.pi)
    (harglow : 1 / (100 * (N : ℝ)) ≤ z.arg)
    (hargup : z.arg ≤ Real.pi / 2 - 1 / (100 * (N : ℝ))) (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤
      ((N : ℝ) ^ (3 / 2 : ℝ) *
          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
        (1 + |t|) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hδ0 : (0 : ℝ) < 1 / (100 * (N : ℝ)) := by positivity
  have hlogpos : (0 : ℝ) < Real.log N := by
    have := one_le_log442 N hN
    linarith
  have hloginv : (0 : ℝ) < 1 / Real.log N := div_pos one_pos hlogpos
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hznpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hA := norm_rpow_le442 N hN hre
  have hσpos : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N := by positivity
  have hK : (0 : ℝ) ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi) := by
    have h1 : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h2 : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h3 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    linarith
  -- the power of the base
  have hcpow : ‖z ^ (-(mellinLine1622 N t))‖ ≤
      ‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) * Real.exp (t * z.arg) := by
    have h := Complex.norm_cpow_le z (-(mellinLine1622 N t))
    rw [show (-(mellinLine1622 N t)).re = -(1 / 2 + 1 / Real.log N) by
          rw [Complex.neg_re, mellin_re442],
        show (-(mellinLine1622 N t)).im = -t by rw [Complex.neg_im, mellin_im442]] at h
    refine h.trans_eq ?_
    rw [show z.arg * -t = -(z.arg * t) by ring, Real.exp_neg, div_inv_eq_mul, mul_comm z.arg t]
  -- the Gaussian-type decay of `Γ`
  have hPL : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * t / 2)) := by
    have h1 : (1 : ℝ) / 2 ≤ (mellinLine1622 N t).re := by
      rw [mellin_re442]; linarith [hloginv]
    have h2 : (mellinLine1622 N t).re ≤ 3 / 2 := by
      rw [mellin_re442]; linarith [inv_log_le_one442 N hN]
    have hsi : (mellinLine1622 N t).im = t := mellin_im442 N t
    have hnorm : ‖(mellinLine1622 N t) + 1‖ ≤ 3 + |t| := by
      have h := Complex.norm_le_abs_re_add_abs_im ((mellinLine1622 N t) + 1)
      have hre' : ((mellinLine1622 N t) + 1).re = 1 / 2 + 1 / Real.log N + 1 := by
        rw [Complex.add_re, mellin_re442]; norm_num
      have him' : ((mellinLine1622 N t) + 1).im = t := by
        rw [Complex.add_im, mellin_im442]; norm_num
      rw [hre', him'] at h
      have hpos : (0 : ℝ) ≤ 1 / 2 + 1 / Real.log N + 1 := by positivity
      rw [abs_of_nonneg hpos] at h
      have hle : 1 / 2 + 1 / Real.log N + 1 ≤ 3 := by linarith [inv_log_le_one442 N hN]
      linarith
    have hpl := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL h1 h2
    rw [hsi] at hpl
    refine hpl.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  -- the uniform bound of `Γ` on the strip
  have hC : ‖Complex.Gamma (mellinLine1622 N t)‖ ≤
      Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
    have h1 : (1 : ℝ) / 2 ≤ (mellinLine1622 N t).re := by
      rw [mellin_re442]; linarith [hloginv]
    have h2 : (mellinLine1622 N t).re ≤ 3 / 2 := by
      rw [mellin_re442]; linarith [inv_log_le_one442 N hN]
    exact LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le h1 h2
  rcases lt_or_ge t 0 with ht | ht
  · have habs : |t| = -t := abs_of_neg ht
    have hexp : Real.exp (t * z.arg) ≤ Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
      rw [habs]
      apply Real.exp_le_exp.mpr
      have hmono : t * z.arg ≤ t * (1 / (100 * (N : ℝ))) :=
        mul_le_mul_of_nonpos_left harglow ht.le
      linarith
    calc ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖
        ≤ ‖z ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) * Real.exp (t * z.arg)) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) := by
          apply mul_le_mul hcpow hC (norm_nonneg _) (by positivity)
      _ ≤ ((N : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|)) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) := by gcongr
      _ ≤ ((N : ℝ) ^ (3 / 2 : ℝ) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
          (1 + |t|) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
          have hCpos : (0 : ℝ) ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) := by
            have h1 : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
            have h2 : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
            linarith
          have hN32 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hNr.le _
          have hb : (N : ℝ) ^ (3 / 2 : ℝ) * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2)) ≤
              ((N : ℝ) ^ (3 / 2 : ℝ) *
                (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) * (1 + |t|) := by
            calc (N : ℝ) ^ (3 / 2 : ℝ) * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))
                ≤ (N : ℝ) ^ (3 / 2 : ℝ) *
                    (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) := by
                  apply mul_le_mul_of_nonneg_left _ hN32
                  nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
              _ ≤ ((N : ℝ) ^ (3 / 2 : ℝ) *
                    (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
                    (1 + |t|) := by
                  have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
                  calc (N : ℝ) ^ (3 / 2 : ℝ) *
                        (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))
                      = ((N : ℝ) ^ (3 / 2 : ℝ) *
                          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) * 1 := by
                          ring
                    _ ≤ ((N : ℝ) ^ (3 / 2 : ℝ) *
                          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
                          (1 + |t|) := by
                          apply mul_le_mul_of_nonneg_left h1 (by positivity)
          calc ((N : ℝ) ^ (3 / 2 : ℝ) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|)) *
                (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))
              = ((N : ℝ) ^ (3 / 2 : ℝ) * (Real.Gamma (1 / 2) + Real.Gamma (3 / 2))) *
                  Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by ring
            _ ≤ (((N : ℝ) ^ (3 / 2 : ℝ) *
                  (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
                  (1 + |t|)) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by gcongr
            _ = _ := by ring
  · have habs : |t| = t := abs_of_nonneg ht
    have hexp : Real.exp (t * z.arg) * Real.exp (-(Real.pi * t / 2)) ≤
        Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
      rw [← Real.exp_add, habs]
      apply Real.exp_le_exp.mpr
      have hle : t * z.arg ≤ t * (Real.pi / 2 - 1 / (100 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hargup ht
      nlinarith
    calc ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖
        ≤ ‖z ^ (-(mellinLine1622 N t))‖ * ‖Complex.Gamma (mellinLine1622 N t)‖ := norm_mul_le _ _
      _ ≤ (‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) * Real.exp (t * z.arg)) *
            (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * t / 2))) := by
          apply mul_le_mul hcpow hPL (norm_nonneg _) (by positivity)
      _ = ‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) * Real.sqrt (2 * Real.pi) * (3 + |t|) *
            (Real.exp (t * z.arg) * Real.exp (-(Real.pi * t / 2))) := by ring
      _ ≤ ‖z‖ ^ (-(1 / 2 + 1 / Real.log N)) * Real.sqrt (2 * Real.pi) * (3 + |t|) *
            Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
      _ ≤ ((N : ℝ) ^ (3 / 2 : ℝ) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
          (1 + |t|) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|) :=
          step_bound442 N t (Real.exp (-(1 / (100 * (N : ℝ))) * |t|))
            (‖z‖ ^ (-(1 / 2 + 1 / Real.log N))) hA (by positivity)

/-- The base is bounded in modulus as soon as the frequency is at most two. -/
private lemma base_norm_le_two442 (N : ℕ) (hN1 : 1 ≤ N) {α : ℝ} (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 + 4 * Real.pi := by
  have h1 : 2 * Real.pi * α ≤ 4 * Real.pi := by nlinarith [Real.pi_pos]
  have h2 := Complex.norm_le_abs_re_add_abs_im
    (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)
  rw [base_re442, base_im442, abs_of_nonneg (by positivity),
    abs_of_nonneg (by nlinarith [Real.pi_pos])] at h2
  have h3 : (1 / (N : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hN1
  linarith

/-- The minimum of the two interval endpoints is positive and supplies the uniform
argument gap of the kernel bound. -/
private lemma c_bounds442 (N : ℕ) (hN : 3 ≤ N) {R : ℝ} (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    0 < min (4 / (N : ℝ)) (1 / R) ∧
      1 / (100 * (N : ℝ)) ≤
        2 * Real.pi * min (4 / (N : ℝ)) (1 / R) / (1 + 4 * Real.pi) := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hpow : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) := by
    calc (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hR2N : R ≤ 2 * (N : ℝ) := by linarith
  have hhalf : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  have hcge : 1 / (2 * (N : ℝ)) ≤ min (4 / (N : ℝ)) (1 / R) := by
    refine le_min ?_ ?_
    · rw [div_le_div_iff₀ (by positivity) hNr]
      nlinarith
    · rw [div_le_div_iff₀ (by positivity) hRpos]
      nlinarith
  refine ⟨lt_of_lt_of_le hhalf hcge, ?_⟩
  have key : 1 / (100 * (N : ℝ)) * (1 + 4 * Real.pi) ≤ 2 * Real.pi * (1 / (2 * (N : ℝ))) := by
    have h1 : 1 / (100 * (N : ℝ)) * (1 + 4 * Real.pi) = (1 + 4 * Real.pi) / (100 * (N : ℝ)) := by
      ring
    have h2 : 2 * Real.pi * (1 / (2 * (N : ℝ))) = Real.pi / (N : ℝ) := by
      field_simp
    rw [h1, h2, div_le_div_iff₀ (by positivity) hNr]
    nlinarith [Real.pi_gt_three]
  have hmono : 2 * Real.pi * (1 / (2 * (N : ℝ))) ≤
      2 * Real.pi * min (4 / (N : ℝ)) (1 / R) :=
    mul_le_mul_of_nonneg_left hcge (by positivity)
  have hden : (0 : ℝ) < 1 + 4 * Real.pi := by nlinarith [Real.pi_pos]
  rw [le_div_iff₀ hden]
  linarith

/-- At every frequency of the outer interval the log weighted Mellin kernel mass is
bounded by the integral of the dominating exponential. -/
private lemma mass_le_dominant442 (N : ℕ) (hN : 3 ≤ N) {R α : ℝ} (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ))
    (hα : α ∈ Set.uIoc (4 / (N : ℝ)) (1 / R)) :
    (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
      ∫ t : ℝ,
        ((N : ℝ) ^ (3 / 2 : ℝ) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
          (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
            Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  obtain ⟨hminpos, hc200⟩ := c_bounds442 N hN hR hR2
  have hαlo : min (4 / (N : ℝ)) (1 / R) ≤ α := le_of_lt hα.1
  have hαhi : α ≤ max (4 / (N : ℝ)) (1 / R) := hα.2
  have hα2 : α ≤ 2 := by
    refine le_trans hαhi (max_le ?_ ?_)
    · rw [div_le_iff₀ hNr]
      linarith
    · rw [div_le_iff₀ hRpos]
      linarith
  have hα0 : 0 ≤ α := le_trans hminpos.le hαlo
  have hnormz : ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 + 4 * Real.pi := base_norm_le_two442 N (by omega) hα0 hα2
  have hz0 : (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hre := base_re442 N α
    rw [h] at hre
    simp at hre
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have him' : 2 * Real.pi * min (4 / (N : ℝ)) (1 / R) ≤
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).im := by
    rw [base_im442]
    nlinarith [Real.pi_pos]
  have him0 : 0 ≤ (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).im :=
    le_trans (by positivity : (0 : ℝ) ≤ 2 * Real.pi * min (4 / (N : ℝ)) (1 / R)) him'
  have harglow : 1 / (100 * (N : ℝ)) ≤
      (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).arg :=
    arg_lower442 N hminpos.le him' hnormz hz0 hc200
  have hargup : (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I).arg
      ≤ Real.pi / 2 - 1 / (100 * (N : ℝ)) :=
    (base_arg_bounds442 N hN (base_re442 N α) him0 hnormz).2
  have hlog0 : ∀ t : ℝ, (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    intro t
    apply pow_nonneg
    apply Real.log_nonneg
    have h2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h3 : (1 : ℝ) * 1 ≤ (N : ℝ) * (|t| + 2) :=
      mul_le_mul hN1 h2 zero_le_one (by linarith)
    linarith
  have hpt : ∀ t : ℝ,
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
        ((N : ℝ) ^ (3 / 2 : ℝ) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
          (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
            Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by
    intro t
    have hkb := kernel_bound_arg442 N hN (z := (((1 / (N : ℝ) : ℝ) : ℂ) +
      ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I)) (base_re442 N α) him0 hnormz harglow hargup t
    calc ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3
        ≤ (((N : ℝ) ^ (3 / 2 : ℝ) *
              (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
            (1 + |t|) * Real.exp (-(1 / (100 * (N : ℝ))) * |t|)) *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3 :=
          mul_le_mul_of_nonneg_right hkb (hlog0 t)
      _ = ((N : ℝ) ^ (3 / 2 : ℝ) *
              (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
            (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
              Real.exp (-(1 / (100 * (N : ℝ))) * |t|) := by ring
  have hK0 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) *
      (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hNr.le _
    have h2 : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h4 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi) := by
      linarith
    exact mul_nonneg h1 h5
  have hGint : Integrable (fun t : ℝ =>
      ((N : ℝ) ^ (3 / 2 : ℝ) *
          (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
        (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
          Real.exp (-(1 / (100 * (N : ℝ))) * |t|)) := by
    have h := integrable_dominant442 N hN
      ((N : ℝ) ^ (3 / 2 : ℝ) *
        (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)))
      (1 / (100 * (N : ℝ))) hK0 (by positivity)
    simpa using h
  exact integral_mono_of_nonneg (ae_of_all _ (fun t => mul_nonneg (norm_nonneg _) (hlog0 t)))
    hGint (ae_of_all _ hpt)

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
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) *
      (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi)) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hNr.le _
    have h2 : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h4 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi) := by
      linarith
    exact mul_nonneg h1 h5
  have hδ0 : (0 : ℝ) < 1 / (100 * (N : ℝ)) := by positivity
  have hFsm : StronglyMeasurable (fun p : ℝ × ℝ =>
      ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * p.1 : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N p.2)) * Complex.Gamma (mellinLine1622 N p.2)‖ *
          Real.log ((N : ℝ) * (|p.2| + 2)) ^ 3) :=
    (integrand_cont_pair442 N hN).stronglyMeasurable
  have hmass_sm : StronglyMeasurable (fun α : ℝ =>
      ∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
    hFsm.integral_prod_right' (ν := volume)
  have hmass2 : StronglyMeasurable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) := hmass_sm.pow 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog0 : ∀ t : ℝ, (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
    intro t
    apply pow_nonneg
    apply Real.log_nonneg
    have h2 : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    have h3 : (1 : ℝ) * 1 ≤ (N : ℝ) * (|t| + 2) :=
      mul_le_mul hN1 h2 zero_le_one (by linarith)
    linarith
  have hkey : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.uIoc (4 / (N : ℝ)) (1 / R) →
      volume s < ⊤ →
      IntegrableOn (fun α : ℝ =>
        (∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) s volume := by
    intro s hs hsub hfin
    refine IntegrableOn.of_bound hfin (hmass2.aestronglyMeasurable.restrict)
      ((∫ t : ℝ,
        ((N : ℝ) ^ (3 / 2 : ℝ) *
            (Real.Gamma (1 / 2) + Real.Gamma (3 / 2) + 4 * Real.sqrt (2 * Real.pi))) *
          (1 + |t|) * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 *
            Real.exp (-(1 / (100 * (N : ℝ))) * |t|)) ^ 2) ?_
    filter_upwards [ae_restrict_mem hs] with α hα
    have hle := mass_le_dominant442 N hN hR hR2 (hsub hα)
    have hnn : (0 : ℝ) ≤
        ∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      refine integral_nonneg (fun t => ?_)
      exact mul_nonneg (norm_nonneg _) (hlog0 t)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnn 2)]
    exact pow_le_pow_left₀ hnn hle 2
  exact ⟨hkey _ measurableSet_Ioc Set.Ioc_subset_uIoc measure_Ioc_lt_top,
    hkey _ measurableSet_Ioc Set.Ioc_subset_uIoc' measure_Ioc_lt_top⟩

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
