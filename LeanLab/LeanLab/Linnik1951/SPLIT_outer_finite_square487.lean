/-
Unit Linnik1951/SPLIT-outer_finite_square487.
Split of outer_finite_square487 of Decomp487b into the square-to-kernel reduction,
the region split of the frequency square at the sign of t + u, and the two region estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp487b
import LeanLab.Linnik1951.Repair493PositiveKernel

namespace LeanLab.Linnik1951

open MeasureTheory

set_option maxHeartbeats 1600000

/-- The Mellin kernel is continuous in the pair (alpha, t). -/
private theorem continuous_mellinKernel487 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let Z : ℝ → ℂ := fun α => ((1 / (N : ℝ) : ℝ) : ℂ) +
    ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hZ : Continuous Z := by dsimp [Z]; fun_prop
  have hline : Continuous (fun t : ℝ => mellinLine1622 N t) := by
    dsimp [mellinLine1622]; fun_prop
  have hGamma : Continuous (fun t : ℝ => Complex.Gamma (mellinLine1622 N t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp hline.continuousAt
    intro m hm
    have hh := congrArg Complex.re hm
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hh
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlog0 : (0 : ℝ) ≤ 1 / Real.log (N : ℝ) :=
      div_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)))
    linarith
  have hslit (p : ℝ × ℝ) : Z p.1 ∈ Complex.slitPlane := by
    refine Or.inl ?_
    have hre : (Z p.1).re = 1 / (N : ℝ) := by
      simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hre]
    exact div_pos one_pos hNpos
  exact ((hZ.comp continuous_fst).cpow (hline.comp continuous_snd).neg hslit).mul
    (hGamma.comp continuous_snd)

/-- The alpha integral of the kernel product is continuous in the frequency pair. -/
private theorem continuous_alphaKernel_integral487 (N : ℕ) (hN : 1 ≤ N) (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ α in a..b,
      mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)) := by
  let f : (ℝ × ℝ) → ℝ → ℂ := fun p α =>
    mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)
  have h := continuous_mellinKernel487 N hN
  have hu : Continuous (Function.uncurry f) := by
    change Continuous (fun q : (ℝ × ℝ) × ℝ =>
      mellinKernel442 N q.2 q.1.1 * (starRingEnd ℂ) (mellinKernel442 N q.2 q.1.2))
    exact (h.comp (continuous_snd.prodMk continuous_fst.fst)).mul
      (h.comp (continuous_snd.prodMk continuous_fst.snd)).star
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := f) (μ := volume) hu a b
  exact hc

/-- An iterated interval integral over a square is the set integral over the product box. -/
private theorem iterated_eq_box487 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → ℝ → E) (a b : ℝ)
    (hF : IntegrableOn (Function.uncurry F) (Set.uIoc a b ×ˢ Set.uIoc a b)) :
    (∫ t in a..b, ∫ u in a..b, F t u) =
      ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
  rcases le_total a b with h | h
  · rw [Set.uIoc_of_le h] at hF
    calc (∫ t in a..b, ∫ u in a..b, F t u)
        = ∫ t in Set.Ioc a b, ∫ u in Set.Ioc a b, F t u := by
          simp_rw [intervalIntegral.integral_of_le h]
      _ = ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
          rw [Set.uIoc_of_le h]
          exact (setIntegral_prod (fun z : ℝ × ℝ => F z.1 z.2) hF).symm
  · rw [Set.uIoc_of_ge h] at hF
    calc (∫ t in a..b, ∫ u in a..b, F t u)
        = ∫ t in a..b, (-∫ u in Set.Ioc b a, F t u) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact intervalIntegral.integral_of_ge h
      _ = -∫ t in a..b, (∫ u in Set.Ioc b a, F t u) :=
          intervalIntegral.integral_neg
      _ = -(-∫ t in Set.Ioc b a, (∫ u in Set.Ioc b a, F t u)) := by
          rw [intervalIntegral.integral_of_ge h]
      _ = ∫ t in Set.Ioc b a, ∫ u in Set.Ioc b a, F t u := by rw [neg_neg]
      _ = ∫ z in (Set.uIoc a b ×ˢ Set.uIoc a b), F z.1 z.2 := by
          rw [Set.uIoc_of_ge h]
          exact (setIntegral_prod (fun z : ℝ × ℝ => F z.1 z.2) hF).symm

/-- Split a double interval integral over a square at the sign of the sum of the variables. -/
private theorem region_split_aux487 (T : ℝ) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (Function.uncurry G)) :
    (∫ t in -T..T, ∫ u in -T..T, G t u) =
      (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then G t u else 0) +
      (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else G t u) := by
  set S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 + p.2} with hS
  have hSmeas : MeasurableSet S := by
    rw [hS]
    exact measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  have hBmeas : MeasurableSet (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    measurableSet_uIoc.prod measurableSet_uIoc
  have hGmeas : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := hG.measurable
  have hGint : IntegrableOn (Function.uncurry G) (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    (hG.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hGint' : Integrable (Function.uncurry G)
      (volume.restrict (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)) := hGint
  have hind1 : IntegrableOn (S.indicator (Function.uncurry G))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    refine Integrable.mono' hGint'.norm (hGmeas.indicator hSmeas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => norm_indicator_le_norm_self _ p)
  have hind2 : IntegrableOn (Sᶜ.indicator (Function.uncurry G))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    refine Integrable.mono' hGint'.norm (hGmeas.indicator hSmeas.compl).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => norm_indicator_le_norm_self _ p)
  have hfun1 : (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then G p.1 p.2 else 0) =
      S.indicator (Function.uncurry G) := by
    funext p
    by_cases h : 0 ≤ p.1 + p.2
    · rw [if_pos h, Set.indicator_of_mem (f := Function.uncurry G)
        (show p ∈ S from by simpa [hS] using h)]
      rfl
    · rw [if_neg h, Set.indicator_of_notMem (f := Function.uncurry G)
        (show p ∉ S from by simpa [hS] using h)]
  have hfun2 : (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then 0 else G p.1 p.2) =
      Sᶜ.indicator (Function.uncurry G) := by
    funext p
    by_cases h : 0 ≤ p.1 + p.2
    · rw [if_pos h, Set.indicator_of_notMem (f := Function.uncurry G)
        (show p ∉ Sᶜ from fun hp => hp (show p ∈ S from by simpa [hS] using h))]
    · rw [if_neg h, Set.indicator_of_mem (f := Function.uncurry G)
        (show p ∈ Sᶜ from by simpa [hS] using h)]
      rfl
  have hp1 : IntegrableOn (Function.uncurry (fun t u => if 0 ≤ t + u then G t u else 0))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have he : Function.uncurry (fun t u => if 0 ≤ t + u then G t u else 0)
        = (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then G p.1 p.2 else 0) := rfl
    rw [he, hfun1]
    exact hind1
  have hp2 : IntegrableOn (Function.uncurry (fun t u => if 0 ≤ t + u then 0 else G t u))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have he : Function.uncurry (fun t u => if 0 ≤ t + u then 0 else G t u)
        = (fun p : ℝ × ℝ => if 0 ≤ p.1 + p.2 then 0 else G p.1 p.2) := rfl
    rw [he, hfun2]
    exact hind2
  have hpiece1 : (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then G t u else 0) =
      ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        S.indicator (Function.uncurry G) z := by
    rw [iterated_eq_box487 (fun t u => if 0 ≤ t + u then G t u else 0) (-T) T hp1, hfun1]
  have hpiece2 : (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else G t u) =
      ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        Sᶜ.indicator (Function.uncurry G) z := by
    rw [iterated_eq_box487 (fun t u => if 0 ≤ t + u then 0 else G t u) (-T) T hp2, hfun2]
  have hBsplit : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), Function.uncurry G z) =
      (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), S.indicator (Function.uncurry G) z) +
      (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T),
        Sᶜ.indicator (Function.uncurry G) z) := by
    have hdisj : Disjoint ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ S)
        ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ Sᶜ) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have hun : ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ S) ∪
        ((Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) ∩ Sᶜ) =
        Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    have key := setIntegral_union (μ := volume) hdisj (hBmeas.inter hSmeas.compl)
      (hGint.mono_set Set.inter_subset_left) (hGint.mono_set Set.inter_subset_left)
    rw [hun] at key
    rw [key, setIntegral_indicator (s := Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)
        (f := Function.uncurry G) hSmeas,
      setIntegral_indicator (s := Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T)
        (f := Function.uncurry G) hSmeas.compl]
  have hboxG : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), Function.uncurry G z) =
      (∫ t in -T..T, ∫ u in -T..T, G t u) :=
    (iterated_eq_box487 G (-T) T hGint).symm
  rw [← hboxG, hBsplit, ← hpiece1, ← hpiece2]

/-- Sharp modulus of one power factor of the Mellin kernel. -/
private theorem norm_cpow_mellin487 (N : ℕ) (hN : 3 ≤ N) {z : ℂ} (hz : z ≠ 0)
    (t : ℝ) :
    ‖z ^ (-(mellinLine1622 N t))‖ =
      ‖z‖ ^ (-(1 / 2 + 1 / Real.log (N : ℝ))) * Real.exp (t * z.arg) := by
  have hlog : Complex.log z = (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im]
  have hre : (Complex.log z * (-(mellinLine1622 N t))).re =
      -((1 / 2 + 1 / Real.log (N : ℝ)) * Real.log ‖z‖) + t * z.arg := by
    rw [hlog]
    simp only [mellinLine1622, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
      sub_zero, zero_add]
    ring
  have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  calc ‖z ^ (-(mellinLine1622 N t))‖
      = Real.exp ((Complex.log z * (-(mellinLine1622 N t))).re) := by
        rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp]
    _ = Real.exp (-((1 / 2 + 1 / Real.log (N : ℝ)) * Real.log ‖z‖)) *
          Real.exp (t * z.arg) := by
        rw [hre, Real.exp_add]
    _ = ‖z‖ ^ (-(1 / 2 + 1 / Real.log (N : ℝ))) * Real.exp (t * z.arg) := by
        rw [Real.rpow_def_of_pos hpos]
        congr 1
        ring

/-- The pair of conjugate power factors at two frequencies, with the sum exponent. -/
private theorem norm_cpow_pair487 (N : ℕ) (hN : 3 ≤ N) {z : ℂ} (hz : z ≠ 0)
    (hzre : z.re = 1 / (N : ℝ)) (t u : ℝ) :
    ‖z ^ (-(mellinLine1622 N t)) * (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ ≤
      Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set σ : ℝ := 1 / 2 + 1 / Real.log (N : ℝ) with hσ
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hnt : ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ := by
    have hznorm : (1 / (N : ℝ)) ≤ ‖z‖ := by
      have h1 := Complex.abs_re_le_norm z
      rw [hzre] at h1
      rwa [abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))] at h1
    have hstep := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 / (N : ℝ)) hznorm
      (show -σ ≤ 0 from by linarith)
    have hbase : ((1 : ℝ) / (N : ℝ)) ^ (-σ) = (N : ℝ) ^ σ := by
      rw [one_div, Real.inv_rpow hNpos.le, ← Real.rpow_neg]
      · ring_nf
      · exact hNpos.le
    rwa [hbase] at hstep
  have hNpow : (N : ℝ) ^ σ = Real.exp 1 * Real.sqrt N := by
    have hadd : (N : ℝ) ^ σ =
        (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / Real.log (N : ℝ)) := by
      rw [hσ, Real.rpow_add hNpos]
    rw [hadd, ← Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos,
      show Real.log (N : ℝ) * (1 / Real.log (N : ℝ)) = 1 from by field_simp]
    ring
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have e1 := norm_cpow_mellin487 N hN hz t
  have e2 := norm_cpow_mellin487 N hN hz u
  rw [norm_mul, Complex.norm_conj, e1, e2]
  change ‖z‖ ^ (-σ) * Real.exp (t * z.arg) *
      (‖z‖ ^ (-σ) * Real.exp (u * z.arg)) ≤
    Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg)
  have hprod : (‖z‖ ^ (-σ) * Real.exp (t * z.arg)) *
      (‖z‖ ^ (-σ) * Real.exp (u * z.arg)) =
      (‖z‖ ^ (-σ) * ‖z‖ ^ (-σ)) * (Real.exp (t * z.arg) * Real.exp (u * z.arg)) := by
    ring
  rw [hprod]
  have hmono : ‖z‖ ^ (-σ) * ‖z‖ ^ (-σ) ≤ (N : ℝ) ^ σ * (N : ℝ) ^ σ :=
    mul_le_mul hnt hnt (Real.rpow_nonneg (norm_nonneg z) _) (Real.rpow_nonneg hNpos.le _)
  have hexpadd : Real.exp (t * z.arg) * Real.exp (u * z.arg) =
      Real.exp ((t + u) * z.arg) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpadd]
  refine le_trans (mul_le_mul hmono le_rfl (Real.exp_pos _).le (by positivity)) ?_
  rw [hexp2, hNpow]
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
    rw [← sq, Real.sq_sqrt hNpos.le]
  have hstep : Real.exp 1 * Real.sqrt (N : ℝ) * (Real.exp 1 * Real.sqrt (N : ℝ)) *
        Real.exp ((t + u) * z.arg) =
      Real.exp 1 * Real.exp 1 * (N : ℝ) * Real.exp ((t + u) * z.arg) := by
    rw [show Real.exp 1 * Real.sqrt (N : ℝ) * (Real.exp 1 * Real.sqrt (N : ℝ))
        = Real.exp 1 * Real.exp 1 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) from by ring, hsq]
  exact le_of_eq hstep

-- END LEAF 5 HELPERS

/-! ### Leaf 5: a lower bound for the sum kernel (a strip of width 1 along the anti-diagonal) -/

/-- On the frequency square of radius `T` the exponentially decreasing sum kernel is at least
a constant times `T`: the strip `0 ≤ t ≤ T - 1`, `-t ≤ u ≤ -t + 1` has measure `T - 1` and
there `|t + u| ≤ 1`, so the integrand is bounded below by `exp (-(π/4))`. -/
private theorem sumKernel_lower487 (T : ℝ) (hT : 2 ≤ T) :
    Real.exp (-(Real.pi / 4)) * (T / 2) ≤ sumKernel376 T := by
  set F : ℝ → ℝ → ℝ := fun t u => Real.exp (-(Real.pi / 4) * |t + u|) with hF
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 4)) := Real.exp_pos _
  have hFcurry : Function.uncurry F =
      fun p : ℝ × ℝ => Real.exp (-(Real.pi / 4) * |p.1 + p.2|) := by
    funext p
    rfl
  have hFcont : Continuous (Function.uncurry F) := by
    rw [hFcurry]
    fun_prop
  have hFt (t : ℝ) : Continuous fun u : ℝ => F t u := by
    have h : (fun u : ℝ => F t u) = fun u => Real.exp (-(Real.pi / 4) * |t + u|) := by
      funext u
      simp only [hF]
    rw [h]
    fun_prop
  -- the inner integral from `-T` to `T` dominates the constant on the strip
  have hinner : ∀ t ∈ Set.Icc (0 : ℝ) (T - 1),
      Real.exp (-(Real.pi / 4)) ≤ ∫ u in -T..T, F t u := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have htT : t ≤ T - 1 := ht.2
    have hconst : (∫ u in (-t)..(-t + 1), Real.exp (-(Real.pi / 4))) =
        Real.exp (-(Real.pi / 4)) := by
      simp
    have hstep2 : (∫ u in (-t)..(-t + 1), Real.exp (-(Real.pi / 4))) ≤
        ∫ u in (-t)..(-t + 1), F t u := by
      apply intervalIntegral.integral_mono_on (by linarith : (-t : ℝ) ≤ -t + 1)
      · exact intervalIntegrable_const
      · exact (hFt t).intervalIntegrable _ _
      · intro u hu
        have hu1 : -t ≤ u := hu.1
        have hu2 : u ≤ -t + 1 := hu.2
        have habs : |t + u| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        refine Real.exp_le_exp.mpr ?_
        nlinarith [Real.pi_pos, abs_nonneg (t + u), habs]
    have hstep3 : (∫ u in (-t)..(-t + 1), F t u) ≤ ∫ u in -T..T, F t u := by
      apply intervalIntegral.integral_mono_interval (c := -T) (d := T)
      · linarith
      · linarith
      · linarith
      · exact Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
      · exact (hFt t).intervalIntegrable _ _
    rw [hconst] at hstep2
    exact hstep2.trans hstep3
  -- restrict the outer integral to the same range of `t`
  have houter : (∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4))) ≤
      ∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u := by
    apply intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ T - 1)
    · exact intervalIntegrable_const
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := F) (μ := volume) hFcont (-T) T).intervalIntegrable _ _
    · intro t ht
      exact hinner t ⟨ht.1, ht.2⟩
  have houter2 : (∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u) ≤
      ∫ t in -T..T, ∫ u in -T..T, F t u := by
    apply intervalIntegral.integral_mono_interval (c := -T) (d := T)
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall (fun t =>
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => (Real.exp_pos _).le))
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := F) (μ := volume) hFcont (-T) T).intervalIntegrable _ _
  have hval : (∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4))) =
      Real.exp (-(Real.pi / 4)) * (T - 1) := by
    simp [mul_comm]
  have hhalf : T / 2 ≤ T - 1 := by linarith
  calc Real.exp (-(Real.pi / 4)) * (T / 2)
      ≤ Real.exp (-(Real.pi / 4)) * (T - 1) := mul_le_mul_of_nonneg_left hhalf hc.le
    _ = ∫ t in (0 : ℝ)..(T - 1), Real.exp (-(Real.pi / 4)) := hval.symm
    _ ≤ ∫ t in (0 : ℝ)..(T - 1), ∫ u in -T..T, F t u := houter
    _ ≤ ∫ t in -T..T, ∫ u in -T..T, F t u := houter2
    _ = sumKernel376 T := by rw [hF]; simp only [sumKernel376]

-- END LEAF 5 LOWER

/-! ### Leaf 5: the exponential frequency weight is uniformly bounded on the square -/

/-- The linear weight is absorbed by the exponential decay: `3 + |s| ≤ 4 exp ((π/4)|s|)`. -/
private theorem exp_weight_le487 (s : ℝ) :
    (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|) ≤ 4 * Real.exp (-(Real.pi / 4) * |s|) := by
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |s|) := Real.exp_pos _
  have hs : (0 : ℝ) ≤ |s| := abs_nonneg s
  have hlin : 3 + |s| ≤ 4 * Real.exp ((Real.pi / 4) * |s|) := by
    have h1 : (Real.pi / 4) * |s| + 1 ≤ Real.exp ((Real.pi / 4) * |s|) := Real.add_one_le_exp _
    nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hlin hc.le
  refine hmul.trans_eq ?_
  rw [mul_assoc, ← Real.exp_add,
    show (Real.pi / 4) * |s| + -(Real.pi / 2) * |s| = -(Real.pi / 4) * |s| from by ring]

/-- Pointwise in `alpha`: on the negative region `t + u ≤ 0` the kernel pair is bounded by
`exp 2 · N` times the two Gamma weights. The angular factor is `≤ 1` because `arg z ≥ 0`. -/
private theorem kernel_pair_pointwise487 (N : ℕ) (hN : 3 ≤ N) {α : ℝ} (hα : 0 ≤ α)
    (t u : ℝ) (htu : t + u ≤ 0) :
    ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
      (Real.exp 2 * (N : ℝ)) *
        ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
         (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) := by
  set z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I with hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hzre : z.re = 1 / (N : ℝ) := by simp [hz]
  have hzim : z.im = 2 * Real.pi * α := by simp [hz]
  have hzpos : 0 < z.re := by rw [hzre]; positivity
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hzpos
    simp at hzpos
  have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [hzim]; positivity)
  have hpow := norm_cpow_pair487 N hN hzne hzre t u
  have hexp : Real.exp ((t + u) * z.arg) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [harg, htu]
  have hker : ∀ s : ℝ, mellinKernel442 N α s =
      z ^ (-(mellinLine1622 N s)) * Complex.Gamma (mellinLine1622 N s) := by
    intro s
    rfl
  have hgamma_t := gamma_mellin_line442 N hN t
  have hgamma_u := gamma_mellin_line442 N hN u
  have h1 : ‖z ^ (-(mellinLine1622 N t)) *
      (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ ≤ Real.exp 2 * (N : ℝ) := by
    refine hpow.trans ?_
    calc Real.exp 2 * (N : ℝ) * Real.exp ((t + u) * z.arg)
        ≤ Real.exp 2 * (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 2 * (N : ℝ) := by ring
  have hAB : ‖Complex.Gamma (mellinLine1622 N t)‖ *
      ‖Complex.Gamma (mellinLine1622 N u)‖ ≤
      (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
        (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))) :=
    mul_le_mul hgamma_t hgamma_u (norm_nonneg _) (by positivity)
  calc ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
      = ‖z ^ (-(mellinLine1622 N t)) *
            (starRingEnd ℂ) (z ^ (-(mellinLine1622 N u)))‖ *
          (‖Complex.Gamma (mellinLine1622 N t)‖ *
            ‖Complex.Gamma (mellinLine1622 N u)‖) := by
        rw [hker t, hker u, map_mul]
        simp only [norm_mul, Complex.norm_conj]
        ring
    _ ≤ (Real.exp 2 * (N : ℝ)) *
          ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
           (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) :=
        mul_le_mul h1 hAB (by positivity) (by positivity)

/-- The `alpha` integral of the kernel pair on the outer range, on the negative region. -/
private theorem kernel_pair_integral487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hRN : 4 * R ≤ (N : ℝ)) (t u : ℝ) (htu : t + u ≤ 0) :
    ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤
      (1 / R) * ((Real.exp 2 * (N : ℝ)) *
        ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
         (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hN1 : 1 ≤ N := by omega
  set C : ℝ := (Real.exp 2 * (N : ℝ)) *
      ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
       (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) with hC
  have hCnonneg : (0 : ℝ) ≤ C := by rw [hC]; positivity
  have hab : 4 / (N : ℝ) ≤ 1 / R := by
    rw [div_le_div_iff₀ hNpos hRpos]
    linarith
  have hker := continuous_mellinKernel487 N hN1
  have hcont : Continuous fun α : ℝ =>
      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u) := by
    have h1 : Continuous fun α : ℝ => mellinKernel442 N α t :=
      hker.comp (continuous_id.prodMk continuous_const)
    have h2 : Continuous fun α : ℝ => mellinKernel442 N α u :=
      hker.comp (continuous_id.prodMk continuous_const)
    exact h1.mul h2.star
  have hpt : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ ≤ C := by
    intro α hα
    have hα0 : 0 ≤ α := by
      have : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
      linarith [hα.1]
    exact kernel_pair_pointwise487 N hN hα0 t u htu
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun α : ℝ => mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)) hab
  have hmono : (∫ α in (4 / (N : ℝ))..(1 / R),
        ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
      ∫ α in (4 / (N : ℝ))..(1 / R), C := by
    apply intervalIntegral.integral_mono_on hab
    · exact hcont.norm.intervalIntegrable _ _
    · exact intervalIntegrable_const (c := C)
    · intro α hα
      exact hpt α hα
  have hval : (∫ α in (4 / (N : ℝ))..(1 / R), C) = C * (1 / R - 4 / (N : ℝ)) := by
    simp [mul_comm]
  have hdiff : 1 / R - 4 / (N : ℝ) ≤ 1 / R := by
    have : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
    linarith
  calc ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
      ≤ (∫ α in (4 / (N : ℝ))..(1 / R),
        ‖mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) := hnorm
    _ ≤ ∫ α in (4 / (N : ℝ))..(1 / R), C := hmono
    _ = C * (1 / R - 4 / (N : ℝ)) := hval
    _ ≤ C * (1 / R) := mul_le_mul_of_nonneg_left hdiff hCnonneg
    _ = (1 / R) * C := by ring

-- END LEAF 5 PAIR

/-- The line bound with the logarithm of the frequency replaced by a polynomial weight:
`‖M t‖ ≤ B0 (8 log³N + 8 (3 + |t|)³)` for `N ≥ 2`. This is what lets the exponential decay of the
Gamma factor absorb the coefficient weight on the negative region. -/
private theorem mellin_weight_le487 (N : ℕ) (hN : 2 ≤ N) (B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (t : ℝ) :
    ‖M t‖ ≤ B0 * (8 * Real.log N ^ 3 + 8 * (3 + |t|) ^ 3) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsplit := log_cube_split442 N t hN
  -- the logarithm of the frequency is dominated by the linear weight
  have h3 : Real.log (|t| + 2) ≤ 3 + |t| := by
    have hpos : (0 : ℝ) < |t| + 2 := by positivity
    have hle : Real.log (|t| + 2) ≤ |t| + 2 - 1 := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hcube : Real.log (|t| + 2) ^ 3 ≤ (3 + |t|) ^ 3 := by
    have h3' : (0 : ℝ) ≤ 3 + |t| := by linarith [abs_nonneg t]
    exact pow_le_pow_left₀ hlog0 h3 3
  have hbound : Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * (3 + |t|) ^ 3 := by
    refine hsplit.trans ?_
    have : 8 * Real.log (|t| + 2) ^ 3 ≤ 8 * (3 + |t|) ^ 3 := by linarith
    linarith
  exact (hM.2 t).trans (mul_le_mul_of_nonneg_left hbound hB0)

-- END LEAF 5 COEFF

/-- A polynomial weight of degree four is dominated by half of the exponential decay. -/
private theorem poly_le_exp487 (s : ℝ) :
    (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|) ≤
      4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
  have hs : (0 : ℝ) ≤ |s| := abs_nonneg s
  -- (1 + |s|) ^ 4 ≤ 384 e · exp (|s| / 2)
  have h1 : (1 + |s|) ^ 4 ≤ 384 * (Real.exp 1 * Real.exp (|s| / 2)) := by
    set u : ℝ := |s| / 2 + 1 with hu
    have hu1 : (1 : ℝ) ≤ u := by rw [hu]; linarith
    have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu1
    have hpow : u ^ 4 / ((Nat.factorial 4 : ℕ) : ℝ) ≤ Real.exp u :=
      Real.pow_div_factorial_le_exp (x := u) hu0 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
    rw [hfac] at hpow
    have h4 : u ^ 4 ≤ 24 * Real.exp u := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 24)] at hpow
      linarith
    have hlin : 1 + |s| ≤ 2 * u := by rw [hu]; linarith
    have h4' : (0 : ℝ) ≤ 1 + |s| := by linarith
    have hpow4 : (1 + |s|) ^ 4 ≤ (2 * u) ^ 4 := pow_le_pow_left₀ h4' hlin 4
    have hexp : Real.exp u = Real.exp 1 * Real.exp (|s| / 2) := by
      rw [hu, show |s| / 2 + 1 = 1 + |s| / 2 from by ring, Real.exp_add]
    rw [hexp] at h4
    calc (1 + |s|) ^ 4 ≤ (2 * u) ^ 4 := hpow4
      _ = 16 * u ^ 4 := by ring
      _ ≤ 384 * (Real.exp 1 * Real.exp (|s| / 2)) := by nlinarith [h4]
  -- (3 + |s|) ^ 4 ≤ 256 (1 + |s|) ^ 4
  have h2 : (3 + |s|) ^ 4 ≤ 256 * (1 + |s|) ^ 4 := by
    have hle : 3 + |s| ≤ 4 * (1 + |s|) := by linarith
    have hpos : (0 : ℝ) ≤ 3 + |s| := by linarith
    calc (3 + |s|) ^ 4 ≤ (4 * (1 + |s|)) ^ 4 := pow_le_pow_left₀ hpos hle 4
      _ = 256 * (1 + |s|) ^ 4 := by ring
  -- combine: (3 + |s|) ^ 4 ≤ 1048576 exp (1 + |s| / 2)
  have key : (3 + |s|) ^ 4 ≤ 1048576 * Real.exp (1 + |s| / 2) := by
    have hexp1 : Real.exp 1 * Real.exp (|s| / 2) = Real.exp (1 + |s| / 2) := by
      rw [Real.exp_add]
    rw [hexp1] at h1
    refine h2.trans ?_
    calc 256 * (1 + |s|) ^ 4 ≤ 256 * (384 * Real.exp (1 + |s| / 2)) := by linarith [h1]
      _ ≤ 1048576 * Real.exp (1 + |s| / 2) := by
          have hpos : (0 : ℝ) < Real.exp (1 + |s| / 2) := Real.exp_pos _
          nlinarith [hpos]
  -- multiply by the decay and fold into one exponential
  have hc : (0 : ℝ) < Real.exp (-(Real.pi / 2) * |s|) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right key hc.le
  have he1 : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hpos : (0 : ℝ) < Real.exp (-((Real.pi - 1) / 2) * |s|) := Real.exp_pos _
  refine hmul.trans ?_
  calc 1048576 * Real.exp (1 + |s| / 2) * Real.exp (-(Real.pi / 2) * |s|)
      = 1048576 * (Real.exp 1 * Real.exp (-((Real.pi - 1) / 2) * |s|)) := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
        have hh := mul_le_mul_of_nonneg_right he1 hpos.le
        nlinarith [hpos]

-- END LEAF 5 POLY

/-- The degree four polynomial-exponential weight has an absolutely bounded integral on any
symmetric interval. This is the constant that absorbs the coefficient weight in leaf 5. -/
private theorem poly_exp_moment487 (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) ≤ 8388608 := by
  have hc : (0 : ℝ) < (Real.pi - 1) / 2 := by linarith [Real.pi_gt_three]
  have hcont : Continuous fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|) := by fun_prop
  have hTT : (-T : ℝ) ≤ T := by linarith
  -- the one sided integral of the decay
  have hhalf : (∫ s in (0 : ℝ)..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) ≤
      2 / (Real.pi - 1) := by
    rw [intervalIntegral.integral_of_le hT]
    have hcongr : (∫ s in Set.Ioc (0 : ℝ) T,
        Real.exp (-((Real.pi - 1) / 2) * |s|)) =
        ∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-((Real.pi - 1) / 2) * s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [abs_of_pos hs.1]
    rw [hcongr]
    refine le_trans (setIntegral_mono_set (μ := volume)
      (integrableOn_exp_mul_Ioi (a := -((Real.pi - 1) / 2)) (by linarith) (0 : ℝ))
      (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx))) ?_
    rw [integral_exp_mul_Ioi (a := -((Real.pi - 1) / 2)) (by linarith) (0 : ℝ), mul_zero,
      Real.exp_zero]
    have hval : -(1 : ℝ) / (-((Real.pi - 1) / 2)) = 2 / (Real.pi - 1) := by
      rw [div_eq_div_iff (by linarith : (-((Real.pi - 1) / 2)) ≠ 0)
        (by linarith : (Real.pi - 1) ≠ 0)]
      ring
    rw [hval]
  have heven : (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) =
      ∫ s in (0 : ℝ)..T, Real.exp (-((Real.pi - 1) / 2) * |s|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|)) (a := (0 : ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [abs_neg]
  have htotal : (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) ≤
      4 / (Real.pi - 1) := by
    have h1 : IntervalIntegrable (fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|))
        volume (-T) 0 := hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => Real.exp (-((Real.pi - 1) / 2) * |s|))
        volume 0 T := hcont.intervalIntegrable _ _
    have hsplit : (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) =
        (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
          (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    calc (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|))
        = (∫ s in -T..0, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
            (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := hsplit
      _ = (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) +
            (∫ s in 0..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := by rw [heven]
      _ ≤ 2 / (Real.pi - 1) + 2 / (Real.pi - 1) := add_le_add hhalf hhalf
      _ = 4 / (Real.pi - 1) := by ring
  have hstep : (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) ≤
      ∫ s in -T..T, 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (by fun_prop : Continuous fun s : ℝ =>
        (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s : ℝ =>
        4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|)).intervalIntegrable _ _
    · intro s _
      exact poly_le_exp487 s
  have hval : (∫ s in -T..T, 4194304 * Real.exp (-((Real.pi - 1) / 2) * |s|)) =
      4194304 * (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hval] at hstep
  have hpi : (0 : ℝ) < (Real.pi - 1) := by linarith [Real.pi_gt_three]
  have hnn : (0 : ℝ) ≤ ∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|) :=
    intervalIntegral.integral_nonneg hTT (fun s _ => (Real.exp_pos _).le)
  calc (∫ s in -T..T, (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|))
      ≤ 4194304 * (∫ s in -T..T, Real.exp (-((Real.pi - 1) / 2) * |s|)) := hstep
    _ ≤ 4194304 * (4 / (Real.pi - 1)) := by
        have : (0 : ℝ) ≤ 4 / (Real.pi - 1) := by positivity
        nlinarith [htotal, hnn, hpi]
    _ ≤ 8388608 := by
        rw [show (8388608 : ℝ) = 4194304 * 2 from by norm_num]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [div_le_iff₀ hpi]
        nlinarith [Real.pi_gt_three]

-- END LEAF 5 MOMENT

/-- The linear-exponential weight integrates to at most sixteen. -/
private theorem linear_exp_moment487 (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) ≤ 16 := by
  have hcont : Continuous fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|) := by fun_prop
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hhalf : (∫ s in (0 : ℝ)..T, Real.exp (-(Real.pi / 4) * |s|)) ≤ 4 / Real.pi := by
    rw [intervalIntegral.integral_of_le hT]
    have hcongr : (∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-(Real.pi / 4) * |s|)) =
        ∫ s in Set.Ioc (0 : ℝ) T, Real.exp (-(Real.pi / 4) * s) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [abs_of_pos hs.1]
    rw [hcongr]
    refine le_trans (setIntegral_mono_set (μ := volume)
      (integrableOn_exp_mul_Ioi (a := -(Real.pi / 4)) (by linarith [Real.pi_pos]) (0 : ℝ))
      (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx))) ?_
    rw [integral_exp_mul_Ioi (a := -(Real.pi / 4)) (by linarith [Real.pi_pos]) (0 : ℝ), mul_zero,
      Real.exp_zero]
    have hval : -(1 : ℝ) / (-(Real.pi / 4)) = 4 / Real.pi := by
      rw [div_eq_div_iff (by linarith [Real.pi_pos] : (-(Real.pi / 4)) ≠ 0)
        (ne_of_gt Real.pi_pos)]
      ring
    rw [hval]
  have heven : (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) =
      ∫ s in (0 : ℝ)..T, Real.exp (-(Real.pi / 4) * |s|) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) (a := (0 : ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [abs_neg]
  have htotal : (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) ≤ 8 / Real.pi := by
    have h1 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) volume (-T) 0 :=
      hcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Real.pi / 4) * |s|)) volume 0 T :=
      hcont.intervalIntegrable _ _
    have hsplit : (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) =
        (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) +
          (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    calc (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|))
        = (∫ s in -T..0, Real.exp (-(Real.pi / 4) * |s|)) +
            (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) := hsplit
      _ = (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) +
            (∫ s in 0..T, Real.exp (-(Real.pi / 4) * |s|)) := by rw [heven]
      _ ≤ 4 / Real.pi + 4 / Real.pi := add_le_add hhalf hhalf
      _ = 8 / Real.pi := by ring
  have hstep : (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) ≤
      ∫ s in -T..T, 4 * Real.exp (-(Real.pi / 4) * |s|) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (by fun_prop : Continuous fun s : ℝ =>
        (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun s : ℝ =>
        4 * Real.exp (-(Real.pi / 4) * |s|)).intervalIntegrable _ _
    · intro s _
      exact exp_weight_le487 s
  have hval : (∫ s in -T..T, 4 * Real.exp (-(Real.pi / 4) * |s|)) =
      4 * (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hval] at hstep
  have hnn : (0 : ℝ) ≤ ∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|) :=
    intervalIntegral.integral_nonneg hTT (fun s _ => (Real.exp_pos _).le)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  calc (∫ s in -T..T, (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|))
      ≤ 4 * (∫ s in -T..T, Real.exp (-(Real.pi / 4) * |s|)) := hstep
    _ ≤ 4 * (8 / Real.pi) := by
        have : (0 : ℝ) ≤ 8 / Real.pi := by positivity
        nlinarith [htotal, hnn, hpi]
    _ ≤ 16 := by
        have he : 4 * (8 / Real.pi) = 32 / Real.pi := by ring
        rw [he, div_le_iff₀ hpi]
        nlinarith [Real.pi_gt_three]

-- END LEAF 5 LINEARMOMENT

/-- The coefficient times the Gamma weight integrates to an explicit constant, uniformly in the
frequency radius. This is the single-variable factor of the negative-region square. -/
private theorem coeff_weight_moment487 (N : ℕ) (hN : 16384 ≤ N) (B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in -T..T, ‖M s‖ * (Real.sqrt (2 * Real.pi) * (3 + |s|) *
        Real.exp (-(Real.pi * |s| / 2))))
      ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) := by
  set W : ℝ → ℝ := fun s => Real.sqrt (2 * Real.pi) * (3 + |s|) *
    Real.exp (-(Real.pi * |s| / 2)) with hW
  set L : ℝ → ℝ := fun s => (3 + |s|) * Real.exp (-(Real.pi / 2) * |s|) with hL
  set P : ℝ → ℝ := fun s => (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|) with hP
  have hconv : ∀ s : ℝ, Real.exp (-(Real.pi * |s| / 2)) = Real.exp (-(Real.pi / 2) * |s|) := by
    intro s
    congr 1
    ring
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hWcont : Continuous W := by rw [hW]; fun_prop
  have hLcont : Continuous L := by rw [hL]; fun_prop
  have hPcont : Continuous P := by rw [hP]; fun_prop
  -- the pointwise comparison
  have hpt : ∀ s : ℝ, ‖M s‖ * W s ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
    intro s
    have h1 := mellin_weight_le487 N (by omega) B0 hB0 M hM s
    have hWnn : (0 : ℝ) ≤ W s := by rw [hW]; positivity
    have hstep : ‖M s‖ * W s ≤
        B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) * W s :=
      mul_le_mul_of_nonneg_right h1 hWnn
    have he' : B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) *
          (Real.sqrt (2 * Real.pi) * (3 + |s|) * Real.exp (-(Real.pi * |s| / 2))) =
        8 * B0 * Real.sqrt (2 * Real.pi) *
          (Real.log N ^ 3 * ((3 + |s|) * Real.exp (-(Real.pi / 2) * |s|)) +
            (3 + |s|) ^ 4 * Real.exp (-(Real.pi / 2) * |s|)) := by
      rw [hconv s]
      ring
    have he : B0 * (8 * Real.log N ^ 3 + 8 * (3 + |s|) ^ 3) * W s =
        8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
      simpa only [hW, hL, hP] using he'
    linarith [hstep, he ▸ hstep]
  -- the majorant is continuous
  have hmajcont : Continuous fun s : ℝ =>
      8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) :=
    continuous_const.mul ((continuous_const.mul hLcont).add hPcont)
  have hmono : (∫ s in -T..T, ‖M s‖ * W s) ≤
      ∫ s in -T..T, 8 * B0 * Real.sqrt (2 * Real.pi) * (Real.log N ^ 3 * L s + P s) := by
    apply intervalIntegral.integral_mono_on hTT
    · exact (hM.1.norm.mul hWcont).intervalIntegrable _ _
    · exact hmajcont.intervalIntegrable _ _
    · intro s _
      exact hpt s
  -- evaluate the majorant integral
  have hsplit : (∫ s in -T..T, 8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * L s + P s)) =
      8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s)) := by
    have hIL : IntervalIntegrable (fun s : ℝ => Real.log N ^ 3 * L s) volume (-T) T :=
      (continuous_const.mul hLcont).intervalIntegrable _ _
    have hIP : IntervalIntegrable P volume (-T) T := hPcont.intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_add hIL hIP, intervalIntegral.integral_const_mul]
  have hLb : (∫ s in -T..T, L s) ≤ 16 := by
    rw [hL]
    exact linear_exp_moment487 T hT
  have hPb : (∫ s in -T..T, P s) ≤ 8388608 := by
    rw [hP]
    exact poly_exp_moment487 T hT
  have hLnn : (0 : ℝ) ≤ ∫ s in -T..T, L s :=
    intervalIntegral.integral_nonneg hTT (fun s _ => by rw [hL]; positivity)
  have hlog3 : (0 : ℝ) ≤ Real.log N ^ 3 := by positivity
  have hB : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) := by positivity
  rw [hsplit] at hmono
  refine hmono.trans ?_
  have hinner : Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s) ≤
      16 * Real.log N ^ 3 + 8388608 := by
    nlinarith [hLb, hPb, hLnn, hlog3]
  calc 8 * B0 * Real.sqrt (2 * Real.pi) *
        (Real.log N ^ 3 * (∫ s in -T..T, L s) + (∫ s in -T..T, P s))
      ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) :=
        mul_le_mul_of_nonneg_left hinner hB

-- END LEAF 5 COEFFMOMENT

private theorem sum_region_core487 (N : ℕ) (hN : 16384 ≤ N) (R : ℝ) (hR1 : 1 ≤ R)
    (hRN : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (B0 : ℝ) (hB0 : 0 < B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M) :
    (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          if 0 ≤ t + u then 0
          else ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)
      ≤ (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTT : -T ≤ T := by linarith
  -- the logarithms are at least one
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    refine Real.le_log_iff_exp_le ?_ |>.mpr ?_
    · exact hNpos
    · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  -- `4 R ≤ N`
  have h4R : 4 * R ≤ (N : ℝ) := by
    have h1 : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    have h2 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 4 := by
      rw [← Real.sqrt_eq_rpow]
      have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hNpos.le
      have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 16 ≤ N by omega)
      have h4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith [hs, hs0, h16]
      nlinarith [hs, hs0, h4]
    linarith
  -- the single-variable weight and the coefficient-weighted version
  set G : ℝ → ℝ := fun s => ‖M s‖ * (Real.sqrt (2 * Real.pi) * (3 + |s|) *
    Real.exp (-(Real.pi * |s| / 2))) with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact hM.1.norm.mul (by fun_prop)
  have hGnn : ∀ s : ℝ, 0 ≤ G s := by
    intro s
    rw [hG]
    positivity
  -- the joint integrand and its majorant
  set C : ℝ := (1 / R) * (Real.exp 2 * (N : ℝ)) with hC
  have hCnn : (0 : ℝ) ≤ C := by rw [hC]; positivity
  have hJcont : Continuous fun z : ℝ × ℝ =>
      ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖ := by
    have hI : Continuous fun z : ℝ × ℝ => ∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2) :=
      continuous_alphaKernel_integral487 N (by omega) _ _
    exact ((hM.1.comp continuous_fst).norm.mul (hM.1.comp continuous_snd).norm).mul hI.norm
  have hMAJcont : Continuous fun z : ℝ × ℝ => C * (G z.1 * G z.2) :=
    continuous_const.mul ((hGcont.comp continuous_fst).mul (hGcont.comp continuous_snd))
  -- pointwise domination on the whole plane
  have hmaj : ∀ t u : ℝ,
      (if 0 ≤ t + u then (0 : ℝ)
        else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)
      ≤ C * (G t * G u) := by
    intro t u
    by_cases h : 0 ≤ t + u
    · rw [if_pos h]
      have h1 : (0 : ℝ) ≤ G t := hGnn t
      have h2 : (0 : ℝ) ≤ G u := hGnn u
      have := mul_nonneg h1 h2
      have := mul_nonneg hCnn this
      linarith
    · rw [if_neg h]
      have hker := kernel_pair_integral487 N (by omega) R hR1 h4R t u
        (le_of_lt (lt_of_not_ge h))
      have hstep : ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
          ≤ ‖M t‖ * ‖M u‖ * (C *
            ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
             (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := by
        rw [hC]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
            ≤ 1 / R * (Real.exp 2 * (N : ℝ) *
                ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                 (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2))))) := hker
          _ = 1 / R * (Real.exp 2 * (N : ℝ)) *
                ((Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) *
                 (Real.sqrt (2 * Real.pi) * (3 + |u|) * Real.exp (-(Real.pi * |u| / 2)))) := by ring
      refine hstep.trans (le_of_eq ?_)
      rw [hC, hG]
      ring
  -- the majorant is integrable on the box
  have hMAJint : IntegrableOn (fun z : ℝ × ℝ => C * (G z.1 * G z.2))
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) :=
    (hMAJcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hnnF : ∀ z : ℝ × ℝ, (0 : ℝ) ≤
      (if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖) := by
    intro z
    by_cases h : 0 ≤ z.1 + z.2
    · rw [if_pos h]
    · rw [if_neg h]
      positivity
  -- the joint integrand is integrable on the box by domination
  have hFint : IntegrableOn (fun z : ℝ × ℝ => if 0 ≤ z.1 + z.2 then (0 : ℝ)
      else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖)
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T) := by
    have hmeas : Measurable fun z : ℝ × ℝ => if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖ :=
      Measurable.ite (measurableSet_le measurable_const (measurable_fst.add measurable_snd))
        measurable_const hJcont.measurable
    refine Integrable.mono' hMAJint hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnnF z)]
    exact hmaj z.1 z.2
  -- the box comparison
  have hbox : (∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), (if 0 ≤ z.1 + z.2 then (0 : ℝ)
        else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖))
      ≤ ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), C * (G z.1 * G z.2) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => ?_))
      hMAJint (Filter.Eventually.of_forall (fun z => hmaj z.1 z.2))
    exact hnnF z
  -- factorize the majorant integral
  have hmajint : (∫ t in -T..T, ∫ u in -T..T, C * (G t * G u)) =
      C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by
    have hinner : ∀ t : ℝ, (∫ u in -T..T, C * (G t * G u)) =
        C * G t * (∫ u in -T..T, G u) := by
      intro t
      have hfac : (fun u : ℝ => C * (G t * G u)) = fun u : ℝ => (C * G t) * G u := by
        funext u
        ring
      rw [hfac, intervalIntegral.integral_const_mul]
    have houter : (∫ t in -T..T, C * G t * (∫ u in -T..T, G u)) =
        C * (∫ u in -T..T, G u) * (∫ t in -T..T, G t) := by
      have hfac : (fun t : ℝ => C * G t * (∫ u in -T..T, G u)) =
          fun t : ℝ => (C * (∫ u in -T..T, G u)) * G t := by
        funext t
        ring
      rw [hfac, intervalIntegral.integral_const_mul]
    calc (∫ t in -T..T, ∫ u in -T..T, C * (G t * G u))
        = ∫ t in -T..T, C * G t * (∫ u in -T..T, G u) := by simp only [hinner]
      _ = C * (∫ u in -T..T, G u) * (∫ t in -T..T, G t) := houter
      _ = C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by ring
  have hmono : (∫ t in -T..T, ∫ u in -T..T, (if 0 ≤ t + u then (0 : ℝ)
        else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
            mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖))
      ≤ C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := by
    calc (∫ t in -T..T, ∫ u in -T..T, (if 0 ≤ t + u then (0 : ℝ)
          else ‖M t‖ * ‖M u‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖))
        = ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), (if 0 ≤ z.1 + z.2 then (0 : ℝ)
            else ‖M z.1‖ * ‖M z.2‖ * ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α z.1 * (starRingEnd ℂ) (mellinKernel442 N α z.2)‖) :=
          iterated_eq_box487 _ (-T) T hFint
      _ ≤ ∫ z in (Set.uIoc (-T) T ×ˢ Set.uIoc (-T) T), C * (G z.1 * G z.2) := hbox
      _ = ∫ t in -T..T, ∫ u in -T..T, C * (G t * G u) :=
          (iterated_eq_box487 (fun t u => C * (G t * G u)) (-T) T hMAJint).symm
      _ = C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) := hmajint
  -- bound the one dimensional integral
  have hGb : (∫ s in -T..T, G s) ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608) := by
    rw [hG]
    exact coeff_weight_moment487 N hN B0 hB0.le M hM T hT0
  have hlog3 : (1 : ℝ) ≤ Real.log N ^ 3 := by
    have h0 := Real.log_nonneg hNr1
    nlinarith [hlog1, h0, sq_nonneg (Real.log N)]
  have hGb2 : (∫ s in -T..T, G s) ≤
      8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 := by
    refine hGb.trans ?_
    have h1 : 16 * Real.log N ^ 3 + 8388608 ≤ 8388624 * Real.log N ^ 3 := by
      nlinarith [hlog3]
    have h2 : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) := by positivity
    calc 8 * B0 * Real.sqrt (2 * Real.pi) * (16 * Real.log N ^ 3 + 8388608)
        ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * (8388624 * Real.log N ^ 3) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 := by ring
  -- numerical closing
  have hA : (0 : ℝ) ≤ (1 / R) * (Real.exp 2 * (N : ℝ)) := by positivity
  have hG2 : (∫ s in -T..T, G s) * (∫ s in -T..T, G s) ≤
      (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) := by
    have hnn : (0 : ℝ) ≤ ∫ s in -T..T, G s :=
      intervalIntegral.integral_nonneg hTT (fun s _ => hGnn s)
    exact mul_le_mul hGb2 hGb2 hnn (by positivity)
  refine hmono.trans ?_
  have hlog6 : (0 : ℝ) ≤ Real.log N ^ 6 := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have h1 : (2 * Real.pi : ℝ) ≤ 9 := by nlinarith [Real.pi_lt_four]
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt h1
      _ = 3 := by norm_num
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have he : (Real.exp 2 : ℝ) ≤ 9 := by
    rw [hexp2]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith [Real.exp_pos 1]
  have hnnG : (0 : ℝ) ≤ ∫ s in -T..T, G s :=
    intervalIntegral.integral_nonneg hTT (fun s _ => hGnn s)
  -- insert the one dimensional bound
  have hstep1 : C * ((∫ s in -T..T, G s) * (∫ s in -T..T, G s)) ≤
      C * ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCnn
    exact mul_le_mul hGb2 hGb2 hnnG (by positivity)
  refine hstep1.trans ?_
  rw [hC]
  have hK : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
        (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2) ≤
      B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
    have hloggroup : Real.log N ^ 6 = Real.log N ^ 3 * Real.log N ^ 3 := by ring
    rw [hloggroup]
    have hS : 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 ≤
        8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by
      calc 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3
          = (8 * B0 * 8388624 * Real.log N ^ 3) * Real.sqrt (2 * Real.pi) := by ring
        _ ≤ (8 * B0 * 8388624 * Real.log N ^ 3) * 3 :=
            mul_le_mul_of_nonneg_left hsqrt
              (by positivity : (0 : ℝ) ≤ 8 * B0 * 8388624 * Real.log N ^ 3)
        _ = 8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by ring
    have hSnn : (0 : ℝ) ≤ 8 * B0 * 3 * 8388624 * Real.log N ^ 3 := by positivity
    have hS'nn : (0 : ℝ) ≤ 8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3 :=
      by positivity
    have hsq : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) ≤
        (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) :=
      mul_le_mul hS hS hS'nn hSnn
    have hsq2 : (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2) ≤
        (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) * (Real.exp 2) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos 2).le
    refine hsq2.trans ?_
    have hrw : (8 * B0 * 3 * 8388624 * Real.log N ^ 3) *
          (8 * B0 * 3 * 8388624 * Real.log N ^ 3) * (Real.exp 2) =
        B0 ^ 2 * (Real.log N ^ 3 * Real.log N ^ 3) *
          ((8 * 3 * 8388624) * (8 * 3 * 8388624) * (Real.exp 2)) := by ring
    rw [hrw]
    have hnn : (0 : ℝ) ≤ B0 ^ 2 * (Real.log N ^ 3 * Real.log N ^ 3) := by positivity
    have hnum : (8 * 3 * 8388624 : ℝ) * (8 * 3 * 8388624) * (Real.exp 2) ≤
        36893488147419103232 := by
      nlinarith [he, Real.exp_pos 2, sq_nonneg (8 * 3 * 8388624 : ℝ)]
    exact mul_le_mul_of_nonneg_left hnum hnn
  calc (1 / R) * (Real.exp 2 * (N : ℝ)) *
        ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3))
      = (N : ℝ) / R * ((8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) *
          (8 * B0 * Real.sqrt (2 * Real.pi) * 8388624 * Real.log N ^ 3) * (Real.exp 2)) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ (N : ℝ) / R * (B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232) := by
        refine mul_le_mul_of_nonneg_left hK (by positivity)
    _ = (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by
        have hsplit : (N : ℝ) / R * (B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232) =
            (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 := by ring
        rw [hsplit]

-- END LEAF 5 CORE

/-- `4 R ≤ N` from the radius restriction, for the range used by leaf 5. -/
private theorem four_mul_le487 (N : ℕ) (hN : 16384 ≤ N) (R : ℝ)
    (hR : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) : 4 * R ≤ (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h1 : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
  have h2 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 4 := by
    rw [← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNpos.le
    have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have h16 : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 16 ≤ N by omega)
    have h4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith [hs, hs0, h16]
    nlinarith [hs, hs0, h4]
  linarith

/-- The decay factor at the anti-diagonal scale is at least a sixteenth. -/
private theorem exp_quarter_le487 : (1 / 16 : ℝ) ≤ Real.exp (-(Real.pi / 4)) := by
  have hpos : (0 : ℝ) < Real.exp (Real.pi / 4) := Real.exp_pos _
  have h2 : Real.exp (Real.pi / 4) ≤ 16 := by
    have hpi : Real.pi / 4 ≤ 2 := by nlinarith [Real.pi_lt_four]
    have hle : Real.exp (Real.pi / 4) ≤ Real.exp 2 := Real.exp_le_exp.mpr hpi
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h9 : Real.exp 2 ≤ 9 := by
      rw [he2]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    linarith
  have hinv : Real.exp (-(Real.pi / 4)) = (Real.exp (Real.pi / 4))⁻¹ := by
    rw [← Real.exp_neg]
  rw [hinv]
  simpa only [one_div] using one_div_le_one_div_of_le hpos h2


/-- LEAF. First conjunct of the target: the square of the finite signed contour is continuous in
alpha, so it is interval integrable over the outer range. No estimate is involved. -/
theorem outer_finite_square_integrable487 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, ∀ M : ℝ → ℂ, Continuous M →
      IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2) volume
        (4 / (N : ℝ)) (1 / R) := by
  refine ⟨2, ?_⟩
  intro N hN R M hM
  exact ((continuous_truncatedMellin487 N (by omega) R M hM).norm.pow 2).intervalIntegrable _ _

/-- LEAF. Square and Fubini step. The squared finite contour is bounded by two over pi squared
times the double frequency integral of the coefficient moduli times the modulus of the alpha
integral of the kernel product. Only the signed square identity, the exchange of the alpha
integral with the two frequency integrals and the triangle inequality are used here. -/
theorem outer_finite_modulus_reduction487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (M : ℝ → ℂ)
    (hM : Continuous M) :
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
      (1 / (2 * Real.pi)) ^ 2 *
        ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ := by
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let a : ℝ := 4 / (N : ℝ)
  let b : ℝ := 1 / R
  let H : ℝ → ℝ → ℝ := fun t u => ‖M t‖ * ‖M u‖ *
    ‖∫ α in a..b, mellinKernel442 N α t * star (mellinKernel442 N α u)‖
  have hH0 (t u : ℝ) : 0 ≤ H t u := by dsimp [H]; positivity
  have hpos : 0 ≤ ∫ t in -T..T, ∫ u in -T..T, H t u := by
    rcases le_total (-T) T with hT | hT
    · exact intervalIntegral.integral_nonneg_of_forall hT (fun t =>
        intervalIntegral.integral_nonneg_of_forall hT (hH0 t))
    · have hrev : (∫ t in -T..T, ∫ u in -T..T, H t u) =
          ∫ t in T..-T, ∫ u in T..-T, H t u := by
        calc
          _ = -(∫ t in T..-T, ∫ u in -T..T, H t u) := by
            rw [intervalIntegral.integral_symm]
          _ = -(∫ t in T..-T, -(∫ u in T..-T, H t u)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro t ht
            change (∫ u in -T..T, H t u) = -(∫ u in T..-T, H t u)
            exact intervalIntegral.integral_symm T (-T)
          _ = _ := by rw [intervalIntegral.integral_neg, neg_neg]
      rw [hrev]
      exact intervalIntegral.integral_nonneg_of_forall hT (fun t =>
        intervalIntegral.integral_nonneg_of_forall hT (hH0 t))
  change (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) ≤
    (1 / (2 * Real.pi)) ^ 2 * ∫ t in -T..T, ∫ u in -T..T, H t u
  by_cases hab : a ≤ b
  · have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have ha : 0 < a := by dsimp [a]; positivity
    have hRp : 0 < R := (one_div_pos).mp (ha.trans_le hab)
    have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hT0 : 0 ≤ T := by dsimp [T]; positivity
    have horder : -T ≤ T := by linarith
    let G : ℝ → ℝ → ℂ := fun t u => (M t * star (M u)) *
      ∫ α in a..b, mellinKernel442 N α t * star (mellinKernel442 N α u)
    have hK : Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
      simpa only [mul_one] using
        continuous_mellin_integrand487 N hN (fun _ => 1) continuous_const
    have hP : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.1)) :=
      continuous_snd.prodMk continuous_fst.fst
    have hQ : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) :=
      continuous_snd.prodMk continuous_fst.snd
    have hF : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        mellinKernel442 N p.2 p.1.1 * star (mellinKernel442 N p.2 p.1.2)) := by
      simpa only [Function.comp_def, Pi.mul_def] using (hK.comp hP).mul (hK.comp hQ).star
    have hI : Continuous (fun p : ℝ × ℝ =>
        ∫ α in a..b, mellinKernel442 N α p.1 * star (mellinKernel442 N α p.2)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF a b
    have hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2) := by
      simpa only [G, Function.comp_def, Pi.mul_def] using
        ((hM.comp continuous_fst).mul (hM.comp continuous_snd).star).mul hI
    have hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
      simpa only [H, Function.comp_def, Pi.mul_def] using
        ((hM.comp continuous_fst).norm.mul (hM.comp continuous_snd).norm).mul hI.norm
    have hGi : Continuous (fun t : ℝ => ∫ u in -T..T, G t u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG (-T) T
    have hHi : Continuous (fun t : ℝ => ∫ u in -T..T, H t u) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hH (-T) T
    have hfactor (t u : ℝ) :
        (∫ α in a..b, (mellinKernel442 N α t * M t) *
          (starRingEnd ℂ) (mellinKernel442 N α u * M u)) = G t u := by
      dsimp [G]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro α hα
      simp only [map_mul]
      ring
    have hf := truncated_signed_fubini487 N hN R M hM a b
    dsimp only at hf
    simp_rw [hfactor] at hf
    rw [hf]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    calc
      _ ≤ ‖∫ t in -T..T, ∫ u in -T..T, G t u‖ := Complex.re_le_norm _
      _ ≤ ∫ t in -T..T, ‖∫ u in -T..T, G t u‖ :=
        intervalIntegral.norm_integral_le_integral_norm horder
      _ ≤ ∫ t in -T..T, ∫ u in -T..T, H t u := by
        apply intervalIntegral.integral_mono_on horder
          (hGi.norm.intervalIntegrable _ _) (hHi.intervalIntegrable _ _)
        intro t ht
        calc
          _ ≤ ∫ u in -T..T, ‖G t u‖ :=
            intervalIntegral.norm_integral_le_integral_norm horder
          _ = _ := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp only [G, H, norm_mul, norm_star]
  · have hba : b ≤ a := le_of_not_ge hab
    have hleft : (∫ α in a..b, ‖truncatedMellin487 N R M α‖ ^ 2) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall hba
        (fun α => sq_nonneg ‖truncatedMellin487 N R M α‖))
    exact hleft.trans (mul_nonneg (sq_nonneg _) hpos)

/-- LEAF. Region split of the frequency square. The double modulus integral over the square of
radius N over R times log cubed N is the sum of its part with t + u nonnegative and its part with
t + u negative. The two parts are the positive frequency difference case and the negative
frequency sum case of the outer contour. -/
theorem outer_finite_region_split487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (hM : Continuous M) :
    (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
      (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
            else 0) +
        (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then 0
            else
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) := by
  by_cases hzero : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := by omega
  let T : ℝ := (N : ℝ) / R * Real.log N ^ 3
  let H : ℝ × ℝ → ℝ := fun p => ‖M p.1‖ * ‖M p.2‖ *
    ‖∫ α in (4 / (N : ℝ))..(1 / R),
      mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)‖
  have hK : Continuous (fun p : ℝ × ℝ => mellinKernel442 N p.1 p.2) := by
    simpa only [mul_one] using
      continuous_mellin_integrand_positive493 N hN (fun _ => 1) continuous_const
  have hP : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.1)) :=
    continuous_snd.prodMk continuous_fst.fst
  have hQ : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.2, p.1.2)) :=
    continuous_snd.prodMk continuous_fst.snd
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      mellinKernel442 N p.2 p.1.1 * (starRingEnd ℂ) (mellinKernel442 N p.2 p.1.2)) := by
    simpa only [Function.comp_def, Pi.mul_def, starRingEnd_apply] using (hK.comp hP).mul (hK.comp hQ).star
  have hI : Continuous (fun p : ℝ × ℝ =>
      ∫ α in (4 / (N : ℝ))..(1 / R),
        mellinKernel442 N α p.1 * (starRingEnd ℂ) (mellinKernel442 N α p.2)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _
  have hH : Continuous H := by
    simpa only [H, Function.comp_def, Pi.mul_def] using
      ((hM.comp continuous_fst).norm.mul (hM.comp continuous_snd).norm).mul hI.norm
  let μ : Measure ℝ := volume.restrict (Set.uIoc (-T) T)
  have hprod : Integrable H (μ.prod μ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact (hH.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hinner (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (t : ℝ) :
      IntervalIntegrable (fun u => S.indicator H (t, u)) volume (-T) T := by
    apply intervalIntegrable_iff.mpr
    have hc : Continuous (fun u : ℝ => H (t, u)) :=
      hH.comp (continuous_const.prodMk continuous_id)
    have hi : IntervalIntegrable (fun u : ℝ => H (t,u)) volume (-T) T :=
      hc.intervalIntegrable (-T) T
    have hs : MeasurableSet ((fun u : ℝ => (t, u)) ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    change IntegrableOn (((fun u : ℝ => (t,u)) ⁻¹' S).indicator
      (fun u => H (t,u))) (Set.uIoc (-T) T) volume
    exact hi.def'.indicator hs
  have houter (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
      IntervalIntegrable (fun t => ∫ u in -T..T, S.indicator H (t, u))
        volume (-T) T := by
    apply intervalIntegrable_iff.mpr
    have hi := (hprod.indicator hS).integral_prod_left
    have hs := hi.const_mul (if -T ≤ T then (1 : ℝ) else -1)
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, μ, IntegrableOn] using hs
  let S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 + p.2}
  have hS : MeasurableSet S := measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  change (∫ t in -T..T, ∫ u in -T..T, H (t,u)) ≤
    (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then H (t,u) else 0) +
    (∫ t in -T..T, ∫ u in -T..T, if 0 ≤ t + u then 0 else H (t,u))
  have hsplit (t : ℝ) : (∫ u in -T..T, H (t,u)) =
      (∫ u in -T..T, S.indicator H (t,u)) +
      (∫ u in -T..T, Sᶜ.indicator H (t,u)) := by
    rw [← intervalIntegral.integral_add (hinner S hS t) (hinner Sᶜ hS.compl t)]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, Set.mem_compl_iff]
    split_ifs <;> simp
  calc
    _ = ∫ t in -T..T, ((∫ u in -T..T, S.indicator H (t,u)) +
        (∫ u in -T..T, Sᶜ.indicator H (t,u))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hsplit t
    _ = (∫ t in -T..T, ∫ u in -T..T, S.indicator H (t,u)) +
        (∫ t in -T..T, ∫ u in -T..T, Sᶜ.indicator H (t,u)) :=
      intervalIntegral.integral_add (houter S hS) (houter Sᶜ hS.compl)
    _ ≤ _ := by
      simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, Set.mem_compl_iff,
        ite_not]
      exact le_rfl

/-- LEAF. Positive frequency difference region, t + u nonnegative. The second mean value theorem in
alpha applied to the monotone arctangent factor bounds the alpha integral of the kernel product by
a constant over one plus the frequency difference, so the region costs the reciprocal difference
kernel at the radius N over R times log cubed N. -/
theorem outer_finite_difference_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
                else 0) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  sorry

/-- LEAF. Negative frequency sum region, t + u negative. There the Gamma asymptotics on the line
supply exponential decay in the sum of the frequencies, which dominates the polynomial weight of
the coefficient bound, so the region costs log N to the seventh times the exponential sum kernel at
the radius N over R times log cubed N. -/
theorem outer_finite_sum_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then 0
                else
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  refine ⟨4722366482869645213696 * B0 ^ 2, by positivity, 16383, ?_⟩
  intro N hN R hR1 hRN M hM
  have hN16 : 16384 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRpos : (0 : ℝ) < R := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    refine Real.le_log_iff_exp_le hNpos |>.mpr ?_
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  have hlog4 : (1 : ℝ) ≤ Real.log N ^ 4 := by
    have h0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
    have hsq : (1 : ℝ) ≤ Real.log N * Real.log N := by nlinarith [hlog1]
    have hgroup : Real.log N ^ 4 = (Real.log N * Real.log N) * (Real.log N * Real.log N) :=
      by ring
    rw [hgroup]
    nlinarith [hsq, mul_nonneg h0 h0]
  have h4R : 4 * R ≤ (N : ℝ) := four_mul_le487 N hN16 R hRN
  -- the radius is at least two, so the sum kernel obeys its lower bound
  have hT2 : 2 ≤ (N : ℝ) / R * Real.log N ^ 3 := by
    have hNR : (4 : ℝ) ≤ (N : ℝ) / R := by
      rw [le_div_iff₀ hRpos]
      linarith
    have hlog3 : (1 : ℝ) ≤ Real.log N ^ 3 := by
      have h0 : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
      nlinarith [hlog1, h0, sq_nonneg (Real.log N)]
    calc (2 : ℝ) ≤ 4 * 1 := by norm_num
      _ ≤ (N : ℝ) / R * Real.log N ^ 3 :=
          mul_le_mul hNR hlog3 (by norm_num) (by linarith)
  have hlow := sumKernel_lower487 ((N : ℝ) / R * Real.log N ^ 3) hT2
  have hcore := sum_region_core487 N hN16 R hR1 hRN B0 hB0 M hM
  have hquarter := exp_quarter_le487
  -- everything is nonnegative
  have hNn : (0 : ℝ) ≤ N := hNpos.le
  have hRn : (0 : ℝ) ≤ R := hRpos.le
  have hlogn : (0 : ℝ) ≤ Real.log N := le_trans zero_le_one hlog1
  have hprod : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 := by positivity
  -- the comparison of the two right hand sides
  refine hcore.trans ?_
  have hstep : (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232 ≤
      4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7 *
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
    -- replace the sum kernel by its lower bound
    have hsumlb : Real.exp (-(Real.pi / 4)) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := hlow
    have hkey : (1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
        sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) :=
      le_trans (by
        have h1 : (1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2) ≤
            Real.exp (-(Real.pi / 4)) * (((N : ℝ) / R * Real.log N ^ 3) / 2) :=
          mul_le_mul_of_nonneg_right hquarter (by positivity)
        exact h1) hsumlb
    -- multiply the lower bound by the positive factor
    have hfac : (0 : ℝ) ≤ 4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7 := by positivity
    have hmul : (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
          ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) ≤
        (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
          sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) :=
      mul_le_mul_of_nonneg_left hkey hfac
    refine le_trans ?_ hmul
    -- and the explicit arithmetic
    have hlog6nn : (0 : ℝ) ≤ Real.log N ^ 6 := by positivity
    have hB0nn : (0 : ℝ) ≤ B0 ^ 2 := by positivity
    have hbase : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 6 := by positivity
    have harith : (N : ℝ) / R * Real.log N ^ 6 * 36893488147419103232 ≤
        (4722366482869645213696 : ℝ) * Real.log N ^ 7 *
          ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) := by
      have hgroup : Real.log N ^ 7 = Real.log N ^ 6 * Real.log N := by ring
      rw [hgroup]
      nlinarith [hlog4, hlog6nn, hlogn, hprod, hNn, hRn,
        mul_nonneg hlogn hlog6nn, mul_nonneg hlog6nn hlog6nn,
        mul_nonneg (mul_nonneg hlogn hlog6nn) hlogn]
    have hB0sq : (0 : ℝ) ≤ B0 ^ 2 := hB0nn
    calc (N : ℝ) / R * B0 ^ 2 * Real.log N ^ 6 * 36893488147419103232
        = B0 ^ 2 * ((N : ℝ) / R * Real.log N ^ 6 * 36893488147419103232) := by ring
      _ ≤ B0 ^ 2 * ((4722366482869645213696 : ℝ) * Real.log N ^ 7 *
            ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2))) :=
          mul_le_mul_of_nonneg_left harith hB0sq
      _ = (4722366482869645213696 * B0 ^ 2 * Real.log N ^ 7) *
            ((1 / 16 : ℝ) * (((N : ℝ) / R * Real.log N ^ 3) / 2)) := by ring
  exact hstep

/-- The finite signed outer square of the contour truncated at radius N over R times log cubed N.
This is proved from the integrability leaf, the square and Fubini reduction, the region split and
the two region estimates; the two region constants are added. -/
theorem outer_finite_square487_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2)
            volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  obtain ⟨Cd, hCd, Nd, hd⟩ := outer_finite_difference_region487 B0 hB0
  obtain ⟨Cs, hCs, Ns, hs⟩ := outer_finite_sum_region487 B0 hB0
  obtain ⟨Ni, hi⟩ := outer_finite_square_integrable487
  refine ⟨Cd + Cs, by positivity, max 8 (max Ni (max Nd Ns)), ?_⟩
  intro N hN R hR1 hR M hM
  have hN8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNd : Nd < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNs : Ns < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (pow_nonneg hl0 3)
  have hd0 : 0 ≤ differenceKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hs0 : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun u => (Real.exp_pos _).le)
  have hk0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ 2 := by positivity
  have hk1 : (1 / (2 * Real.pi)) ^ 2 ≤ 1 := by
    have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hle : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc (1 / (2 * Real.pi)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = 1 := one_pow 2
  have hl6d : 0 ≤ Real.log N ^ 6 * differenceKernel376 T :=
    mul_nonneg (pow_nonneg hl0 6) hd0
  have hl7s : 0 ≤ Real.log N ^ 7 * sumKernel376 T :=
    mul_nonneg (pow_nonneg hl0 7) hs0
  have e1 : (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) ≤
      Cd * Real.log N ^ 6 * differenceKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T)
        ≤ 1 * (Cd * Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCd.le (pow_nonneg hl0 6)) hd0)
      _ = Cd * Real.log N ^ 6 * differenceKernel376 T := one_mul _
  have e2 : (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) ≤
      Cs * Real.log N ^ 7 * sumKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T)
        ≤ 1 * (Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCs.le (pow_nonneg hl0 7)) hs0)
      _ = Cs * Real.log N ^ 7 * sumKernel376 T := one_mul _
  have e3 : Cd * Real.log N ^ 6 * differenceKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by
    calc Cd * Real.log N ^ 6 * differenceKernel376 T
        = Cd * (Real.log N ^ 6 * differenceKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCs.le) hl6d
      _ = (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by ring
  have e4 : Cs * Real.log N ^ 7 * sumKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by
    calc Cs * Real.log N ^ 7 * sumKernel376 T
        = Cs * (Real.log N ^ 7 * sumKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCd.le) hl7s
      _ = (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by ring
  refine ⟨hi N hNi R M hM.1, ?_⟩
  calc
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2)
        ≤ (1 / (2 * Real.pi)) ^ 2 *
          ∫ t in -T..T, ∫ u in -T..T,
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ :=
          outer_finite_modulus_reduction487 N (by omega) R M hM.1
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          ((∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
              else 0) +
            (∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then 0
              else
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)) :=
          mul_le_mul_of_nonneg_left (outer_finite_region_split487 N R M hM.1) hk0
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          (Cd * Real.log N ^ 6 * differenceKernel376 T +
            Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hd N hNd R hR1 hR M hM) (hs N hNs R hR1 hR M hM)) hk0
    _ = (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) +
          (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) := by ring
    _ ≤ Cd * Real.log N ^ 6 * differenceKernel376 T +
          Cs * Real.log N ^ 7 * sumKernel376 T := add_le_add e1 e2
    _ ≤ (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T +
          (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := add_le_add e3 e4

end LeanLab.Linnik1951
