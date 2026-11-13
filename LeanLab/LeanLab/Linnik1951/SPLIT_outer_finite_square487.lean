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

set_option maxHeartbeats 1600000 in
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
  sorry

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
