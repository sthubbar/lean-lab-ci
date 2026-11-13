import LeanLab.HelfgottMajor.MiddleEnergy123

/-!
Route burst 2026-11-12, step gaussian_explicit_estimate p4, the sampling step.
Source: Helfgott, book version Part IV pages 431 to 434, Lemma 16.9 as applied in the proof of
Lemma 16.10, display 16.26. Paper P0014 Lemma 4.4 is the arXiv form.

Contents, all PROVED here, with the count of display 3.95 entering only through the existing
leaf ZeroCount1623.book_zero_count:
* abel_count_bound and abel_norm_bound: the two integrations by parts of Lemma 16.9 on the
  range from 1 to T0, with the boundary term at T0 kept.
* bookCount_signed, full_count_bound, full_count_split: the count N(T, χ) in the form needed,
  a zero at the upper height counted in full, the lower half through the inverse character.
* signed_sampling_linear and signed_sampling_raw_cutoff: display 16.26 in corrected form,
  for either sign of the height.
* middle_mass_bound: the same statement as MiddleEnergy123.Decomp389b.middle_mass_bound,
  proved without MiddleEnergy123.Decomp389b.signed_sampling_raw.

QUESTION, book page 433: Lemma 16.9 asks for a continuous f, and is applied to
f(t) = |Gδ(1/2 + it)| for t ≤ T0 and 0 for t > T0, which jumps at T0, see the lab check
Sampling431.cutoff_not_continuous. Read with f' as a distribution, the error integral of
display 16.20 contains the point mass |f(T0)| gχ(T0) at the jump. Display 16.26 as printed
drops it, so 16.26 does not follow from Lemma 16.9 and display 3.95 alone. The corrected
bound proved here keeps the term |Gδ(1/2 ± iT0)| gχ(T0). The printed 16.26 itself is not
refuted. The final bound of the lab statement middle_mass_bound is not affected: the term is
absorbed by the gap between the book coefficients and the older page 40 coefficients, see
coefficient_gap. Whether the printed constants of display 16.22 absorb it is not checked here.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SamplingSplit123
open Real MeasureTheory Set Filter
open scoped Topology

/-- Book page 431 and 432, the two integrations by parts in the proof of Lemma 16.9, on the
finite range from 1 to T and for a finite family of ordinates with weights. The count input is
the hypothesis hcount: the weighted number of ordinates up to t, plus the count c0 up to
height 1, is M t up to the error E t. The boundary term at T is kept, since the test function
is not assumed to vanish there. -/
theorem abel_count_bound {ι : Type*} (Z : Finset ι) (γ m : ι → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hγ : ∀ i ∈ Z, 1 < γ i ∧ γ i ≤ T)
    (g g' M M' E : ℝ → ℝ) (c0 : ℝ)
    (hg : ∀ t ∈ Icc 1 T, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (Icc 1 T))
    (hM : ∀ t ∈ Icc 1 T, HasDerivAt M (M' t) t)
    (hM' : ContinuousOn M' (Icc 1 T))
    (hE : ContinuousOn E (Icc 1 T))
    (hcount : ∀ t ∈ Icc 1 T, |c0 + (∑ i ∈ Z, if γ i ≤ t then m i else 0) - M t| ≤ E t) :
    ∑ i ∈ Z, m i * g (γ i) ≤
      (∫ t in (1 : ℝ)..T, g t * M' t) + |g T| * E T + |g 1| * E 1 +
        ∫ t in (1 : ℝ)..T, |g' t| * E t := by
  classical
  have huIcc : uIcc 1 T = Icc 1 T := uIcc_of_le hT
  have hgc : ContinuousOn g (Icc 1 T) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Icc 1 T) := fun t ht => (hM t ht).continuousAt.continuousWithinAt
  have hg'i : IntegrableOn g' (Icc 1 T) := hg'.integrableOn_compact isCompact_Icc
  -- the single ordinate identity
  have hone : ∀ i ∈ Z, (∫ t in (1 : ℝ)..T, (Ici (γ i)).indicator (fun t => m i * g' t) t) =
      m i * (g T - g (γ i)) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hγ i hi
    rw [intervalIntegral.integral_of_le hT, setIntegral_indicator measurableSet_Ici]
    have hset : Ioc 1 T ∩ Ici (γ i) = Icc (γ i) T := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, b⟩, c⟩; exact ⟨c, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨by linarith, b⟩, a⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2,
      intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le h2] at ht
      exact hg t ⟨by linarith [ht.1], ht.2⟩
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le h2]
      exact hg'.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have hind_int : ∀ i ∈ Z, IntervalIntegrable
      (fun t => (Ici (γ i)).indicator (fun t => m i * g' t) t) volume 1 T := by
    intro i _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact ((hg'i.mono_set Ioc_subset_Icc_self).const_mul (m i)).indicator measurableSet_Ici
  set C : ℝ → ℝ := fun t => ∑ i ∈ Z, if γ i ≤ t then m i else 0 with hC
  have hCg : ∀ t, C t * g' t = ∑ i ∈ Z, (Ici (γ i)).indicator (fun t => m i * g' t) t := by
    intro t
    rw [hC, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : γ i ≤ t <;> simp [indicator, h]
  have hCg_int : IntervalIntegrable (fun t => C t * g' t) volume 1 T := by
    have := IntervalIntegrable.sum Z hind_int
    refine this.congr ?_
    intro t _
    simp only [Finset.sum_apply]
    exact (hCg t).symm
  have hsum : ∑ i ∈ Z, m i * g (γ i) = g T * C T - ∫ t in (1 : ℝ)..T, C t * g' t := by
    have h1 : (∫ t in (1 : ℝ)..T, C t * g' t) = ∑ i ∈ Z, m i * (g T - g (γ i)) := by
      simp_rw [hCg]
      rw [intervalIntegral.integral_finsetSum hind_int]
      exact Finset.sum_congr rfl hone
    have hCT : C T = ∑ i ∈ Z, m i := by
      rw [hC]
      apply Finset.sum_congr rfl
      intro i hi
      simp [(hγ i hi).2]
    rw [h1, hCT, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hC1 : C 1 = 0 := by
    rw [hC]
    apply Finset.sum_eq_zero
    intro i hi
    simp [not_le.mpr (hγ i hi).1]
  set R : ℝ → ℝ := fun t => c0 + C t - M t with hR
  have hRabs : ∀ t ∈ Icc 1 T, |R t| ≤ E t := hcount
  have hMg_int : IntervalIntegrable (fun t => M t * g' t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hMc.mul hg'
  have hg'_int : IntervalIntegrable g' volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hg'
  have hM'_int : IntervalIntegrable M' volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hM'
  have hRg_int : IntervalIntegrable (fun t => R t * g' t) volume 1 T := by
    have := (hCg_int.sub hMg_int).add (hg'_int.const_mul c0)
    refine this.congr ?_
    intro t _
    simp only [hR]; ring
  have hsplit : (∫ t in (1 : ℝ)..T, C t * g' t) =
      (∫ t in (1 : ℝ)..T, R t * g' t) + (∫ t in (1 : ℝ)..T, M t * g' t) -
        c0 * (g T - g 1) := by
    have hgi : (∫ t in (1 : ℝ)..T, g' t) = g T - g 1 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hg t (huIcc ▸ ht)) hg'_int
    rw [← hgi, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hRg_int hMg_int,
      ← intervalIntegral.integral_sub (hRg_int.add hMg_int) (hg'_int.const_mul c0)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hR]; ring
  have hparts : (∫ t in (1 : ℝ)..T, M t * g' t) =
      M T * g T - M 1 * g 1 - ∫ t in (1 : ℝ)..T, M' t * g t :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht => hM t (huIcc ▸ ht))
      (fun t ht => hg t (huIcc ▸ ht)) hM'_int hg'_int
  have hgE_int : IntervalIntegrable (fun t => |g' t| * E t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hg'.abs.mul hE
  have hbound : -(∫ t in (1 : ℝ)..T, R t * g' t) ≤ ∫ t in (1 : ℝ)..T, |g' t| * E t := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_mono_on hT hRg_int.neg hgE_int
    intro t ht
    have h1 := hRabs t ht
    have h2 : -(R t * g' t) ≤ |R t * g' t| := neg_le_abs _
    rw [abs_mul] at h2
    have h3 : |R t| * |g' t| ≤ E t * |g' t| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    show -(R t * g' t) ≤ |g' t| * E t
    linarith
  have hcomm : (∫ t in (1 : ℝ)..T, M' t * g t) = ∫ t in (1 : ℝ)..T, g t * M' t := by
    apply intervalIntegral.integral_congr
    intro t _; ring
  have hRT := hRabs T ⟨hT, le_rfl⟩
  have hR1 := hRabs 1 ⟨le_rfl, hT⟩
  have hR1eq : R 1 = c0 - M 1 := by simp only [hR, hC1]; ring
  have hCTeq : C T = R T + M T - c0 := by simp only [hR]; ring
  have e1 : g T * R T ≤ |g T| * E T := by
    calc g T * R T ≤ |g T * R T| := le_abs_self _
      _ = |g T| * |R T| := abs_mul _ _
      _ ≤ |g T| * E T := mul_le_mul_of_nonneg_left hRT (abs_nonneg _)
  have e2 : -(g 1 * R 1) ≤ |g 1| * E 1 := by
    calc -(g 1 * R 1) ≤ |g 1 * R 1| := neg_le_abs _
      _ = |g 1| * |R 1| := abs_mul _ _
      _ ≤ |g 1| * E 1 := mul_le_mul_of_nonneg_left hR1 (abs_nonneg _)
  rw [hsum, hsplit, hparts, hcomm, hCTeq]
  rw [hR1eq] at e2
  nlinarith [e1, e2, hbound]

/-! ### Lemma 16.9 for the norm of a differentiable complex function -/

lemma reg_norm_bounds (a : ℂ) {η : ℝ} (hη : 0 < η) :
    ‖a‖ ≤ sqrt (‖a‖ ^ 2 + η ^ 2) ∧ sqrt (‖a‖ ^ 2 + η ^ 2) ≤ ‖a‖ + η := by
  constructor
  · apply le_sqrt_of_sq_le; nlinarith [sq_nonneg η]
  · apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [norm_nonneg a]

lemma reg_norm_deriv_le (a b : ℂ) {η : ℝ} (hη : 0 < η) :
    |2 * inner ℝ a b / (2 * sqrt (‖a‖ ^ 2 + η ^ 2))| ≤ ‖b‖ := by
  have hr : 0 < sqrt (‖a‖ ^ 2 + η ^ 2) := sqrt_pos.mpr (by positivity)
  have ha := (reg_norm_bounds a hη).1
  have hi := abs_real_inner_le_norm a b
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * sqrt (‖a‖ ^ 2 + η ^ 2)), div_le_iff₀ (by positivity),
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [norm_nonneg b, mul_le_mul_of_nonneg_right ha (norm_nonneg b)]

/-- Book pages 431 and 432, Lemma 16.9 on the finite range from 1 to T, for the test function
t ↦ ‖F t‖ with F continuously differentiable. The absolute value of the derivative of the
test function is bounded by ‖F' t‖, as on book page 434 "since f (t) = Gδ (1/2 + it)". The
boundary term at T is kept. -/
theorem abel_norm_bound {ι : Type*} (Z : Finset ι) (γ m : ι → ℝ) (T : ℝ) (hT : 1 ≤ T)
    (hγ : ∀ i ∈ Z, 1 < γ i ∧ γ i ≤ T) (hm : ∀ i ∈ Z, 0 ≤ m i)
    (F F' : ℝ → ℂ) (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    (M M' E : ℝ → ℝ) (c0 : ℝ)
    (hM : ∀ t ∈ Icc 1 T, HasDerivAt M (M' t) t)
    (hM' : ContinuousOn M' (Icc 1 T))
    (hE : ContinuousOn E (Icc 1 T)) (hE0 : ∀ t ∈ Icc 1 T, 0 ≤ E t)
    (hcount : ∀ t ∈ Icc 1 T, |c0 + (∑ i ∈ Z, if γ i ≤ t then m i else 0) - M t| ≤ E t) :
    ∑ i ∈ Z, m i * ‖F (γ i)‖ ≤
      (∫ t in (1 : ℝ)..T, ‖F t‖ * M' t) + ‖F T‖ * E T + ‖F 1‖ * E 1 +
        ∫ t in (1 : ℝ)..T, ‖F' t‖ * E t := by
  have huIcc : uIcc 1 T = Icc 1 T := uIcc_of_le hT
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  have hET := hE0 T ⟨hT, le_rfl⟩
  have hE1 := hE0 1 ⟨le_rfl, hT⟩
  have hM'a_int : IntervalIntegrable (fun t => |M' t|) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hM'.abs
  have hFM_int : IntervalIntegrable (fun t => ‖F t‖ * M' t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFc.norm.continuousOn.mul hM'
  have hFE_int : IntervalIntegrable (fun t => ‖F' t‖ * E t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hF'.norm.continuousOn.mul hE
  set K : ℝ := (∫ t in (1 : ℝ)..T, |M' t|) + E T + E 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ t in (1 : ℝ)..T, |M' t| :=
      intervalIntegral.integral_nonneg hT (fun t _ => abs_nonneg _)
    linarith
  apply le_of_forall_pos_le_add
  intro e he
  set η : ℝ := e / (K + 1) with hηdef
  have hη : 0 < η := by positivity
  have hηK : η * K ≤ e := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  set g : ℝ → ℝ := fun t => sqrt (‖F t‖ ^ 2 + η ^ 2) with hg
  set g' : ℝ → ℝ := fun t => 2 * inner ℝ (F t) (F' t) / (2 * sqrt (‖F t‖ ^ 2 + η ^ 2)) with hg'
  have hgd : ∀ t, HasDerivAt g (g' t) t := fun t =>
    ((hF t).norm_sq.add_const (η ^ 2)).sqrt (by positivity)
  have hg'c : Continuous g' := by
    rw [hg']
    refine Continuous.div (continuous_const.mul (hFc.inner hF')) (continuous_const.mul
      (continuous_sqrt.comp ((hFc.norm.pow 2).add continuous_const))) ?_
    intro t
    have : 0 < sqrt (‖F t‖ ^ 2 + η ^ 2) := sqrt_pos.mpr (by positivity)
    positivity
  have hgc : Continuous g := continuous_sqrt.comp ((hFc.norm.pow 2).add continuous_const)
  have hA := abel_count_bound Z γ m T hT hγ g g' M M' E c0 (fun t _ => hgd t)
    hg'c.continuousOn hM hM' hE hcount
  have hb : ∀ t, ‖F t‖ ≤ g t ∧ g t ≤ ‖F t‖ + η := fun t => reg_norm_bounds (F t) hη
  have hg0 : ∀ t, 0 ≤ g t := fun t => sqrt_nonneg _
  have h1 : ∑ i ∈ Z, m i * ‖F (γ i)‖ ≤ ∑ i ∈ Z, m i * g (γ i) :=
    Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hb _).1 (hm i hi))
  have hgM_int : IntervalIntegrable (fun t => g t * M' t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hgc.continuousOn.mul hM'
  have h2 : (∫ t in (1 : ℝ)..T, g t * M' t) ≤
      (∫ t in (1 : ℝ)..T, ‖F t‖ * M' t) + η * ∫ t in (1 : ℝ)..T, |M' t| := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hFM_int
      (hM'a_int.const_mul η)]
    apply intervalIntegral.integral_mono_on hT hgM_int (hFM_int.add (hM'a_int.const_mul η))
    intro t _
    have h3 : (g t - ‖F t‖) * M' t ≤ η * |M' t| := by
      calc (g t - ‖F t‖) * M' t ≤ |(g t - ‖F t‖) * M' t| := le_abs_self _
        _ = (g t - ‖F t‖) * |M' t| := by
          rw [abs_mul, abs_of_nonneg (by linarith [(hb t).1])]
        _ ≤ η * |M' t| := mul_le_mul_of_nonneg_right (by linarith [(hb t).2]) (abs_nonneg _)
    show g t * M' t ≤ ‖F t‖ * M' t + η * |M' t|
    linarith
  have hgE_int : IntervalIntegrable (fun t => |g' t| * E t) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hg'c.abs.continuousOn.mul hE
  have h3 : (∫ t in (1 : ℝ)..T, |g' t| * E t) ≤ ∫ t in (1 : ℝ)..T, ‖F' t‖ * E t := by
    apply intervalIntegral.integral_mono_on hT hgE_int hFE_int
    intro t ht
    exact mul_le_mul_of_nonneg_right (reg_norm_deriv_le (F t) (F' t) hη) (hE0 t ht)
  have h4 : |g T| * E T ≤ ‖F T‖ * E T + η * E T := by
    rw [abs_of_nonneg (hg0 T)]
    nlinarith [(hb T).2]
  have h5 : |g 1| * E 1 ≤ ‖F 1‖ * E 1 + η * E 1 := by
    rw [abs_of_nonneg (hg0 1)]
    nlinarith [(hb 1).2]
  have hKe : η * K = η * (∫ t in (1 : ℝ)..T, |M' t|) + η * E T + η * E 1 := by
    rw [hK]; ring
  linarith

/-! ### The count input of Lemma 16.9, in the form the partial summation uses -/

section Count
open ZeroCount1623
variable {q : ℕ} [NeZero q]

/-- Book page 434, the remark that the lower half is handled with the conjugate character:
the book count of χ for ε = 1, and of its inverse for ε = −1, counts the zeros of χ on the
side 0 ≤ ε Im ρ. -/
theorem bookCount_signed (χ : DirichletCharacter ℂ q) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (t : ℝ) :
    bookCount (if ε = 1 then χ else χ⁻¹) t =
      ∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        halfWeight t (ε * ρ.im) * (mult χ ρ : ℝ) := by
  rcases hε with rfl | rfl
  · simp only [ite_true, one_mul]
    rfl
  · rw [ite_eq_right (by norm_num), bookCount_inv]
    have hp : ∀ ρ : ℂ, (ρ.im ≤ 0) ↔ (0 ≤ -1 * ρ.im) := by
      intro ρ; constructor <;> intro h <;> linarith
    simp only [hp, neg_one_mul]

/-- Book page 431, proof of Lemma 16.9: the count of display 3.95 with a zero at the upper
height counted in full, obtained from the half weighted count just above that height.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem full_count_bound (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) {t : ℝ} (ht : 1 ≤ t) :
    |(∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        (if ε * ρ.im = 0 then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ)) - bookMain q t| ≤
      bookError q t := by
  classical
  have hψ : (if ε = 1 then χ else χ⁻¹).IsPrimitive := by
    split_ifs
    · exact hχ
    · simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  obtain ⟨d, hd, hgap⟩ := exists_gap χ t
  set N := ∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        (if ε * ρ.im = 0 then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ) with hN
  have hev : ∀ᶠ u in 𝓝[>] t, |N - bookMain q u| ≤ bookError q u := by
    have hmem : Ioo t (t + d) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hmem] with u hu
    have hu1 : 1 ≤ u := ht.trans hu.1.le
    have he := hgap u hu.1 hu.2
    have hNu : N = bookCount (if ε = 1 then χ else χ⁻¹) u := by
      rw [bookCount_signed χ ε hε u, hN]
      have hfs : (stripZeros_finite χ u).toFinset = (stripZeros_finite χ t).toFinset := by
        ext ρ; simp [he]
      rw [hfs]
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hρ' := (stripZeros_finite χ t).mem_toFinset.mp (Finset.mem_filter.mp hρ).1
      have hle : ε * ρ.im ≤ t := by
        have h1 := (abs_le.mp hρ'.2.2.2)
        rcases hε with rfl | rfl <;> linarith [h1.1, h1.2]
      have hne : ε * ρ.im ≠ u := by linarith [hu.1]
      unfold halfWeight
      by_cases h0 : ε * ρ.im = 0
      · simp [h0]
      · simp [h0, hne]
    rw [hNu]
    exact book_zero_count _ hψ hu1
  have hcont1 : ContinuousAt (fun u ↦ bookMain q u) t := by
    unfold bookMain
    have hne : (q : ℝ) * t / (2 * Real.pi * Real.exp 1) ≠ 0 :=
      div_ne_zero (mul_ne_zero hq0 (by linarith)) (by positivity)
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have hcont2 : ContinuousAt (fun u ↦ bookError q u) t := by
    unfold bookError
    have hne : (q : ℝ) * t ≠ 0 := mul_ne_zero hq0 (by linarith)
    exact ContinuousAt.add (ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne))
      (by fun_prop)
  have hL : Tendsto (fun u ↦ |N - bookMain q u|) (𝓝[>] t) (𝓝 |N - bookMain q t|) :=
    ((continuousAt_const.sub hcont1).abs).tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun u ↦ bookError q u) (𝓝[>] t) (𝓝 (bookError q t)) :=
    hcont2.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hL hR hev

lemma strip_toFinset_filter (χ : DirichletCharacter ℂ q) {s T : ℝ} (hs : s ≤ T) :
    (stripZeros_finite χ s).toFinset =
      (stripZeros_finite χ T).toFinset.filter (fun ρ => |ρ.im| ≤ s) := by
  ext ρ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, stripZeros, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, b, c, d.trans hs⟩, d⟩
  · rintro ⟨⟨a, b, c, _⟩, d⟩; exact ⟨a, b, c, d⟩

/-- Book page 431, the Stieltjes measure dN of T in the proof of Lemma 16.9: the full count up
to height t is the count up to height 1 plus the multiplicities of the zeros with
1 < ε Im ρ ≤ t. -/
theorem full_count_split (χ : DirichletCharacter ℂ q) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    {t T : ℝ} (ht : 1 ≤ t) (htT : t ≤ T) :
    (∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        (if ε * ρ.im = 0 then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ)) =
      (∑ ρ ∈ (stripZeros_finite χ 1).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        (if ε * ρ.im = 0 then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ)) +
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 1 < ε * ρ.im),
        if ε * ρ.im ≤ t then (mult χ ρ : ℝ) else 0 := by
  classical
  rw [strip_toFinset_filter χ htT, strip_toFinset_filter χ (ht.trans htT),
    Finset.filter_filter, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  have habs : |ρ.im| = |ε * ρ.im| := by
    rcases hε with rfl | rfl <;> simp
  rw [habs]
  generalize ε * ρ.im = b
  generalize (mult χ ρ : ℝ) = m
  by_cases hb0 : 0 ≤ b
  · rw [abs_of_nonneg hb0]
    by_cases hb1 : b ≤ 1
    · have hbt : b ≤ t := hb1.trans ht
      have h3 : ¬ 1 < b := not_lt.mpr hb1
      simp [hb0, hb1, hbt, h3]
    · have h3 : 1 < b := not_le.mp hb1
      have hne : b ≠ 0 := by linarith
      by_cases hbt : b ≤ t
      · simp [hb0, hb1, hbt, h3, hne]
      · simp [hb0, hb1, hbt, h3]
  · have h3 : ¬ 1 < b := by linarith
    simp [hb0, h3]

end Count

/-! ### The Gaussian Mellin transform on the critical line -/

section Sampling
open ZeroCount1623 LeanLab.HelfgottArcs MiddleEnergy123.Decomp269a MiddleEnergy123.Decomp269b
  MiddleEnergy123.Decomp389b
open private gauss_mellin_hasDerivAt integrable_deriv_mellin_sq from
  LeanLab.HelfgottMajor.MiddleEnergy123

lemma gm_differentiableAt (δ : ℝ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    DifferentiableAt ℂ (gaussianMellin δ) s :=
  (gauss_mellin_hasDerivAt δ h0 h1).differentiableAt

lemma line_re (ε t : ℝ) : ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I).re = 1 / 2 := by
  simp

lemma gm_deriv_continuous (δ ε : ℝ) :
    Continuous (fun t : ℝ =>
      deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hd : DifferentiableOn ℂ (gaussianMellin δ) {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    fun s hs => (gm_differentiableAt δ hs.1 hs.2).differentiableWithinAt
  rw [continuous_iff_continuousAt]
  intro t
  have hmem : ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    show 0 < _ ∧ _ < 1
    rw [line_re]; constructor <;> norm_num
  have han : AnalyticAt ℂ (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) :=
    hd.analyticAt (hU.mem_nhds hmem)
  have hc := han.deriv.continuousAt
  exact ContinuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) hc
    (by fun_prop)

lemma gm_line_hasDerivAt (δ ε t : ℝ) :
    HasDerivAt (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I))
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) *
        ((ε : ℂ) * Complex.I)) t := by
  have hp : HasDerivAt (fun t : ℝ => (1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)
      ((ε : ℂ) * Complex.I) t := by
    have h1 := ((hasDerivAt_id t).const_mul ε).ofReal_comp
    have h2 := (h1.mul_const Complex.I).const_add (1 / 2 : ℂ)
    simpa using h2
  have hG : HasDerivAt (gaussianMellin δ)
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I))
      ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) :=
    (gm_differentiableAt δ (by rw [line_re]; norm_num) (by rw [line_re]; norm_num)).hasDerivAt
  have := HasDerivAt.scomp t hG hp
  convert this using 1
  · rfl
  · rw [smul_eq_mul, mul_comm]

/-- Derivative of the main term of the count, book page 432: the derivative of
T / 2π · log (qT / 2πe) is log (qT / 2π) / 2π. -/
lemma bookMain_hasDerivAt (q : ℕ) [NeZero q] {t : ℝ} (ht : 0 < t) :
    HasDerivAt (bookMain q) (1 / (2 * π) * log ((q : ℝ) * t / (2 * π))) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hne : (q : ℝ) * t / (2 * π * exp 1) ≠ 0 := by positivity
  have hl := (((hasDerivAt_id t).const_mul (q : ℝ)).div_const (2 * π * exp 1)).log hne
  have hm := ((hasDerivAt_id t).div_const (2 * π)).mul hl
  have hlog : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [show (q : ℝ) * t / (2 * π * exp 1) = (q : ℝ) * t / (2 * π) / exp 1 by field_simp,
      log_div (by positivity) (exp_ne_zero 1), log_exp]
  have hfun : bookMain q = fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1)) := by
    funext u; rfl
  have hm' : HasDerivAt (fun u : ℝ => u / (2 * π) * log ((q : ℝ) * u / (2 * π * exp 1)))
      (1 / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)) +
        t / (2 * π) * ((q : ℝ) * 1 / (2 * π * exp 1) / ((q : ℝ) * t / (2 * π * exp 1)))) t := hm
  rw [hfun]
  refine hm'.congr_deriv ?_
  rw [hlog]
  field_simp
  ring

/-- Book page 433, the application of Lemma 16.9 with y = 1 to the cut off function
f(t) = |Gδ(1/2 + it)| for t ≤ T0, in its corrected form: the boundary term |f(T0)| gχ(T0)
at the cutoff is kept. Both signs of the height are covered, ε = −1 through the conjugate
character as on book page 434. CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem signed_sampling_linear (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    signedMass χ δ T ε ≤
      1 / (2 * π) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  classical
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  set F : ℝ → ℂ := fun t => gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)
    with hF
  set F' : ℝ → ℂ := fun t =>
    deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I) *
      ((ε : ℂ) * Complex.I) with hF'
  have hF'norm : ∀ t, ‖F' t‖ =
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ := by
    intro t
    have : ‖((ε : ℂ) * Complex.I)‖ = 1 := by
      rcases hε with rfl | rfl <;> simp
    simp only [hF', norm_mul, this, mul_one]
  set Z : Finset ℂ := (stripZeros_finite χ T).toFinset.filter (fun ρ => 1 < ε * ρ.im) with hZ
  -- the signed mass as a finite sum over the ordinates
  have hmass : signedMass χ δ T ε = ∑ ρ ∈ Z, (mult χ ρ : ℝ) * ‖F (ε * ρ.im)‖ := by
    unfold signedMass
    have h1 := tsum_zeroIdx χ T (fun ρ => if 1 < ε * ρ.im then mellinMassTerm χ δ ρ else 0)
    have h2 : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ε * ρ.val.im} (fun ρ => mellinMassTerm χ δ ρ.val) ρ) =
        ∑' ρ : ZeroIdx χ T, (fun ρ : ℂ => if 1 < ε * ρ.im then mellinMassTerm χ δ ρ else 0) ρ.val := by
      apply tsum_congr
      intro ρ
      by_cases h : 1 < ε * ρ.val.im <;> simp [Set.indicator, h]
    rw [h2, h1, hZ, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hρ
    by_cases h : 1 < ε * ρ.im
    · rw [ite_eq_left h, ite_eq_left h]
      have hre := hzeros ρ hρ'.1 hρ'.2.1 hρ'.2.2.1 hρ'.2.2.2
      have hpt : (1 / 2 : ℂ) + ((ε * (ε * ρ.im) : ℝ) : ℂ) * Complex.I = ρ := by
        apply Complex.ext
        · simp [hre]
        · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
            Complex.ofReal_im, Complex.I_re]
          rw [← mul_assoc, hεsq]; simp
      simp only [hF, hpt]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
  have hγ : ∀ ρ ∈ Z, 1 < ε * ρ.im ∧ ε * ρ.im ≤ T := by
    intro ρ hρ
    rw [hZ, Finset.mem_filter] at hρ
    have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hρ.1
    refine ⟨hρ.2, ?_⟩
    have h1 := abs_le.mp hρ'.2.2.2
    rcases hε with rfl | rfl <;> linarith [h1.1, h1.2]
  have hM'c : ContinuousOn (fun t : ℝ => 1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))
      (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hne : (q : ℝ) * t / (2 * π) ≠ 0 := by positivity
    have hc : Continuous (fun t : ℝ => (q : ℝ) * t / (2 * π)) :=
      (continuous_const.mul continuous_id).div_const _
    exact (continuousAt_const.mul (hc.continuousAt.log hne)).continuousWithinAt
  have hEc : ContinuousOn (bookError q) (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hne : (q : ℝ) * t ≠ 0 := by positivity
    have hc : Continuous (fun t : ℝ => (q : ℝ) * t) := continuous_const.mul continuous_id
    have hfun : bookError q = fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389 := by
      funext u; rfl
    rw [hfun]
    exact ((continuousAt_const.mul (hc.continuousAt.log hne)).add
      continuousAt_const).continuousWithinAt
  have hE0 : ∀ t ∈ Icc 1 T, 0 ≤ bookError q t := by
    intro t ht
    unfold bookError
    have : 0 ≤ log ((q : ℝ) * t) := log_nonneg (by nlinarith [ht.1])
    linarith
  have hA := abel_norm_bound Z (fun ρ => ε * ρ.im) (fun ρ => (mult χ ρ : ℝ)) T hT hγ
    (fun ρ _ => Nat.cast_nonneg _) F F' (fun t => gm_line_hasDerivAt δ ε t)
    ((gm_deriv_continuous δ ε).mul continuous_const)
    (bookMain q) (fun t => 1 / (2 * π) * log ((q : ℝ) * t / (2 * π))) (bookError q)
    (∑ ρ ∈ (stripZeros_finite χ 1).toFinset.filter (fun ρ => 0 ≤ ε * ρ.im),
        (if ε * ρ.im = 0 then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ))
    (fun t ht => bookMain_hasDerivAt q (lt_of_lt_of_le zero_lt_one ht.1)) hM'c hEc hE0
    (fun t ht => by
      rw [hZ, ← full_count_split χ ε hε ht.1 ht.2]
      exact full_count_bound χ hχ ε hε ht.1)
  rw [hmass]
  refine hA.trans (le_of_eq ?_)
  have hi1 : (∫ t in (1 : ℝ)..T, ‖F t‖ * (1 / (2 * π) * log ((q : ℝ) * t / (2 * π)))) =
      1 / (2 * π) * ∫ t in (1 : ℝ)..T, ‖F t‖ * log ((q : ℝ) * t / (2 * π)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _; ring
  have hi2 : (∫ t in (1 : ℝ)..T, ‖F' t‖ * bookError q t) =
      ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hF'norm, bookError]
  have hF1 : F 1 = gaussianMellin δ ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I) := by
    simp only [hF, mul_one]
  rw [hi1, hi2, hF1]
  simp only [bookError, mul_one]
  ring
end Sampling

/-! ### The two Cauchy Schwarz steps of book pages 433 and 434

The three helpers are copied from the lab file SPLIT_positive_sampling_raw, where they are
proved; that file sits downstream of Decomp123 and cannot be imported here. -/

section CauchySchwarz
/-- A product of two `L²` functions is integrable by the AM GM inequality. -/
lemma integrable_mul_of_memLp_two {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    MeasureTheory.Integrable (fun x => f x * g x) (MeasureTheory.volume.restrict s) := by
  have hf2 : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdom : MeasureTheory.Integrable
      (fun x => (‖f x‖ ^ 2 + ‖g x‖ ^ 2) / 2) (MeasureTheory.volume.restrict s) :=
    (hf2.add hg2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  have hsq : 0 ≤ (‖f x‖ - ‖g x‖) ^ 2 := sq_nonneg _
  rw [norm_mul]
  nlinarith [norm_nonneg (f x), norm_nonneg (g x), hsq]

/-- The norm product of two `L²` functions is integrable. -/
lemma integrable_norm_mul_of_memLp_two {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    MeasureTheory.Integrable (fun x => ‖f x‖ * ‖g x‖) (MeasureTheory.volume.restrict s) := by
  have hf2 : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hg2 : MeasureTheory.Integrable (fun x => ‖g x‖ ^ 2) (MeasureTheory.volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdom : MeasureTheory.Integrable
      (fun x => (‖f x‖ ^ 2 + ‖g x‖ ^ 2) / 2) (MeasureTheory.volume.restrict s) :=
    (hf2.add hg2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    ((hf.aestronglyMeasurable.norm).mul (hg.aestronglyMeasurable.norm)) ?_
  filter_upwards with x
  have hsq : 0 ≤ (‖f x‖ - ‖g x‖) ^ 2 := sq_nonneg _
  have h1 : ‖‖f x‖ * ‖g x‖‖ = ‖f x‖ * ‖g x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [h1]
  nlinarith [norm_nonneg (f x), norm_nonneg (g x), hsq]

/-- Cauchy Schwarz in integral form: `∫ f g ≤ √(∫ f²) √(∫ g²)` on a set. -/
lemma setIntegral_mul_le_sqrt {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict s))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict s)) :
    ∫ x in s, f x * g x ≤ sqrt (∫ x in s, f x ^ 2) * sqrt (∫ x in s, g x ^ 2) := by
  have hHolder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := MeasureTheory.volume.restrict s) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (by simpa using hf) (by simpa using hg)
  have hmono : (∫ x in s, f x * g x) ≤ ∫ x in s, ‖f x‖ * ‖g x‖ := by
    refine MeasureTheory.integral_mono_ae (integrable_mul_of_memLp_two hf hg)
      (integrable_norm_mul_of_memLp_two hf hg) (Filter.Eventually.of_forall (fun x => ?_))
    refine (le_abs_self (f x * g x)).trans_eq ?_
    simp only [abs_mul, Real.norm_eq_abs]
  refine hmono.trans (hHolder.trans (le_of_eq ?_))
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have hsq1 : (∫ a in s, ‖f a‖ ^ (2 : ℝ)) = ∫ x in s, f x ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [← h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hsq2 : (∫ a in s, ‖g a‖ ^ (2 : ℝ)) = ∫ x in s, g x ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [← h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [hsq1, hsq2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]



/-- Cauchy Schwarz on the interval from 1 to T for continuous functions, book page 433. -/
lemma cs_interval {f w : ℝ → ℝ} {T : ℝ} (hT : 1 ≤ T) (hf : ContinuousOn f (Icc 1 T))
    (hw : ContinuousOn w (Icc 1 T)) :
    (∫ t in (1 : ℝ)..T, f t * w t) ≤
      sqrt (∫ t in (1 : ℝ)..T, f t ^ 2) * sqrt (∫ t in (1 : ℝ)..T, w t ^ 2) := by
  have hmem : ∀ {u : ℝ → ℝ}, ContinuousOn u (Icc 1 T) →
      MemLp u 2 (volume.restrict (Ioc (1 : ℝ) T)) := by
    intro u hu
    have haesm : AEStronglyMeasurable u (volume.restrict (Ioc (1 : ℝ) T)) :=
      (hu.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    rw [memLp_two_iff_integrable_sq_norm haesm]
    have : IntegrableOn (fun t => ‖u t‖ ^ 2) (Icc 1 T) :=
      (hu.norm.pow 2).integrableOn_compact isCompact_Icc
    exact this.mono_set Ioc_subset_Icc_self
  simp only [intervalIntegral.integral_of_le hT]
  exact setIntegral_mul_le_sqrt (hmem hf) (hmem hw)
end CauchySchwarz

section Assembly
open ZeroCount1623 LeanLab.HelfgottArcs MiddleEnergy123.Decomp269a MiddleEnergy123.Decomp269b
  MiddleEnergy123.Decomp389b
open private gauss_mellin_hasDerivAt integrable_deriv_mellin_sq from
  LeanLab.HelfgottMajor.MiddleEnergy123

lemma gm_line_continuous (δ ε : ℝ) :
    Continuous (fun t : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)) :=
  continuous_iff_continuousAt.mpr (fun t => (gm_line_hasDerivAt δ ε t).continuousAt)

/-- Book pages 433 and 434, display 16.26 before the scalar weight estimates, in its corrected
form: the statement of MiddleEnergy123 signed_sampling_raw plus the boundary term
|f(T0)| gχ(T0) at the cutoff, which the printed display drops.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem signed_sampling_raw_cutoff (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    signedMass χ δ T ε ≤
      sqrt (lineEnergy δ ε) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) +
      sqrt (derivativeEnergy δ ε) *
        sqrt (∫ t in (1 : ℝ)..T, (0.15 * log ((q : ℝ) * t) + 3.389) ^ 2) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I)‖ *
        (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hlin := signed_sampling_linear q χ hχ δ T ε hε hT hzeros
  have hLc : ContinuousOn (fun t : ℝ => log ((q : ℝ) * t / (2 * π))) (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hne : (q : ℝ) * t / (2 * π) ≠ 0 := by positivity
    have hc : Continuous (fun t : ℝ => (q : ℝ) * t / (2 * π)) :=
      (continuous_const.mul continuous_id).div_const _
    exact (hc.continuousAt.log hne).continuousWithinAt
  have hEc : ContinuousOn (fun t : ℝ => 0.15 * log ((q : ℝ) * t) + 3.389) (Icc 1 T) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hne : (q : ℝ) * t ≠ 0 := by positivity
    have hc : Continuous (fun t : ℝ => (q : ℝ) * t) := continuous_const.mul continuous_id
    exact ((continuousAt_const.mul (hc.continuousAt.log hne)).add
      continuousAt_const).continuousWithinAt
  -- the main term
  have hcs1 := cs_interval hT (gm_line_continuous δ ε).norm.continuousOn hLc
  have hint1 : Integrable (fun t : ℝ =>
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ ^ 2) :=
    (integrable_mellin_sq δ).comp_mul_left' hε0
  have hmono1 : (∫ t in (1 : ℝ)..T,
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      lineEnergy δ ε := by
    rw [intervalIntegral.integral_of_le hT, lineEnergy]
    refine setIntegral_mono_set hint1.integrableOn ?_ ?_
    · filter_upwards with x using by positivity
    · exact Filter.Eventually.of_forall (fun x hx => lt_trans zero_lt_one hx.1)
  have h1 : 1 / (2 * π) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) ≤
      sqrt (lineEnergy δ ε) / (2 * π) *
        sqrt (∫ t in (1 : ℝ)..T, log ((q : ℝ) * t / (2 * π)) ^ 2) := by
    have h2 := hcs1.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hmono1) (sqrt_nonneg _))
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    refine h3.trans (le_of_eq ?_)
    ring
  -- the error term
  have hcs2 := cs_interval hT (gm_deriv_continuous δ ε).norm.continuousOn hEc
  have hint2 : Integrable (fun t : ℝ =>
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ ^ 2) :=
    (integrable_deriv_mellin_sq δ).comp_mul_left' hε0
  have hmono2 : (∫ t in (1 : ℝ)..T,
      ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + ((ε * t : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      derivativeEnergy δ ε := by
    rw [intervalIntegral.integral_of_le hT, derivativeEnergy]
    refine setIntegral_mono_set hint2.integrableOn ?_ ?_
    · filter_upwards with x using by positivity
    · exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have h2 := hcs2.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hmono2) (sqrt_nonneg _))
  linarith

/-- Book page 434, the corrected display 16.26 with the two scalar weight estimates applied.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem signed_sampling_bound_cutoff (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hT : 1 ≤ T)
    (hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    signedMass χ δ T ε ≤
      sqrt (lineEnergy δ ε) / (2 * π) * sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) +
      sqrt (derivativeEnergy δ ε) *
        (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T +
      2.15581 * (0.15 * log (q : ℝ) + 3.389) +
      2.15581 * (0.15 * log ((q : ℝ) * T) + 3.389) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hM := mul_le_mul_of_nonneg_left
    (main_weight_root_bound (q : ℝ) T hq hT hlarge)
    (by positivity : 0 ≤ sqrt (lineEnergy δ ε) / (2 * π))
  have hE := mul_le_mul_of_nonneg_left
    (error_weight_root_bound (q : ℝ) T hq hT hlarge)
    (sqrt_nonneg (derivativeEnergy δ ε))
  have hn1 := MiddleEnergy123.Decomp389a.mellin_critical_norm_le δ
    ((1 / 2 : ℂ) + (ε : ℂ) * Complex.I) (by simp)
    HalfMoment389.gaussian_half_moment_bound
  have hn2 := MiddleEnergy123.Decomp389a.mellin_critical_norm_le δ
    ((1 / 2 : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I) (line_re ε T)
    HalfMoment389.gaussian_half_moment_bound
  have hl1 : 0 ≤ log (q : ℝ) := log_nonneg hq1
  have hl2 : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hb1 := mul_le_mul_of_nonneg_right hn1 (by linarith : 0 ≤ 0.15 * log (q : ℝ) + 3.389)
  have hb2 := mul_le_mul_of_nonneg_right hn2
    (by linarith : 0 ≤ 0.15 * log ((q : ℝ) * T) + 3.389)
  have hraw := signed_sampling_raw_cutoff q χ hχ δ T ε hε hT hzeros
  calc
    _ ≤ _ := hraw
    _ ≤ _ := add_le_add (add_le_add (add_le_add hM hE) hb1) hb2
    _ = _ := by ring

/-- The gap between the coefficient of Lemma 16.10 and the older page 40 coefficient, which
absorbs the boundary term at the cutoff. Only arithmetic. -/
lemma coefficient_gap :
    sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog + 0.647 ≤
      sqrt Sec45.nTwo + sqrt Sec45.nLog := by
  have hs1 := Sec45.sqrt_pi_gt
  have hs2 := Sec45.sqrt_pi_lt
  have hs0 : 0 < sqrt π := by positivity
  have ha1 := Sec45.sqrt_nTwo_gt
  have hK := BookP1617.K_bds.1
  have hb : (0.8 : ℝ) ≤ sqrt Sec45.nLog := by
    have hh := MiddleEnergy123.Decomp389c.middle_constant_ge
    have hprod : 0 ≤ log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo :=
      mul_nonneg (by linarith) (sqrt_nonneg _)
    linarith
  have hdiv : sqrt Sec45.nTwo / sqrt π ≤ 0.57 * sqrt Sec45.nTwo := by
    rw [div_le_iff₀ hs0]
    nlinarith
  nlinarith

/-- Book Lemma 16.10 in the form of MiddleEnergy123 middle_mass_bound, the same statement,
proved from the corrected display 16.26: the boundary term at the cutoff is absorbed by the
gap between the book coefficients and the older page 40 coefficients. This proof does not
use MiddleEnergy123 signed_sampling_raw. CONDITIONAL ON ZeroCount1623.book_zero_count only. -/
theorem middle_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    middleMass χ δ T ≤
      (sqrt Sec45.nTwo + sqrt Sec45.nLog) * sqrt T * log (q * T) +
      (17.21 * sqrt Sec45.nLog - log (2 * π * sqrt (exp 1)) * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.5 * log q + 17.7) := by
  by_cases hlarge : 2 * π * exp 2 ≤ (q : ℝ) * T
  swap
  · exact MiddleEnergy123.Decomp389c.small_middle_mass_bound q χ hχ δ T hT
      (le_of_not_ge hlarge) hzeros
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT0 : 0 < (q : ℝ) * T := mul_pos hq0 hT0
  have hsπ : 0 < sqrt π := by positivity
  have hsT : 1 ≤ sqrt T := by
    rw [show (1 : ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hT
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg hq
  have hlog : 0 ≤ log ((q : ℝ) * T) := log_nonneg (by nlinarith)
  have hC : 0 < 2 * π * sqrt (exp 1) := by positivity
  have he : sqrt (exp 1) ≤ exp 2 := by
    have hs : sqrt (exp 1) ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num, by linarith [exp_one_lt_three]⟩
    have hh : (2 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    exact hs.trans hh
  have hshift : 0 ≤ log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) := by
    apply log_nonneg
    rw [le_div_iff₀ hC]
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * π)
    nlinarith
  have henergy := gaussian_line_energy_bound δ
  have hderiv := gaussian_derivative_energy_bound δ
  have hE : (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) ≤
      sqrt Sec45.nTwo / sqrt π := by
    calc
      _ ≤ (2 * sqrt π * sqrt Sec45.nTwo) / (2 * π) :=
        div_le_div_of_nonneg_right henergy (by positivity)
      _ = _ := by
        rw [show 2 * π = 2 * sqrt π * sqrt π by nlinarith [sq_sqrt pi_pos.le]]
        field_simp
  have hp := signed_sampling_bound_cutoff q χ hχ δ T 1 (Or.inl rfl) hT hlarge hzeros
  have hn := signed_sampling_bound_cutoff q χ hχ δ T (-1) (Or.inr rfl) hT hlarge hzeros
  have hsum : middleMass χ δ T ≤
      (sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1))) / (2 * π) * (sqrt T *
        log ((q : ℝ) * T / (2 * π * sqrt (exp 1)))) +
      (sqrt (derivativeEnergy δ 1) + sqrt (derivativeEnergy δ (-1))) *
        ((0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T) +
      2 * 2.15581 * (0.15 * log (q : ℝ) + 3.389) +
      2 * 2.15581 * (0.15 * log ((q : ℝ) * T) + 3.389) := by
    rw [middle_mass_signed_split χ δ T]
    calc
      _ ≤ _ := add_le_add hp hn
      _ = _ := by ring
  have hX : 0 ≤ sqrt T * log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) :=
    mul_nonneg (by linarith) hshift
  have hY : 0 ≤ (0.15 * log ((q : ℝ) * T) + 3.242) * sqrt T :=
    mul_nonneg (by linarith) (by linarith)
  have hmain : middleMass χ δ T ≤
      (sqrt Sec45.nTwo / sqrt π + 0.3 * sqrt π * sqrt Sec45.nLog) * (sqrt T * log ((q : ℝ) * T)) +
      (6.484 * sqrt π * sqrt Sec45.nLog -
        log (2 * π * sqrt (exp 1)) / sqrt π * sqrt Sec45.nTwo) * sqrt T +
      2.15581 * (0.3 * log (q : ℝ) + 6.778) +
      2.15581 * (0.3 * log ((q : ℝ) * T) + 6.778) := by
    have h1 := mul_le_mul_of_nonneg_right hE hX
    have h2 := mul_le_mul_of_nonneg_right hderiv hY
    have hld : log ((q : ℝ) * T / (2 * π * sqrt (exp 1))) =
        log ((q : ℝ) * T) - log (2 * π * sqrt (exp 1)) := log_div hqT0.ne' hC.ne'
    rw [hld] at h1 hsum
    refine (hsum.trans (add_le_add (add_le_add (add_le_add h1 h2) le_rfl) le_rfl)).trans
      (le_of_eq ?_)
    ring
  obtain ⟨_, hB⟩ := book_coefficients_le
  have hgap := coefficient_gap
  have hrl : 0 ≤ sqrt T * log ((q : ℝ) * T) := mul_nonneg (by linarith) hlog
  have ha := mul_le_mul_of_nonneg_right hgap hrl
  have hb := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ sqrt T)
  have hc : log ((q : ℝ) * T) ≤ sqrt T * log ((q : ℝ) * T) := by nlinarith
  have hcast : log ((q : ℝ) * T) = log (q * T) := rfl
  nlinarith

end Assembly

end LeanLab.HelfgottMajor.SamplingSplit123
