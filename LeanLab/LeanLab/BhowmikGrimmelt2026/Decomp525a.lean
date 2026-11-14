/-
Cycle free supply for P0029 pages 26 and 27, displays 7.7 and 7.8.
Proof copies from tasks328 retain the exact changing smoothing scale.
The remaining multi denominator estimates are OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ApproximationError
import LeanLab.BhowmikGrimmelt2026.WeightedVariation261
import LeanLab.BhowmikGrimmelt2026.Farey
import LeanLab.BhowmikGrimmelt2026.WeightedFamily261
import LeanLab.BhowmikGrimmelt2026.PartialSums261
import LeanLab.BhowmikGrimmelt2026.SharpSupported261

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Major arc part of the error coefficient in the proof of 7.8, pages 26 and 27. -/
noncomputable def majorError150 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then
    Sphi ϕ N α ^ 2 * (1 - bRhat G ((X : ℝ) ^ ϑ)
      (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α)) else 0

/-- Minor arc part of the same coefficient. The smoothing still depends on N. -/
noncomputable def minorError150 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
    Sphi ϕ N α ^ 2 * (1 - bRhat G ((X : ℝ) ^ ϑ)
      (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))

/-- The smoothed square with a fixed multiplier, restricted to a measurable arc set. -/
noncomputable def arcSquare525 (ϕ : ℝ → ℝ) (V : ℝ → ℂ) (s : Set ℝ)
    (j : ℕ) : ℝ → ℂ := s.indicator (fun α => Sphi ϕ j α ^ 2 * V α)


/-- A continuous multiplier and a measurable arc restriction give the required L2 functions. -/
theorem arcSquare_memLp525 (ϕ : ℝ → ℝ) {V : ℝ → ℂ} (hV : Continuous V)
    {s : Set ℝ} (hs : MeasurableSet s) (j : ℕ) :
    MemLp (arcSquare525 ϕ V s j) 2 (volume.restrict (Set.Ioc 0 1)) := by
  have hc : Continuous (fun α => Sphi ϕ j α ^ 2 * V α) :=
    ((continuous_Sphi ϕ j).pow 2).mul hV
  have hi : Integrable (fun α => ‖Sphi ϕ j α ^ 2 * V α‖ ^ 2)
      (volume.restrict (Set.Ioc 0 1)) :=
    ((hc.norm.pow 2).continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  exact ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hi).indicator
    hs.nullMeasurableSet


/-- The Fourier multiplier has positive scales under the leaf hypotheses. -/
theorem continuous_error_multiplier525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) {η : ℝ} (hη : 0 < η) :
    Continuous (fun α => (1 : ℂ) - bRhat G ((X : ℝ) ^ ϑ)
      (fun q => η * X * q / (X : ℝ) ^ ϑ) α) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊,
      0 < η * X * q / (X : ℝ) ^ ϑ := by
    intro q hq
    have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  exact continuous_const.sub (continuous_bRhat hG.supp hG.even _ _ hT)


/-- Finite rational central terms from display 7.7 on the unit frequency interval.
The integer representatives range from negative q to two q.
Under the scale hypotheses this includes every central term on that interval. -/
noncomputable def nearTransform525 (G : ℝ → ℝ) (X : ℕ) (R η α : ℝ) : ℂ := by
  classical
  exact ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
    ∑ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
      if |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X) then
        GThat G (η * X * q / R) (α - (a : ℝ) / q) else 0


/-- Every central rational on the unit interval occurs in the finite representative sum. -/
theorem majorArc_center_in_sum525 {X : ℕ} {R α : ℝ}
    (hX : 0 < (X : ℝ)) (hRX : R ≤ X) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hm : MajorArc X R α) :
    ∃ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ∃ a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1),
        |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X) := by
  classical
  obtain ⟨q, hq, hqR, a, hcop, hclose⟩ := hm
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hw : R / ((q : ℝ) * X) ≤ 1 := by
    apply (div_le_one (mul_pos hqp hX)).mpr
    nlinarith
  have hd := abs_le.mp (hclose.trans hw)
  have halow : (-1 : ℝ) ≤ (a : ℝ) / q := by linarith [hα.1]
  have haup : (a : ℝ) / q ≤ 2 := by linarith [hα.2]
  have halow' : -(q : ℝ) ≤ (a : ℝ) := by
    have hh := (le_div_iff₀ hqp).mp halow
    linarith
  have haup' : (a : ℝ) ≤ 2 * (q : ℝ) := (div_le_iff₀ hqp).mp haup
  refine ⟨q, Finset.mem_Icc.mpr ⟨hq, Nat.le_floor hqR⟩, a, ?_, hclose⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hcop⟩
  · exact_mod_cast halow'
  · exact_mod_cast haup'


/-- Reduced integer fractions with positive denominators have unique representatives. -/
theorem signed_fraction_unique525 {q r : ℕ} {a b : ℤ}
    (hq : 0 < q) (hr : 0 < r) (ha : Int.gcd a q = 1) (hb : Int.gcd b r = 1)
    (heq : (a : ℝ) / q = (b : ℝ) / r) : q = r ∧ a = b := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hcross : a * (r : ℤ) = b * (q : ℤ) := by
    exact_mod_cast (div_eq_div_iff hqp.ne' hrp.ne').mp heq
  have hcrossNat : a.natAbs * r = b.natAbs * q := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hcross
  have hac : Nat.Coprime a.natAbs q := by simpa [Nat.Coprime, Int.gcd] using ha
  have hbc : Nat.Coprime b.natAbs r := by simpa [Nat.Coprime, Int.gcd] using hb
  have hqr : q ∣ r := hac.symm.dvd_mul_left.mp (by rw [hcrossNat]; exact ⟨b.natAbs, by ring⟩)
  have hrq : r ∣ q := hbc.symm.dvd_mul_left.mp (by rw [← hcrossNat]; exact ⟨a.natAbs, by ring⟩)
  have hden : q = r := Nat.dvd_antisymm hqr hrq
  subst r
  refine ⟨rfl, ?_⟩
  exact mul_right_cancel₀ (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0) hcross


/-- Distinct central reduced rationals cannot overlap when twice R squared is below X. -/
theorem near_rational_unique525 {X R α : ℝ} (hX : 0 < X) (hR : 0 ≤ R)
    (hsep : 2 * R ^ 2 < X) {q r : ℕ} {a b : ℤ}
    (hq : 0 < q) (hr : 0 < r) (hqR : (q : ℝ) ≤ R) (hrR : (r : ℝ) ≤ R)
    (ha : Int.gcd a q = 1) (hb : Int.gcd b r = 1)
    (hcloseq : |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X))
    (hcloser : |α - (b : ℝ) / r| ≤ R / ((r : ℝ) * X)) : q = r ∧ a = b := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  by_cases heq : (a : ℝ) / q = (b : ℝ) / r
  · exact signed_fraction_unique525 hq hr ha hb heq
  have hcross : a * (r : ℤ) ≠ b * (q : ℤ) := by
    intro hc
    apply heq
    apply (div_eq_div_iff hqp.ne' hrp.ne').mpr
    exact_mod_cast hc
  have hlo := rational_separation hq hr hcross
  have hhi : |(a : ℝ) / q - (b : ℝ) / r| ≤
      R / ((q : ℝ) * X) + R / ((r : ℝ) * X) := by
    calc
      _ ≤ |(a : ℝ) / q - α| + |α - (b : ℝ) / r| := abs_sub_le _ _ _
      _ ≤ _ := by rw [abs_sub_comm ((a : ℝ) / q) α]; exact add_le_add hcloseq hcloser
  have hid : R / ((q : ℝ) * X) + R / ((r : ℝ) * X) =
      (R * ((q : ℝ) + r) / X) / ((q : ℝ) * r) := by
    field_simp
    <;> ring
  have hsmall : R * ((q : ℝ) + r) / X < 1 := by
    apply (div_lt_one hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hqR hR, mul_le_mul_of_nonneg_left hrR hR]
  have hlt : R / ((q : ℝ) * X) + R / ((r : ℝ) * X) < 1 / ((q : ℝ) * r) := by
    rw [hid]
    exact div_lt_div_of_pos_right hsmall (mul_pos hqp hrp)
  exact False.elim ((not_lt_of_ge (hlo.trans hhi)) hlt)


/-- On a central arc the finite transform sum has exactly the selected rational term. -/
theorem nearTransform_eq525 {G : ℝ → ℝ} {X : ℕ} {R η α : ℝ}
    (hX : 0 < (X : ℝ)) (hR : 0 ≤ R) (hsep : 2 * R ^ 2 < X)
    {q : ℕ} {a : ℤ} (hqmem : q ∈ Finset.Icc 1 ⌊R⌋₊)
    (hamem : a ∈ (Finset.Icc (-(q : ℤ)) (2 * (q : ℤ))).filter (fun a => Int.gcd a q = 1))
    (hclose : |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)) :
    nearTransform525 G X R η α = GThat G (η * X * q / R) (α - (a : ℝ) / q) := by
  classical
  have hq := Finset.mem_Icc.mp hqmem
  have ha := Finset.mem_filter.mp hamem
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hR)
  unfold nearTransform525
  rw [Finset.sum_eq_single q]
  · rw [Finset.sum_eq_single a]
    · simp only [if_pos hclose]
    · intro b hb hba
      have hbn := Finset.mem_filter.mp hb
      have hnot : ¬ |α - (b : ℝ) / q| ≤ R / ((q : ℝ) * X) := by
        intro hbclose
        have hu := near_rational_unique525 hX hR hsep
          (by omega : 0 < q) (by omega : 0 < q) hqR hqR ha.2 hbn.2 hclose hbclose
        exact hba hu.2.symm
      exact if_neg hnot
    · intro hn
      exact False.elim (hn hamem)
  · intro r hr hrq
    apply Finset.sum_eq_zero
    intro b hb
    have hrn := Finset.mem_Icc.mp hr
    have hbn := Finset.mem_filter.mp hb
    have hrR : (r : ℝ) ≤ R := (Nat.cast_le.mpr hrn.2).trans (Nat.floor_le hR)
    have hnot : ¬ |α - (b : ℝ) / r| ≤ R / ((r : ℝ) * X) := by
      intro hbclose
      have hu := near_rational_unique525 hX hR hsep
        (by omega : 0 < q) (by omega : 0 < r) hqR hrR ha.2 hbn.2 hclose hbclose
      exact hrq hu.1.symm
    exact if_neg hnot
  · intro hn
    exact False.elim (hn hqmem)


/-- A single central term has a Poisson error bounded by eta squared at every allowed scale.
The decay exponent depends on the fixed positive theta. -/
theorem central_scale_tail525 {x ϑ η q : ℝ} (hx : 1 ≤ x) (hϑ : 0 < ϑ)
    (hη : 0 < η) (hq : 1 ≤ q) (hscale : 10 * (x ^ ϑ) ^ 2 ≤ η * x) :
    (η * x * q / x ^ ϑ) ^ (-(2 / ϑ)) ≤ η ^ 2 := by
  have hxp : 0 < x := by linarith
  have hR1 : 1 ≤ x ^ ϑ := Real.one_le_rpow hx hϑ.le
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hRT : x ^ ϑ ≤ η * x * q / x ^ ϑ := by
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ η * x), sq_nonneg (x ^ ϑ)]
  have hinv : 1 / x ≤ η := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith [sq_nonneg (x ^ ϑ - 1)]
  have hpow : (x ^ ϑ) ^ (-(2 / ϑ)) = (1 / x) ^ 2 := by
    rw [← Real.rpow_mul hxp.le]
    have he : ϑ * (-(2 / ϑ)) = -(2 : ℝ) := by field_simp <;> ring
    rw [he, Real.rpow_neg hxp.le, Real.rpow_two]
    simp [one_div, inv_pow]
  calc
    _ ≤ (x ^ ϑ) ^ (-(2 / ϑ)) :=
      Real.rpow_le_rpow_of_nonpos hRp hRT (neg_nonpos.mpr (div_nonneg (by norm_num) hϑ.le))
    _ = (1 / x) ^ 2 := hpow
    _ ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2


/-- The selected discrete transform has a uniform quadratic central error.
This estimates one term and does not discard the off rational remainder. -/
theorem central_single_bound525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x η q β : ℝ, 1 ≤ x → 0 < η → 1 ≤ q →
      10 * (x ^ ϑ) ^ 2 ≤ η * x → |β| ≤ x ^ ϑ / (q * x) →
      ‖GThat G (η * x * q / x ^ ϑ) β - 1‖ ≤ D * η ^ 2 := by
  obtain ⟨D, hD, hcentral⟩ := GThat_central hG (2 / ϑ)
  refine ⟨8 * Real.pi ^ 2 + D, by positivity, ?_⟩
  intro x η q β hx hη hq hscale hclose
  have hxp : 0 < x := by linarith
  have hqp : 0 < q := by linarith
  have hR1 : 1 ≤ x ^ ϑ := Real.one_le_rpow hx hϑ.le
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  let T : ℝ := η * x * q / x ^ ϑ
  have hTp : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := by
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ η * x), sq_nonneg (x ^ ϑ - 1)]
  have htβ : T * intDist β ≤ η := by
    calc
      _ ≤ T * |β| := mul_le_mul_of_nonneg_left (by simpa using intDist_le_abs_sub β 0) hTp.le
      _ ≤ T * (x ^ ϑ / (q * x)) := mul_le_mul_of_nonneg_left hclose hTp.le
      _ = η := by dsimp [T]; field_simp <;> ring
  have htβ0 : 0 ≤ T * intDist β := mul_nonneg hTp.le (intDist_nonneg β)
  have hsq := pow_le_pow_left₀ htβ0 htβ 2
  have htail := central_scale_tail525 hx hϑ hη hq hscale
  have hc := hcentral T β hT1
  change T ^ (-(2 / ϑ)) ≤ η ^ 2 at htail
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 8 * Real.pi ^ 2),
    mul_le_mul_of_nonneg_left htail hD.le]


/-- The finite central transform is measurable for positive scales. -/
theorem measurable_nearTransform525 {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) {X : ℕ}
    (hX : 0 < (X : ℝ)) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    Measurable (nearTransform525 G X R η) := by
  classical
  unfold nearTransform525
  apply Finset.measurable_sum
  intro q hq
  apply Finset.measurable_sum
  intro a ha
  have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hT : 0 < η * X * q / R := by positivity
  have hc : Continuous (fun α : ℝ => GThat G (η * X * q / R) (α - (a : ℝ) / q)) :=
    (continuous_GThat hsupp hT).comp (continuous_id.sub continuous_const)
  exact hc.measurable.ite
    (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
    measurable_const


/-- On the unit interval the selected central sum has a uniform quadratic error. -/
theorem nearTransform_bound525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      MajorArc X ((X : ℝ) ^ ϑ) α →
      ‖1 - nearTransform525 G X ((X : ℝ) ^ ϑ) η α‖ ≤ D * η ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := central_single_bound525 hG hϑ
  refine ⟨D, hD, ?_⟩
  intro X hX η hη hη1 hscale α hα hm
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := by positivity
  have hηX : η * X ≤ (X : ℝ) := by nlinarith
  have hRX : (X : ℝ) ^ ϑ ≤ X := by nlinarith [sq_nonneg ((X : ℝ) ^ ϑ - 1)]
  have hsep : 2 * ((X : ℝ) ^ ϑ) ^ 2 < X := by nlinarith
  obtain ⟨q, hq, a, ha, hclose⟩ := majorArc_center_in_sum525 hXp hRX hα hm
  rw [nearTransform_eq525 hXp hRp.le hsep hq ha hclose, norm_sub_rev]
  exact hbound X η q (α - (a : ℝ) / q) hX1 hη
    (by exact_mod_cast (Finset.mem_Icc.mp hq).1) hscale hclose


/-- The central transform times a smoothed square is in L2 on the unit interval. -/
theorem nearSquare_memLp525 (ϕ : ℝ → ℝ) {G : ℝ → ℝ}
    (hsupp : Function.support G ⊆ Set.Icc (-2) 2) {X : ℕ}
    (hX : 0 < (X : ℝ)) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (N : ℕ) :
    MemLp (fun α => Sphi ϕ N α ^ 2 * nearTransform525 G X R η α)
      2 (volume.restrict (Set.Ioc 0 1)) := by
  classical
  simp_rw [nearTransform525, Finset.mul_sum]
  apply memLp_finsetSum
  intro q hq
  apply memLp_finsetSum
  intro a ha
  have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hT : 0 < η * X * q / R := by positivity
  let V : ℝ → ℂ := fun α => GThat G (η * X * q / R) (α - (a : ℝ) / q)
  let s : Set ℝ := {α | |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X)}
  have hV : Continuous V := (continuous_GThat hsupp hT).comp (continuous_id.sub continuous_const)
  have hs : MeasurableSet s :=
    (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  have heq : (fun α => Sphi ϕ N α ^ 2 *
      (if |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X) then V α else 0)) =
        arcSquare525 ϕ V s N := by
    funext α
    by_cases hm : α ∈ s <;> simp [arcSquare525, Set.indicator, s] at hm ⊢ <;>
      simp_all
  rw [show (fun α => Sphi ϕ N α ^ 2 *
      (if |α - (a : ℝ) / q| ≤ R / ((q : ℝ) * X) then
        GThat G (η * X * q / R) (α - (a : ℝ) / q) else 0)) =
      arcSquare525 ϕ V s N from heq]
  exact arcSquare_memLp525 ϕ hV hs N


/-- The major coefficient retaining only its central reduced rational contribution. -/
noncomputable def majorCore525 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ := by
  classical
  exact ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then
    Sphi ϕ N α ^ 2 * (1 - nearTransform525 G X ((X : ℝ) ^ ϑ) η α) *
      ee (-(N * α)) else 0


/-- The remaining major coefficient after subtracting the central contribution.
It retains the full off rational and Poisson remainder. -/
noncomputable def majorTail525 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  majorError150 ϕ G X N ϑ η - majorCore525 ϕ G X N ϑ η


/-- The central major coefficient is an integral of an interval integrable function. -/
theorem majorCore_integrable525 (ϕ : ℝ → ℝ) {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ) {η : ℝ} (hη : 0 < η) :
    IntervalIntegrable
      ({α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator (fun α =>
        Sphi ϕ N α ^ 2 * (1 - nearTransform525 G X ((X : ℝ) ^ ϑ) η α) *
          ee (-(N * α)))) volume 0 1 := by
  classical
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  have hS : MemLp (fun α => Sphi ϕ N α ^ 2) 2 (volume.restrict (Set.Ioc 0 1)) := by
    simpa [arcSquare525] using
      (arcSquare_memLp525 ϕ (V := fun _ => 1) continuous_const (s := Set.univ) MeasurableSet.univ N)
  have hnear := nearSquare_memLp525 ϕ hG.supp hXp hRp hη N
  have hi : IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 -
      Sphi ϕ N α ^ 2 * nearTransform525 G X ((X : ℝ) ^ ϑ) η α) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((hS.sub hnear).integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hie := hi.mul_continuousOn he.continuousOn
  have hs := measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)
  have hm : IntervalIntegrable
      ({α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator (fun α =>
        (Sphi ϕ N α ^ 2 - Sphi ϕ N α ^ 2 * nearTransform525 G X ((X : ℝ) ^ ϑ) η α) *
          ee (-(N * α)))) volume 0 1 := ⟨hie.1.indicator hs, hie.2.indicator hs⟩
  have heq : (fun α => Sphi ϕ N α ^ 2 *
      (1 - nearTransform525 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))) =
      (fun α => (Sphi ϕ N α ^ 2 -
        Sphi ϕ N α ^ 2 * nearTransform525 G X ((X : ℝ) ^ ϑ) η α) * ee (-(N * α))) := by
    funext α
    ring
  rw [heq]
  exact hm


/-- The major remainder is exactly the off rational integral after central subtraction. -/
theorem majorTail_eq_integral525 (ϕ : ℝ → ℝ) {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ) {η : ℝ} (hη : 0 < η) :
    majorTail525 ϕ G X N ϑ η =
      ∫ α in (0 : ℝ)..1,
        {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator (fun α =>
          Sphi ϕ N α ^ 2 *
            (nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α := by
  classical
  let P : ℝ → Prop := MajorArc X ((X : ℝ) ^ ϑ)
  have hs : MeasurableSet {α | P α} := measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)
  have hmask (u : ℝ → ℂ) : {α | P α}.indicator u = (fun α => if P α then u α else 0) := by
    funext α
    by_cases hm : P α <;> simp [Set.indicator, hm]
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hf := arcSquare_memLp525 ϕ (continuous_error_multiplier525 hG hX ϑ hη) hs N
  have hi : IntervalIntegrable
      (fun α => if P α then Sphi ϕ N α ^ 2 *
        (1 - bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
          ee (-(N * α)) else 0) volume 0 1 := by
    have hz : IntervalIntegrable (arcSquare525 ϕ
        (fun α => 1 - bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α)
        {α | P α} N) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
        (hf.integrable (by norm_num : (1 : ENNReal) ≤ 2))
    convert hz.mul_continuousOn he.continuousOn using 1
    funext α
    by_cases hm : P α <;> simp [arcSquare525, Set.indicator, hm]
  have hc := majorCore_integrable525 ϕ hG hX N ϑ hη
  rw [hmask] at hc
  unfold majorTail525 majorError150 majorCore525
  rw [← intervalIntegral.integral_sub hi hc]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hm : P α
  · have hm' : MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, Set.indicator, hm']
    ring
  · have hm' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, Set.indicator, hm']


/-- A finite family split costs a factor two in its squared norm budget. -/
theorem coefficient_split525 {ι : Type*} (s : Finset ι) (E A : ι → ℂ) :
    ∑ i ∈ s, ‖E i‖ ^ 2 ≤
      2 * ((∑ i ∈ s, ‖A i‖ ^ 2) + ∑ i ∈ s, ‖E i - A i‖ ^ 2) := by
  calc
    _ ≤ ∑ i ∈ s, 2 * (‖A i‖ ^ 2 + ‖E i - A i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := norm_add_le (A i) (E i - A i)
      rw [show A i + (E i - A i) = E i by ring] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans add_sq_le
    _ = _ := by rw [← Finset.sum_add_distrib, Finset.mul_sum]


/-- The selected central major contribution has the log power one stated on page 27.
This remains separate from the OPEN off rational remainder. -/
theorem major_core_log1_525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorCore525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hcentral⟩ := nearTransform_bound525 hG hϑ
  obtain ⟨C, hC, hfamily⟩ := smoothed_family_bound261 hϕ
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  let W : ℝ → ℂ := fun α => if α ∈ Set.Icc (0 : ℝ) 1 then
    if MajorArc X ((X : ℝ) ^ ϑ) α then
      1 - nearTransform525 G X ((X : ℝ) ^ ϑ) η α else 0 else 0
  have hW : Measurable W :=
    ((measurable_const.sub (measurable_nearTransform525 hG.supp hXp hRp hη)).ite
      (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)) measurable_const).ite
      measurableSet_Icc measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ D * η ^ 2 := by
    by_cases hα : α ∈ Set.Icc (0 : ℝ) 1
    · by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
      · simpa only [W, if_pos hα, if_pos hm] using hcentral X hX η hη hη1 hscale α hα hm
      · simp only [W, if_pos hα, if_neg hm, norm_zero]
        positivity
    · simp only [W, if_neg hα, norm_zero]
      positivity
  have hb := hfamily X hX W hW (D * η ^ 2) (by positivity) hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
        majorCore525 ϕ G X N ϑ η := by
    apply intervalIntegral.integral_congr
    intro α hα
    have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
    dsimp only [W]
    rw [if_pos hα']
    by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp only [hm, if_true, if_false, mul_zero, zero_mul]
  simp_rw [heq] at hb
  convert hb using 1 <;> ring


/-- LEAF. Pages 26 and 27, display 7.7 inside the major contribution to 7.8.
Central coefficient estimate with no off rational terms.
The actual smoothing scale N and the single central term Poisson error are retained. -/
theorem major_core_family525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorCore525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hbound⟩ := major_core_log1_525 hϕ hG ϑ hϑ hϑ'
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hb := hbound X hX η hη hη1 hscale
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp hlog
    norm_num at hh
    nlinarith only [hh]
  calc
    _ ≤ C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := hb
    _ ≤ (C * η ^ 4 * (X : ℝ) ^ 3) * (16 * Real.log X ^ 5) :=
      mul_le_mul_of_nonneg_left hlog5 (by positivity)
    _ = _ := by ring


/-- Below denominator two, the full weight transform has only the denominator one term. -/
theorem bRhat_single_denominator525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {R : ℝ} (hR : 1 ≤ R) (hR2 : R < 2) (T : ℕ → ℝ) (hT : 0 < T 1) (α : ℝ) :
    bRhat G R T α = GThat G (T 1) α := by
  have hf : ⌊R⌋₊ = 1 := (Nat.floor_eq_iff (by linarith : 0 ≤ R)).mpr (by constructor <;> norm_num <;> assumption)
  have hTs : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hq1 : q = 1 := by rw [hf] at hq; simpa using hq
    simpa [hq1] using hT
  simpa [hf] using bRhat_eq hG.supp hG.even R T hTs α


/-- With only denominator one, there is no off rational major remainder. -/
theorem majorTail_single_denominator525 (ϕ : ℝ → ℝ) {G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) {ϑ η : ℝ} (hϑ : 0 < ϑ)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X) (hR2 : (X : ℝ) ^ ϑ < 2) :
    majorTail525 ϕ G X N ϑ η = 0 := by
  classical
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXp ϑ
  have hf : ⌊(X : ℝ) ^ ϑ⌋₊ = 1 :=
    (Nat.floor_eq_iff hRp.le).mpr (by constructor <;> norm_num <;> assumption)
  have hηX : η * X ≤ (X : ℝ) := by nlinarith
  have hsep : 2 * ((X : ℝ) ^ ϑ) ^ 2 < X := by nlinarith
  have hRX : (X : ℝ) ^ ϑ ≤ X := by nlinarith [sq_nonneg ((X : ℝ) ^ ϑ - 1)]
  rw [majorTail_eq_integral525 ϕ hG hX N ϑ hη]
  have heq : (∫ α in (0 : ℝ)..1,
      {α | MajorArc X ((X : ℝ) ^ ϑ) α}.indicator (fun α => Sphi ϕ N α ^ 2 *
        (nearTransform525 G X ((X : ℝ) ^ ϑ) η α -
          bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
          ee (-(N * α))) α) = ∫ _α in (0 : ℝ)..1, (0 : ℂ) := by
    apply intervalIntegral.integral_congr
    intro α hα
    have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
    by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
    · obtain ⟨q, hq, a, ha, hclose⟩ := majorArc_center_in_sum525 hXp hRX hα' hm
      have hq1 : q = 1 := by rw [hf] at hq; simpa using hq
      subst q
      have hnear := nearTransform_eq525 (G := G) (η := η) hXp hRp.le hsep hq ha hclose
      have hperiod : GThat G (η * X * (1 : ℕ) / (X : ℝ) ^ ϑ) (α - (a : ℝ)) =
          GThat G (η * X * (1 : ℕ) / (X : ℝ) ^ ϑ) α := by
        simpa only [Int.cast_neg, sub_eq_add_neg] using
          GThat_add_int G (η * X * (1 : ℕ) / (X : ℝ) ^ ϑ) α (-a)
      have hfull := bRhat_single_denominator525 hG hR1 hR2
        (fun q => η * X * q / (X : ℝ) ^ ϑ) (by positivity) α
      have hsame : nearTransform525 G X ((X : ℝ) ^ ϑ) η α =
          bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α := by
        simp only [Nat.cast_one, div_one] at hnear hperiod hfull
        exact hnear.trans (hperiod.trans hfull.symm)
      simp [Set.indicator, hm, hsame]
    · simp [Set.indicator, hm]
  rw [heq, intervalIntegral.integral_zero]


/-- The exact major family is proved with log power one when only denominator one is present. -/
theorem major_family_single_denominator525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨C, hC, hb⟩ := major_core_log1_525 hϕ hG ϑ hϑ hϑ'
  refine ⟨C, hC, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have heq (N : ℕ) : majorError150 ϕ G X N ϑ η = majorCore525 ϕ G X N ϑ η := by
    have hz := majorTail_single_denominator525 ϕ hG hX N hϑ hη hη1 hscale hR2
    exact sub_eq_zero.mp hz
  simp_rw [heq]
  exact hb X hX η hη hη1 hscale


/-- The minor arc coefficient with multiplier one. -/
noncomputable def minorBare525 (ϕ : ℝ → ℝ) (X N : ℕ) (ϑ : ℝ) : ℂ := by
  classical
  exact ∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
    Sphi ϕ N α ^ 2 * ee (-(N * α))


/-- The remaining minor coefficient, with multiplier negative bRhat. -/
noncomputable def minorWeighted525 (ϕ G : ℝ → ℝ) (X N : ℕ) (ϑ η : ℝ) : ℂ :=
  minorError150 ϕ G X N ϑ η - minorBare525 ϕ X N ϑ


/-- The weighted minor remainder is exactly the coefficient with negative bRhat.
All integrals are justified by continuity before subtracting. -/
theorem minorWeighted_eq_integral525 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϕ : ℝ → ℝ) {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ)
    {η : ℝ} (hη : 0 < η) :
    minorWeighted525 ϕ G X N ϑ η =
      -(∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
        (fun α => Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
          (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))) α) := by
  classical
  let P : ℝ → Prop := MajorArc X ((X : ℝ) ^ ϑ)
  let f : ℝ → ℂ := fun α => Sphi ϕ N α ^ 2 *
    (1 - bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))
  let g : ℝ → ℂ := fun α => Sphi ϕ N α ^ 2 * ee (-(N * α))
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hf : Continuous f :=
    (((continuous_Sphi ϕ N).pow 2).mul (continuous_error_multiplier525 hG hX ϑ hη)).mul he
  have hg : Continuous g := ((continuous_Sphi ϕ N).pow 2).mul he
  have hs : MeasurableSet {α | ¬ P α} := (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)).compl
  have hmask (u : ℝ → ℂ) : {α | ¬ P α}.indicator u = (fun α => if P α then 0 else u α) := by
    funext α
    by_cases hm : P α <;> simp [Set.indicator, hm]
  have hif : IntervalIntegrable (fun α => if P α then 0 else f α) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rw [← hmask f]
    exact hf.integrableOn_Ioc.indicator hs
  have hig : IntervalIntegrable (fun α => if P α then 0 else g α) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rw [← hmask g]
    exact hg.integrableOn_Ioc.indicator hs
  unfold minorWeighted525 minorError150 minorBare525
  rw [← intervalIntegral.integral_sub hif hig, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro α hα
  by_cases hm : P α
  · have hm' : MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, f, g, Set.indicator, hm']
  · have hm' : ¬ MajorArc X ((X : ℝ) ^ ϑ) α := hm
    simp [P, f, g, Set.indicator, hm']
    ring


/-- The actual minor family has the printed power budget with log power one when R is below two.
The only discrete weight term is bounded uniformly. No power five leaf is used. -/
theorem minor_family_single_denominator525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X := by
  classical
  obtain ⟨D, hD, hGT⟩ := GThat_bound hG.supp hG.smooth (1 : ℝ)
  obtain ⟨C, hC, hfamily⟩ := smoothed_family_bound261 hϕ
  let B : ℝ := 1 + 2 * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * C * B ^ 2, by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℝ := η * X / R
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hRp : 0 < R := by linarith
  have hT1 : 1 ≤ T := by
    apply (le_div_iff₀ hRp).mpr
    change 10 * R ^ 2 ≤ η * X at hscale
    nlinarith [sq_nonneg (R - 1)]
  have hTp : 0 < T := by linarith
  have hb (α : ℝ) :
      ‖bRhat G R (fun q => η * X * q / R) α‖ ≤ 2 * D := by
    rw [bRhat_single_denominator525 hG hR1 hR2 _ (by positivity)]
    have ht := hGT T α hT1
    have hp1 : (1 + T * intDist α) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [intDist_nonneg α]) (by norm_num)
    have hp2 : T ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
    have heq : η * X * (1 : ℕ) / R = T := by dsimp [T]; simp
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hD.le]
  let W : ℝ → ℂ := fun α => if MajorArc X R α then 0 else
    1 - bRhat G R (fun q => η * X * q / R) α
  have hW : Measurable W := measurable_const.ite (measurableSet_majorArc84 X R)
    (continuous_error_multiplier525 hG hX ϑ hη).measurable
  have hWB (α : ℝ) : ‖W α‖ ≤ B := by
    by_cases hm : MajorArc X R α
    · simp only [W, if_pos hm, norm_zero]
      exact hB
    · simp only [W, if_neg hm]
      have hh := norm_sub_le (1 : ℂ) (bRhat G R (fun q => η * X * q / R) α)
      rw [norm_one] at hh
      exact hh.trans (by dsimp [B]; linarith [hb α])
  have hfam := hfamily X hX W hW B hB hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) =
        minorError150 ϕ G X N ϑ η := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, R, hm]
  simp_rw [heq] at hfam
  have hinv : (1 / 2 : ℝ) ≤ R⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      hRp hR2.le
  have hpower : 0 ≤ (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
  have hcoeff : 1 ≤ 2 * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) := by linarith
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hh := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ C * B ^ 2 * (X : ℝ) ^ 3 * Real.log X)
  change (∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) ≤
    (2 * C * B ^ 2) * (R⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X
  nlinarith


/-- LEAF. P0029 page 27, major remainder after display 7.7 in the proof of 7.8.
OPEN only for R at least two. The single denominator case is proved separately. -/
theorem major_tail_multi525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry


/-- LEAF. P0029 page 27, minor contribution in the proof of display 7.8.
OPEN only for R at least two. The single denominator case is proved separately. -/
theorem minor_bare_multi525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry


/-- LEAF. P0029 page 27, minor contribution in the proof of display 7.8.
OPEN only for R at least two. The single denominator case is proved separately. -/
theorem minor_weighted_multi525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorWeighted525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry


/-- The full major tail is CONDITIONAL ON the multi denominator leaf.
P0029 page 27, proof of display 7.8. -/
theorem major_tail_family525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail525 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hb⟩ := major_tail_multi525 hϕ hG ϑ hϑ hϑ'
  refine ⟨C, hC, ?_⟩
  intro X hX η hη hη1 hscale
  by_cases hR : 2 ≤ (X : ℝ) ^ ϑ
  · exact hb X hX hR η hη hη1 hscale
  · have hz (N : ℕ) := majorTail_single_denominator525 ϕ hG hX N hϑ hη hη1 hscale (lt_of_not_ge hR)
    simp_rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (pow_nonneg (Real.log_natCast_nonneg X) 5)


/-- Exact major_family150 statement assembled from the central and off rational pieces.
CONDITIONAL ON major_tail_family525. The central family has clean axioms. -/
theorem major_family_supply525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := major_core_family525 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := major_tail_family525 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hcore := h₁ X hX η hη hη1 hscale
  have htail := h₂ X hX η hη hη1 hscale
  have hsplit := coefficient_split525 (Finset.Icc 1 X)
    (fun N => majorError150 ϕ G X N ϑ η) (fun N => majorCore525 ϕ G X N ϑ η)
  change (∑ N ∈ Finset.Icc 1 X, ‖majorTail525 ϕ G X N ϑ η‖ ^ 2) ≤ _ at htail
  dsimp [majorTail525] at htail
  nlinarith


/-- The logarithm power one bound implies power five uniformly from X two onward. -/
theorem log_le_sixteen_log5_525 {X : ℕ} (hX : 2 ≤ X) :
    Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ X by exact_mod_cast hX)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by linarith [Real.log_two_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
  have hm := mul_le_mul_of_nonneg_right hp (Real.log_natCast_nonneg X)
  norm_num at hm
  nlinarith only [hm]


/-- The actual full minor multiplier has the printed power five below denominator two.
This is the power five consequence of minor_family_single_denominator525. -/
theorem minor_full_single_denominator525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → (X : ℝ) ^ ϑ < 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 → 10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hf⟩ := minor_family_single_denominator525 hϕ hG ϑ hϑ hϑ'
  refine ⟨16 * C, by positivity, ?_⟩
  intro X hX hR2 η hη hη1 hscale
  have hh := mul_le_mul_of_nonneg_left (log_le_sixteen_log5_525 hX)
    (by positivity : 0 ≤ C * (((X : ℝ) ^ ϑ)⁻¹ +
      (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3)
  nlinarith only [hf X hX hR2 η hη hη1 hscale, hh]


/-- The exact minor family is CONDITIONAL ON the two multi denominator leaves.
The single denominator contribution uses only clean supply proofs.
P0029 page 27, proof of display 7.8. -/
theorem minor_family_supply525 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := minor_full_single_denominator525 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_bare_multi525 hϕ ϑ hϑ hϑ'
  obtain ⟨C₃, hC₃, h₃⟩ := minor_weighted_multi525 hϕ hG ϑ hϑ hϑ'
  refine ⟨max C₁ (2 * (C₂ + C₃)), le_trans hC₁ (le_max_left _ _), ?_⟩
  intro X hX η hη hη1 hscale
  by_cases hR : (X : ℝ) ^ ϑ < 2
  · apply (h₁ X hX hR η hη hη1 hscale).trans
    gcongr
    exact le_max_left _ _
  · have hb := h₂ X hX (le_of_not_gt hR)
    have hw := h₃ X hX (le_of_not_gt hR) η hη hη1 hscale
    have hs := coefficient_split525 (Finset.Icc 1 X)
      (fun N => minorError150 ϕ G X N ϑ η) (fun N => minorBare525 ϕ X N ϑ)
    dsimp [minorWeighted525] at hw
    have hmulti : (∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) ≤
        (2 * (C₂ + C₃)) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
      nlinarith only [hs, hb, hw]
    apply hmulti.trans
    gcongr
    exact le_max_right _ _

end LeanLab.BhowmikGrimmelt2026
