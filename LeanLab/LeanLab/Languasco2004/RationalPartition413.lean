/-
Finite integral components of PP1993 page 45 display 7.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.ArcGeometry413
import LeanLab.Languasco2004.MajorData413

namespace LeanLab.Languasco2004.RationalPartition413
open Finset Real MeasureTheory Decomp279b Decomp413b ArcGeometry413
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 45 display 7: the integrals are over a finite union of the
small rational arcs, clipped to the integration period. -/
theorem major_domain_union (N Y H B : ℝ) (hN : 1 ≤ N) :
    period H ∩ majorSet N Y B =
      ⋃ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
        ⋃ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          {x : ℝ | x ∈ period H ∧
            |x - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)} := by
  ext x
  simp only [Set.mem_inter_iff, majorSet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, q, a, hq1, hqL, ha1, haq, hcop, hdist⟩
    exact ⟨q, mem_Icc.mpr ⟨hq1, Nat.le_floor hqL⟩, a,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨ha1, haq⟩, hcop⟩, hx, hdist⟩
  · rintro ⟨q, hq, a, ha, hx, hdist⟩
    obtain ⟨hq1, hqL⟩ := mem_Icc.mp hq
    obtain ⟨haI, hcop⟩ := mem_filter.mp ha
    obtain ⟨ha1, haq⟩ := mem_Icc.mp haI
    have hqL' : (q : ℝ) ≤ Real.log N ^ B :=
      (show (q : ℝ) ≤ (⌊Real.log N ^ B⌋₊ : ℝ) from by exact_mod_cast hqL).trans (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg hN) B))
    exact ⟨hx, q, a, hq1, hqL', ha1, haq, hcop, hdist⟩

/-- Page 45 display 7: a set integral translates to the local arc variable.
This is the translation invariance of Lebesgue measure, with no estimates. -/
theorem arc_translation (f : ℝ → ℂ) (c w H : ℝ) :
    (∫ x in {x : ℝ | x ∈ period H ∧ |x - c| < w}, f x) =
      ∫ t in {t : ℝ | |t| < w ∧ c + t ∈ period H}, f (c + t) := by
  have hs : MeasurableSet {x : ℝ | x ∈ period H ∧ |x - c| < w} := by
    exact measurableSet_Icc.inter (measurableSet_lt (f := fun x : ℝ => |x - c|) (g := fun _ => w) (by fun_prop) measurable_const)
  have ht : MeasurableSet {t : ℝ | |t| < w ∧ c + t ∈ period H} := by
    apply MeasurableSet.inter
    · exact measurableSet_lt (f := fun t : ℝ => |t|) (g := fun _ => w) (by fun_prop) measurable_const
    · exact measurableSet_Icc.preimage (by fun_prop : Measurable (fun t : ℝ => c + t))
  rw [← integral_indicator hs, ← integral_indicator ht]
  have heq : (fun t : ℝ => ({x : ℝ | x ∈ period H ∧ |x - c| < w}.indicator f) (c + t)) =
      {t : ℝ | |t| < w ∧ c + t ∈ period H}.indicator (fun t => f (c + t)) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_setOf_eq, add_sub_cancel_left, and_comm]
  rw [← heq, integral_add_left_eq_self]

/-- Page 45 display 7: finite rational integration preserves sums of
continuous integrands. This supplies the algebraic part of the partition. -/
theorem rationalIntegral_add (N Y H B : ℝ) (m : ℕ)
    (F G : ℕ → ℕ → ℝ → ℂ)
    (hF : ∀ q a : ℕ, Continuous (F q a)) (hG : ∀ q a : ℕ, Continuous (G q a)) :
    rationalIntegral N Y H B m (fun q a t => F q a t + G q a t) =
      rationalIntegral N Y H B m F + rationalIntegral N Y H B m G := by
  unfold rationalIntegral
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  let c : ℝ := (a : ℝ) / q
  let w : ℝ := Real.log N ^ (2 * B) / ((q : ℝ) * Y)
  have hsub : {t : ℝ | |t| < w ∧ c + t ∈ period H} ⊆ Set.Icc (-w) w := by
    intro t ht
    have ht' := abs_lt.mp ht.1
    exact ⟨ht'.1.le, ht'.2.le⟩
  have hFc : Continuous (fun t : ℝ => F q a t * phase (-(m : ℝ) * (c + t))) := by
    unfold phase
    fun_prop
  have hGc : Continuous (fun t : ℝ => G q a t * phase (-(m : ℝ) * (c + t))) := by
    unfold phase
    fun_prop
  have hFi : IntegrableOn (fun t : ℝ => F q a t * phase (-(m : ℝ) * (c + t)))
      {t : ℝ | |t| < w ∧ c + t ∈ period H} volume := hFc.integrableOn_Icc.mono_set hsub
  have hGi : IntegrableOn (fun t : ℝ => G q a t * phase (-(m : ℝ) * (c + t)))
      {t : ℝ | |t| < w ∧ c + t ∈ period H} volume := hGc.integrableOn_Icc.mono_set hsub
  simp_rw [add_mul]
  exact integral_add hFi hGi

/-- Page 45 display 7: integrate the elementary four term identity.
Only the disjoint geometric identification with the major integral remains. -/
theorem rational_product_decomposition (N Y H B : ℝ) (m : ℕ) :
    rationalIntegral N Y H B m (fun q a t =>
      firstSum N Y ((a : ℝ) / q + t) * secondSum Y ((a : ℝ) / q + t)) =
      principalCoefficient N Y H B m + remainderCoefficient N Y H B m := by
  simp_rw [product_decomposition]
  apply rationalIntegral_add
  all_goals intro q a
  all_goals simp only [firstRemainder, secondRemainder, rationalWeight, firstModel, secondModel,
      firstSum, secondSum, phase]
  all_goals fun_prop

/-- Page 45 display 7: small arcs with radii R over q are disjoint
under the common Farey separation condition. -/
theorem variable_radius_disjoint (a q b r : ℕ) (Q R : ℝ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : (q : ℝ) ≤ Q) (hrQ : (r : ℝ) ≤ Q)
    (haq : Nat.Coprime a q) (hbr : Nat.Coprime b r)
    (hne : (q, a) ≠ (r, b)) (hR : 0 ≤ R) (hsmall : 2 * R ≤ 1 / Q ^ 2) :
    Disjoint {x : ℝ | |x - (a : ℝ) / q| < R / q}
      {x : ℝ | |x - (b : ℝ) / r| < R / r} := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hfrac : (a : ℝ) / q ≠ (b : ℝ) / r := by
    intro heq
    obtain ⟨hab, hqr⟩ := reduced_centre_unique a q b r hq hr haq hbr heq
    exact hne (Prod.ext hqr hab)
  have hqR : R / q ≤ R := (div_le_iff₀ hqp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hq1 hR])
  have hrR : R / r ≤ R := (div_le_iff₀ hrp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hr1 hR])
  exact (common_radius_disjoint a q b r Q R hq hr hqQ hrQ hfrac hsmall).mono
    (fun _ hx => hx.trans_le hqR) (fun _ hx => hx.trans_le hrR)

/-- Page 45 display 7: integrate over a finite disjoint family of reduced
rational arcs. The result is the sum of the individual clipped integrals. -/
theorem integral_finite_rational_union (Q R H : ℝ) (f : ℝ → ℂ)
    (hQ : 0 < Q) (hR : 0 ≤ R) (hsmall : 2 * R ≤ 1 / Q ^ 2) (hf : Continuous f) :
    (∫ x in ⋃ q ∈ Icc 1 ⌊Q⌋₊,
      ⋃ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        {x : ℝ | x ∈ period H ∧ |x - (a : ℝ) / q| < R / q}, f x) =
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ x in {x : ℝ | x ∈ period H ∧ |x - (a : ℝ) / q| < R / q}, f x := by
  let s : ℕ → Finset ℕ := fun q => (Icc 1 q).filter (fun a => Nat.Coprime a q)
  let arcs : ℕ → ℕ → Set ℝ := fun q a =>
    {x : ℝ | x ∈ period H ∧ |x - (a : ℝ) / q| < R / q}
  let qa : ℕ → Set ℝ := fun q => ⋃ a ∈ s q, arcs q a
  have hm : ∀ q a : ℕ, MeasurableSet (arcs q a) := by
    intro q a
    exact measurableSet_Icc.inter
      (measurableSet_lt (f := fun x : ℝ => |x - (a : ℝ) / q|)
        (g := fun _ => R / q) (by fun_prop) measurable_const)
  have hqm : ∀ q : ℕ, MeasurableSet (qa q) := by
    intro q
    exact Finset.measurableSet_biUnion (s q) (fun a _ => hm q a)
  have hi : IntegrableOn f (period H) volume := hf.integrableOn_Icc
  have hia : ∀ q a : ℕ, IntegrableOn f (arcs q a) volume :=
    fun _ _ => hi.mono_set (fun _ hx => hx.1)
  have hiq : ∀ q : ℕ, IntegrableOn f (qa q) volume := by
    intro q
    apply hi.mono_set
    intro x hx
    simp only [qa, Set.mem_iUnion] at hx
    obtain ⟨a, _, hx⟩ := hx
    exact hx.1
  have hbounds : ∀ q ∈ Icc 1 ⌊Q⌋₊, 0 < q ∧ (q : ℝ) ≤ Q := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hq
    refine ⟨by omega, ?_⟩
    exact (show (q : ℝ) ≤ (⌊Q⌋₊ : ℝ) from by exact_mod_cast hqQ).trans
      (Nat.floor_le hQ.le)
  have hdis : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a ∈ s q, ∀ r ∈ Icc 1 ⌊Q⌋₊, ∀ b ∈ s r,
      (q, a) ≠ (r, b) → Disjoint (arcs q a) (arcs r b) := by
    intro q hq a ha r hr b hb hne
    have hq' := hbounds q hq
    have hr' := hbounds r hr
    exact (variable_radius_disjoint a q b r Q R hq'.1 hr'.1 hq'.2 hr'.2
      (mem_filter.mp ha).2 (mem_filter.mp hb).2 hne hR hsmall).mono
        (fun _ hx => hx.2) (fun _ hx => hx.2)
  have hqd : Set.Pairwise (↑(Icc 1 ⌊Q⌋₊)) (fun q r => Disjoint (qa q) (qa r)) := by
    intro q hq r hr hqr
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [qa, Set.mem_iUnion] at hx hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hxb⟩ := hy
    have hne : (q, a) ≠ (r, b) := fun hh => hqr (congrArg Prod.fst hh)
    exact Set.disjoint_left.mp (hdis q hq a ha r hr b hb hne) hxa hxb
  change (∫ x in ⋃ q ∈ Icc 1 ⌊Q⌋₊, qa q, f x) = _
  rw [integral_biUnion_finset _ (fun q _ => hqm q) hqd (fun q _ => hiq q)]
  apply sum_congr rfl
  intro q hq
  change (∫ x in ⋃ a ∈ s q, arcs q a, f x) = _
  apply integral_biUnion_finset
  · exact fun a _ => hm q a
  · intro a ha b hb hab
    exact hdis q hq a ha q hq b hb (fun hh => hab (congrArg Prod.snd hh))
  · exact fun a _ => hia q a

/-- Page 45 display 7: disjoint small major arcs give the exact rational
integral of the original prime sums. All endpoints remain explicit. -/
theorem major_to_rational (N Y H B : ℝ) (m : ℕ) (hN : 1 < N) (hY : 0 < Y)
    (hsmall : 2 * (Real.log N ^ (2 * B) / Y) ≤ 1 / (Real.log N ^ B) ^ 2) :
    majorCoefficient N Y H B m = rationalIntegral N Y H B m (fun q a t =>
      firstSum N Y ((a : ℝ) / q + t) * secondSum Y ((a : ℝ) / q + t)) := by
  have hL : 0 < Real.log N := Real.log_pos hN
  have hQ : 0 < Real.log N ^ B := Real.rpow_pos_of_pos hL B
  have hR : 0 ≤ Real.log N ^ (2 * B) / Y := by positivity
  let f : ℝ → ℂ := fun x => firstSum N Y x * secondSum Y x * phase (-(m : ℝ) * x)
  have hf : Continuous f := by
    unfold f firstSum secondSum phase
    fun_prop
  have hid : ∀ q : ℕ, Real.log N ^ (2 * B) / ((q : ℝ) * Y) =
      (Real.log N ^ (2 * B) / Y) / q := by
    intro q
    rw [div_mul_eq_div_div, div_right_comm]
  unfold majorCoefficient
  rw [major_domain_union N Y H B hN.le]
  simp_rw [hid]
  rw [integral_finite_rational_union _ _ H f hQ hR hsmall hf]
  unfold rationalIntegral
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro a ha
  rw [arc_translation]
  simp only [f, hid]

/-- Page 45 display 7: for the prescribed logarithmic arc widths,
rational disjointness holds for sufficiently large N. This proves the
exact geometric partition leaf without a density or sieve input. -/
theorem major_partition_from_geometry :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ m : ℕ,
      majorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m =
        principalCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m +
        remainderCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m := by
  refine ⟨1, by norm_num, ?_⟩
  intro η A hη _ hA
  let B : ℝ := arcExponent η A
  have hp : 0 < (7 / 12 : ℝ) + η := by linarith
  have hlo := isLittleO_log_rpow_rpow_atTop (4 * B) hp
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hlo.bound (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max 3 N₁, ?_⟩
  intro N hN m
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans hN
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hY : 0 < localization N η := Real.rpow_pos_of_pos hNp _
  have hQ : 0 < Real.log N ^ B := Real.rpow_pos_of_pos hL B
  have hb := hN₁ N hN1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hNp.le _)] at hb
  have hpower : Real.log N ^ (2 * B) * (Real.log N ^ B) ^ 2 = Real.log N ^ (4 * B) := by
    rw [← Real.rpow_two (Real.log N ^ B), ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    congr 1
    ring
  have hsmall : 2 * (Real.log N ^ (2 * B) / localization N η) ≤ 1 / (Real.log N ^ B) ^ 2 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hY (sq_pos_of_pos hQ)]
    rw [mul_assoc, hpower]
    change Real.log N ^ (4 * B) ≤ (1 / 2 : ℝ) * localization N η at hb
    linarith
  rw [major_to_rational N (localization N η) (windowLength N η) B m
    (by linarith) hY hsmall, rational_product_decomposition]

#print axioms major_to_rational
#print axioms major_partition_from_geometry
#print axioms variable_radius_disjoint
#print axioms integral_finite_rational_union
#print axioms major_domain_union
#print axioms arc_translation
#print axioms rationalIntegral_add
#print axioms rational_product_decomposition
end
end LeanLab.Languasco2004.RationalPartition413
