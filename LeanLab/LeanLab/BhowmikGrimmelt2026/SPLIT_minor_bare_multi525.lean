/-
Split of the bare multi denominator step for minor_bare_multi525 on the minor arcs.

The bare coefficient is an integral of the squared smoothed sum with the phase
weight, cut off on the minor arcs. Separating the arithmetic weight of that sum
into the part supported on primes and the remaining higher prime power part
writes each coefficient as a sum of two pieces. The squared modulus of that sum
costs a factor two, which the assembly pays, and the second moment of the family
is then bounded by

  twice the second moment of the prime restricted family, plus
  twice the second moment of the defect where the prime part is removed.

The defect is smaller than the family budget by a square root of X, so it fits
the second term of the power budget with the fifth logarithm power; that is one
leaf. The prime restricted family is the genuine analytic obligation on the
range where the minor scale is at least two, and it is the other leaf. Both
leaves are open, the assembly is complete, and nothing here is assumed.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp525a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## The two open pieces -/

/-- LEAF: the prime restricted family on the range where the minor
scale is at least two, which is the prime part of the split of the weight of the
smoothed sum.
For admissible phi and fixed theta strictly between zero and one half, one
nonnegative constant bounds the sum over the cutoff N of the squared modulus of
the minor arc coefficient of the squared prime restricted smoothed sum, by the
constant times the inverse scale budget, X cubed and the fifth power of log X,
for every X at least two with X to the theta at least two. The higher prime
powers are removed from this coefficient, which is what separates this step from
the sealed statement for minorBare525. -/
theorem prime_minor_multi_525 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF: the defect where the prime part is removed from the squared smoothing,
that is the coefficient of squared sum minus squared prime restricted sum, which
carries the higher prime powers. For admissible phi bounded by the nonnegative
constant M, every X at least two and every real theta, the sum over the cutoff N
of the squared modulus of that minor arc coefficient is at most 192 times M to the
fourth times X to thirteen fifths times log X to the fifth. It is smaller than the
family budget by a square root of X, so the second term of that budget pays it. -/
theorem nonprime_defect_log5_525 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2)
      ≤ 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  sorry

/-! ## Proved helpers -/

/-- A continuous integrand cut off on the minor arcs stays interval integrable. -/
private lemma intervalIntegrable_masked_525 (X : ℕ) (R : ℝ) {g : ℝ → ℂ}
    (hg : Continuous g) :
    IntervalIntegrable (fun α => if MajorArc X R α then 0 else g α) volume 0 1 := by
  have hs : MeasurableSet {α : ℝ | ¬ MajorArc X R α} :=
    (measurableSet_majorArc84 X R).compl
  have hmask : (fun α => if MajorArc X R α then 0 else g α) =
      {α : ℝ | ¬ MajorArc X R α}.indicator g := by
    funext α
    by_cases h : MajorArc X R α <;> simp [Set.indicator_apply, h]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  rw [hmask]
  exact hg.integrableOn_Ioc.indicator hs

/-- The prime restricted finite smoothing sum is continuous in the frequency. -/
private lemma continuous_primeSum_525 (ϕ : ℝ → ℝ) (N X : ℕ) :
    Continuous (fun α : ℝ =>
      ∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) := by
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul
    (ee_contDiff.continuous.comp (continuous_id.mul continuous_const))

/-- The phase factor is continuous in the frequency. -/
private lemma continuous_phase_525 (N : ℕ) :
    Continuous (fun α : ℝ => ee (-(N * α))) :=
  ee_contDiff.continuous.comp (continuous_const.mul continuous_id).neg

/-- Sums of squared moduli absorb the split of each term into two pieces. -/
private lemma sum_sq_split_525 {ι : Type*} (s : Finset ι) (c p d : ι → ℂ)
    (h : ∀ i ∈ s, c i = p i + d i) :
    ∑ i ∈ s, ‖c i‖ ^ 2 ≤ 2 * (∑ i ∈ s, ‖p i‖ ^ 2) + 2 * (∑ i ∈ s, ‖d i‖ ^ 2) := by
  have hstep : ∀ i ∈ s, ‖c i‖ ^ 2 ≤ 2 * ‖p i‖ ^ 2 + 2 * ‖d i‖ ^ 2 := by
    intro i hi
    have hpd : ‖c i‖ ≤ ‖p i‖ + ‖d i‖ := by rw [h i hi]; exact norm_add_le _ _
    have h1 : ‖c i‖ ^ 2 ≤ (‖p i‖ + ‖d i‖) ^ 2 := by
      nlinarith [hpd, norm_nonneg (c i), norm_nonneg (p i), norm_nonneg (d i)]
    have h2 : (‖p i‖ + ‖d i‖) ^ 2 ≤ 2 * ‖p i‖ ^ 2 + 2 * ‖d i‖ ^ 2 := by
      nlinarith [sq_nonneg (‖p i‖ - ‖d i‖)]
    linarith
  calc ∑ i ∈ s, ‖c i‖ ^ 2 ≤ ∑ i ∈ s, (2 * ‖p i‖ ^ 2 + 2 * ‖d i‖ ^ 2) :=
        Finset.sum_le_sum hstep
    _ = 2 * (∑ i ∈ s, ‖p i‖ ^ 2) + 2 * (∑ i ∈ s, ‖d i‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ## Assembly -/

/-- The bare multi denominator statement for minorBare525, from the prime
restricted family and the higher prime power defect. Nothing is assumed here
beyond the two leaves. -/
theorem minor_bare_multi525_split {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨M₀, hM₀⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  set M : ℝ := max M₀ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x, |ϕ x| ≤ M := by
    intro x
    have h := hM₀ x
    simp only [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨C₁, hC₁, h₁⟩ := prime_minor_multi_525 hϕ ϑ hϑ hϑ'
  refine ⟨2 * C₁ + 384 * M ^ 4, by positivity, ?_⟩
  intro X hX hR2
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hK : 0 ≤ ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
  -- each bare coefficient splits into the prime restricted coefficient and the defect
  have hsplit : ∀ N : ℕ,
      minorBare525 ϕ X N ϑ =
        (∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
              ee (-(N * α))) +
        ∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (Sphi ϕ N α ^ 2 -
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
              ee (-(N * α)) := by
    intro N
    have h₂ : IntervalIntegrable (fun α : ℝ =>
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
            ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
            ee (-(N * α))) volume 0 1 :=
      intervalIntegrable_masked_525 X _
        (((continuous_primeSum_525 ϕ N X).pow 2).mul (continuous_phase_525 N))
    have h₃ : IntervalIntegrable (fun α : ℝ =>
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))) volume 0 1 :=
      intervalIntegrable_masked_525 X _
        ((((continuous_Sphi ϕ N).pow 2).sub
          ((continuous_primeSum_525 ϕ N X).pow 2)).mul (continuous_phase_525 N))
    unfold minorBare525
    rw [← intervalIntegral.integral_add h₂ h₃]
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases h : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp [h] <;> ring
  have hsum := sum_sq_split_525 (Finset.Icc 1 X)
    (fun N => minorBare525 ϕ X N ϑ)
    (fun N => ∫ α in (0 : ℝ)..1,
      if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
        (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
          ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α)))
    (fun N => ∫ α in (0 : ℝ)..1,
      if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
        (Sphi ϕ N α ^ 2 -
          (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
            ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) * ee (-(N * α)))
    (fun N _ => hsplit N)
  have hP := h₁ X hX hR2
  have hD := nonprime_defect_log5_525 hM hbound hX ϑ
  have hpow : (X : ℝ) ^ (13 / 5 : ℝ) =
      (X : ℝ) ^ 3 * (X : ℝ) ^ (-(2 / 5) : ℝ) := by
    rw [← Real.rpow_natCast (X : ℝ) 3, ← Real.rpow_add hXpos]
    norm_num
  have hbudget : (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 ≤
      (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
    rw [hpow]
    have hinv : 0 ≤ ((X : ℝ) ^ ϑ)⁻¹ := by positivity
    have hcomp : (X : ℝ) ^ (-(2 / 5) : ℝ) ≤
        ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) := le_add_of_nonneg_left hinv
    have hlog : 0 ≤ Real.log X ^ 5 := by positivity
    calc (X : ℝ) ^ 3 * (X : ℝ) ^ (-(2 / 5) : ℝ) * Real.log X ^ 5
        = (X : ℝ) ^ 3 * ((X : ℝ) ^ (-(2 / 5) : ℝ) * Real.log X ^ 5) := by ring
      _ ≤ (X : ℝ) ^ 3 *
            ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * Real.log X ^ 5) := by
          gcongr
      _ = (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
          ring
  have hD' : (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2) ≤
      192 * M ^ 4 *
        ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5) := by
    have hM4 : 0 ≤ 192 * M ^ 4 := by positivity
    calc _ ≤ 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := hD
      _ = 192 * M ^ 4 * ((X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5) := by ring
      _ ≤ 192 * M ^ 4 *
            ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
              Real.log X ^ 5) := by
          exact mul_le_mul_of_nonneg_left hbudget hM4
  have hP' : (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
            ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
            ee (-(N * α))‖ ^ 2) ≤
      C₁ * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
        Real.log X ^ 5) := by
    have he : C₁ * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 =
        C₁ * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
          Real.log X ^ 5) := by ring
    linarith [hP, he]
  calc ∑ N ∈ Finset.Icc 1 X, ‖minorBare525 ϕ X N ϑ‖ ^ 2
      ≤ 2 * (∑ N ∈ Finset.Icc 1 X,
          ‖∫ α in (0 : ℝ)..1,
            if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
                ee (-(N * α))‖ ^ 2) +
        2 * (∑ N ∈ Finset.Icc 1 X,
          ‖∫ α in (0 : ℝ)..1,
            if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
              (Sphi ϕ N α ^ 2 -
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
                ee (-(N * α))‖ ^ 2) := hsum
    _ ≤ (2 * C₁ + 384 * M ^ 4) *
          ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
            Real.log X ^ 5) := by
        have h2P : 2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1,
              if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 *
                  ee (-(N * α))‖ ^ 2) ≤
            2 * (C₁ * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
              (X : ℝ) ^ 3 * Real.log X ^ 5)) := by linarith [hP']
        have h2D : 2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1,
              if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
                (Sphi ϕ N α ^ 2 -
                  (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                    ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
                  ee (-(N * α))‖ ^ 2) ≤
            2 * (192 * M ^ 4 * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
              (X : ℝ) ^ 3 * Real.log X ^ 5)) := by linarith [hD']
        have hid : (2 * C₁ + 384 * M ^ 4) *
            ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
              Real.log X ^ 5) =
            2 * (C₁ * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
              (X : ℝ) ^ 3 * Real.log X ^ 5)) +
            2 * (192 * M ^ 4 * ((((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
              (X : ℝ) ^ 3 * Real.log X ^ 5)) := by ring
        linarith [h2P, h2D, hid]
    _ = (2 * C₁ + 384 * M ^ 4) *
          (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
            Real.log X ^ 5 := by ring

end LeanLab.BhowmikGrimmelt2026
