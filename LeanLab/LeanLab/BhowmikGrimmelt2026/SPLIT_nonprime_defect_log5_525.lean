/-
Split of the bare minor defect step of `SPLIT_minor_bare_multi525`.

The minor arc defect coefficient is the integral over the circle, cut off on the
major arcs, of `S ^ 2 - P ^ 2` against the phase `e(-Nα)`, where `S` is the full
smoothed sum and `P` its prime restricted part. The difference of two squares
factors as `(S - P) * (S + P)`, and the sum `S + P` decomposes into the two
pieces `(S - P) * S` and `(S - P) * P`.

The two leaves are the per coefficient estimates for those pieces. The first
carries the higher prime power piece of the difference: only prime powers with
exponent at least two survive there, so its coefficients are far smaller than
the coefficients of the prime part. The second carries the prime part together
with the smoothing. Both are stated one coefficient at a time, which is weaker
than the summed family bound of the target: the assembly pays a factor two for
the split of the squared modulus and one factor of `X` for the number of
integers up to `X`, which turns the three halves power of `X` into five halves,
and the power thirteen fifths of the target absorbs five halves with room to
spare.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_minor_bare_multi525

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## The two leaves -/

/-- LEAF: the per coefficient estimate for the higher prime power piece of the
defect. Writing `S` for the full smoothed sum and `P` for its prime restricted
part, the coefficient of the product `(S - P) * S` against the phase `e(-Nα)`,
cut off on the minor arcs, is at most in squared modulus the fourth power of the
bound for the smoothing times the three halves power of `X` and the fifth power
of the logarithm, for every cutoff `N` between one and `X`. The two mean squares
of that product cost a square root of `X` from the prime powers and one `X` from
the smoothing, and the logarithm costs the power five. -/
theorem defect_higher_power_coefficient_525 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) {N : ℕ}
    (hN : N ∈ Finset.Icc 1 X) :
    ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α -
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
            Sphi ϕ N α * ee (-(N * α))‖ ^ 2 ≤
      M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5 := by
  sorry

/-- LEAF: the per coefficient estimate for the prime part of the defect. Writing
`S` for the full smoothed sum and `P` for its prime restricted part, the
coefficient of the product `(S - P) * P` against the phase `e(-Nα)`, cut off on
the minor arcs, is at most in squared modulus the fourth power of the bound for
the smoothing times the three halves power of `X` and the fifth power of the
logarithm, for every cutoff `N` between one and `X`. This is the piece on which
the prime part itself sits, so it is the one that would grow without the extra
factor of `X` in the family budget. -/
theorem defect_prime_part_coefficient_525 {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) {N : ℕ}
    (hN : N ∈ Finset.Icc 1 X) :
    ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α -
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) *
            ee (-(N * α))‖ ^ 2 ≤
      M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5 := by
  sorry

/-! ## Proved helpers -/

/-- A continuous integrand cut off on the minor arcs stays interval integrable. -/
private lemma masked_intervalIntegrable_525 (X : ℕ) (R : ℝ) {g : ℝ → ℂ}
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

/-- The prime restricted finite sum is continuous in the frequency. -/
private lemma continuous_prime_part_525 (ϕ : ℝ → ℝ) (N X : ℕ) :
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

/-- The squared modulus of a sum costs a factor two on each piece. -/
private lemma norm_add_sq_le_525 (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [h, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-! ## Assembly -/

/-- The bare minor defect statement for minorBare525, from the two per
coefficient estimates. Nothing is assumed here beyond the two leaves: the
difference of two squares is split into the higher prime power piece and the
prime piece, the squared modulus of a sum costs a factor two, the sum over the
cutoff is bounded by one term per integer up to `X`, and the power budget is
absorbed by the inverse scale part of the family bound. -/
theorem nonprime_defect_log5_525_split {ϕ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2)
      ≤ 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  classical
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hcard : (Finset.Icc 1 X).card = X := by simp
  have hterm : ∀ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2 ≤
      4 * M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5 := by
    intro N hN
    have h1 := defect_higher_power_coefficient_525 hM hbound hX ϑ hN
    have h2 := defect_prime_part_coefficient_525 hM hbound hX ϑ hN
    have hI1 : IntervalIntegrable (fun α : ℝ =>
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α -
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
            Sphi ϕ N α * ee (-(N * α))) volume 0 1 :=
      masked_intervalIntegrable_525 X _
        ((((continuous_Sphi ϕ N).sub (continuous_prime_part_525 ϕ N X)).mul
          (continuous_Sphi ϕ N)).mul (continuous_phase_525 N))
    have hI2 : IntervalIntegrable (fun α : ℝ =>
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α -
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) *
            ee (-(N * α))) volume 0 1 :=
      masked_intervalIntegrable_525 X _
        ((((continuous_Sphi ϕ N).sub (continuous_prime_part_525 ϕ N X)).mul
          (continuous_prime_part_525 ϕ N X)).mul (continuous_phase_525 N))
    have hsplit : (∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))) =
        (∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (Sphi ϕ N α -
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
              Sphi ϕ N α * ee (-(N * α))) +
        (∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (Sphi ϕ N α -
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) *
              ee (-(N * α))) := by
      rw [← intervalIntegral.integral_add hI1 hI2]
      apply intervalIntegral.integral_congr
      intro α hα
      by_cases h : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp [h] <;> ring
    have htwo : ‖(∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α)))‖ ^ 2 ≤
        2 * ‖(∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (Sphi ϕ N α -
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
              Sphi ϕ N α * ee (-(N * α)))‖ ^ 2 +
        2 * ‖(∫ α in (0 : ℝ)..1,
          if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
            (Sphi ϕ N α -
                (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                  ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n))) *
              (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
                ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) *
              ee (-(N * α)))‖ ^ 2 := by
      rw [hsplit]
      exact norm_add_sq_le_525 _ _
    nlinarith [h1, h2, htwo]
  calc ∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2
      ≤ ∑ _N ∈ Finset.Icc 1 X,
          (4 * M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5) :=
        Finset.sum_le_sum hterm
    _ = (X : ℝ) * (4 * M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
        have hpow : (X : ℝ) ^ (5 / 2 : ℝ) ≤ (X : ℝ) ^ (13 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
        have hstep : (X : ℝ) * (X : ℝ) ^ (3 / 2 : ℝ) = (X : ℝ) ^ (5 / 2 : ℝ) := by
          have h : (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (3 / 2 : ℝ) =
              (X : ℝ) ^ (5 / 2 : ℝ) := by
            rw [← Real.rpow_add hXpos]
            norm_num
          simpa using h
        have hkey : (X : ℝ) * (X : ℝ) ^ (3 / 2 : ℝ) ≤ 48 * (X : ℝ) ^ (13 / 5 : ℝ) := by
          rw [hstep]
          have hXp : (0 : ℝ) ≤ (X : ℝ) ^ (13 / 5 : ℝ) := Real.rpow_nonneg hXpos.le _
          linarith
        calc (X : ℝ) * (4 * M ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) * Real.log X ^ 5)
            = (4 * M ^ 4 * Real.log X ^ 5) * ((X : ℝ) * (X : ℝ) ^ (3 / 2 : ℝ)) := by
              ring
          _ ≤ (4 * M ^ 4 * Real.log X ^ 5) * (48 * (X : ℝ) ^ (13 / 5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = 192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by ring

end LeanLab.BhowmikGrimmelt2026
