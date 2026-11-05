import LeanLab.RamareSaouter2003.Decomp290c
import LeanLab.RamareSaouter2003.CorrectedLemma4_290

/-!
P0099 pp. 15 and 16, Lemma 4, applied before display 13 on p. 19.
Ramare 2023 Lemma 1.1 supplies the corrected negative constant.
The single-scale formula, zero-series subtraction and logarithmic subtraction
are separate tasks. The final difference has no split height.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359d

open Real Chebyshev Smooth Thm4Assembly L3Zeta Decomp290c

/-- LEAF. P0099 pp. 15 and 16, Lemma 4 after the affine substitution.
Ramare 2023 p. 1, Lemma 1.1 corrects the constant.
This is one psi integral at one scale, before taking a difference of scales. -/
theorem scaled_weight_formula (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m)
    (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
      (∫ t in (0 : ℝ)..1, A * (1 + δ * t) * fm m t) -
      (∑' i : ZI, ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
          (i.1 : ℂ) * (fm m t : ℂ)).re -
      ∫ t in (0 : ℝ)..1,
        (Real.log (2 * π) + (1 / 2) *
          Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2)) * fm m t := by
  sorry

/-- LEAF. P0099 p. 19, factorization of the zero contribution in display 13.
Only the two actual integrated zero series are subtracted here.
No Chebyshev function or explicit formula is part of this leaf. -/
theorem zero_series_difference (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    (∑' i : ZI, ∫ t in (0 : ℝ)..1,
      (((X * Real.exp u * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)).re -
    (∑' i : ZI, ∫ t in (0 : ℝ)..1,
      (((X * (1 + m * u * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)).re =
      (∑' i : ZI, zeroTerm m X u i).re := by
  sorry

/-- LEAF. P0099 p. 19 before display 13.
The corrected log 2pi constants cancel in the difference of integrals.
This leaf is solely an identity of real logarithmic integrals. -/
theorem log_integral_difference (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    (∫ t in (0 : ℝ)..1,
      (Real.log (2 * π) + (1 / 2) *
        Real.log (1 - 1 / (X * Real.exp u * (1 + m * u * t)) ^ 2)) * fm m t) -
    (∫ t in (0 : ℝ)..1,
      (Real.log (2 * π) + (1 / 2) *
        Real.log (1 - 1 / (X * (1 + m * u * t)) ^ 2)) * fm m t) =
    ∫ t in (0 : ℝ)..1,
      (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
        Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  have hδ : 0 ≤ (m : ℝ) * u := by positivity
  have hint (A : ℝ) (hA : 2 ≤ A) : IntervalIntegrable (fun t : ℝ =>
      (Real.log (2 * π) + (1 / 2) *
        Real.log (1 - 1 / (A * (1 + m * u * t)) ^ 2)) * fm m t)
      MeasureTheory.volume 0 1 := by
    have hZ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 2 ≤ A * (1 + m * u * t) := by
      have hp : 0 ≤ (m : ℝ) * u * t := mul_nonneg hδ ht.1
      nlinarith
    have hZ0 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < A * (1 + m * u * t) := by
      linarith [hZ t ht]
    have harg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        0 < 1 - 1 / (A * (1 + m * u * t)) ^ 2 := by
      have hz := hZ t ht
      have hsq : 1 < (A * (1 + m * u * t)) ^ 2 := by nlinarith
      have hd := (div_lt_one (by positivity : 0 < (A * (1 + m * u * t)) ^ 2)).mpr hsq
      linarith
    have hc : ContinuousOn (fun t : ℝ => Real.log (1 - 1 / (A * (1 + m * u * t)) ^ 2))
        (Set.Icc 0 1) := by
      apply ContinuousOn.log
      · apply ContinuousOn.sub continuousOn_const
        exact ContinuousOn.div continuousOn_const (by fun_prop)
          (fun t ht => pow_ne_zero _ (hZ0 t ht).ne')
      · intro t ht
        exact (harg t ht).ne'
    exact ((continuousOn_const.add (hc.const_mul (1 / 2 : ℝ))).mul
      (continuous_fm m).continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hX2 : 2 ≤ X := by linarith
  have hXE : 2 ≤ X * Real.exp u := by
    have he := Real.one_le_exp hu.le
    nlinarith
  rw [← intervalIntegral.integral_sub (hint (X * Real.exp u) hXE) (hint X hX2)]
  apply intervalIntegral.integral_congr
  intro t _
  have hup : X * Real.exp u * (1 + m * u * t) =
      Real.exp u * ((1 + m * u * t) * X) := by ring
  have hbot : X * (1 + m * u * t) = (1 + m * u * t) * X := by ring
  dsimp only
  rw [hup, hbot]
  ring

/-- The exact weighted_formula_total target of Decomp290c.
P0099 pp. 15 and 16, applied on p. 19. CONDITIONAL ON the three leaves. -/
theorem weighted_formula_total (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      (∑' i : ZI, zeroTerm m X u i).re -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hδ : 0 < (m : ℝ) * u := mul_pos hm0 hu
  have hX2 : 2 ≤ X := by linarith
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have hXE : 2 ≤ X * Real.exp u := by nlinarith
  have htop := scaled_weight_formula m (X * Real.exp u) (m * u) hm hXE hδ
  have hbot := scaled_weight_formula m X (m * u) hm hX2 hδ
  have hzero := zero_series_difference m X u hm hX hu hmu
  have hlog := log_integral_difference m X u hm hX hu hmu
  have hf : ContinuousOn (fm m) (Set.uIcc (0 : ℝ) 1) := (continuous_fm m).continuousOn
  have hItop := ((psi_affine_mono (c := X * Real.exp u) (by positivity) hδ.le).intervalIntegrable
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)).mul_continuousOn hf
  have hIbot := ((psi_affine_mono (c := X) (by linarith) hδ.le).intervalIntegrable
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)).mul_continuousOn hf
  have hpsi : (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1, ψ (X * Real.exp u * (1 + m * u * t)) * fm m t) -
      ∫ t in (0 : ℝ)..1, ψ (X * (1 + m * u * t)) * fm m t := by
    rw [← intervalIntegral.integral_sub hItop hIbot]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Dψ, sub_mul]
  have hmain : (∫ t in (0 : ℝ)..1,
      (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) =
      (∫ t in (0 : ℝ)..1, X * Real.exp u * (1 + m * u * t) * fm m t) -
      ∫ t in (0 : ℝ)..1, X * (1 + m * u * t) * fm m t := by
    rw [← intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; exact Continuous.mul (by fun_prop) (continuous_fm m))
      (by apply Continuous.intervalIntegrable; exact Continuous.mul (by fun_prop) (continuous_fm m))]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hpsi, hmain]
  linarith

end LeanLab.RamareSaouter2003.Decomp359d

#print axioms LeanLab.RamareSaouter2003.Decomp359d.scaled_weight_formula
#print axioms LeanLab.RamareSaouter2003.Decomp359d.zero_series_difference
#print axioms LeanLab.RamareSaouter2003.Decomp359d.log_integral_difference
#print axioms LeanLab.RamareSaouter2003.Decomp359d.weighted_formula_total
