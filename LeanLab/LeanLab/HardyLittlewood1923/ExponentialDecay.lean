import LeanLab.HardyLittlewood1923.WeightedMellin

/-!
AI wrote this Lean code for CODEX task52.
These convergence helpers justify the limiting contour shift after P0004 equation 2.416 on page 11.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace LeanLab.HardyLittlewood1923.Task52

lemma integrable_polynomial_exp_abs (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-δ * |t|)) := by
  have hp : IntegrableOn (fun t : ℝ => (1 + t) ^ k * Real.exp (-δ * t)) (Ioi 0) := by
    have he : (fun t : ℝ => (1 + t) ^ k * Real.exp (-δ * t)) =
        (fun t : ℝ => ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * t ^ (k - i) * Real.exp (-δ * t)) := by
      funext t
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [one_pow, one_mul]
      ring
    rw [he]
    apply integrable_finsetSum
    intro i hi
    have h : IntegrableOn (fun t : ℝ => t ^ (k - i) * Real.exp (-δ * t)) (Ioi 0) := by
      simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := ((k - i : ℕ) : ℝ)) (b := δ) (by linarith [Nat.cast_nonneg (α := ℝ) (k - i)]) (by norm_num) hδ
    simpa only [mul_assoc] using h.const_mul (k.choose i : ℝ)
  have hpos : IntegrableOn (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-δ * |t|)) (Ioi 0) :=
    hp.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hp' : IntegrableOn (fun t : ℝ => (1 + t) ^ k * Real.exp (-δ * t))
      (Ioi (-(0 : ℝ))) := by simpa only [neg_zero] using hp
  have hneg : IntegrableOn (fun t : ℝ => (1 + |t|) ^ k * Real.exp (-δ * |t|)) (Iio 0) := by
    have h := MeasureTheory.IntegrableOn.comp_neg_Iio (c := (0 : ℝ)) hp'
    refine h.congr_fun ?_ measurableSet_Iio
    intro t ht
    dsimp only
    rw [abs_of_neg ht]
  have hneg' := (integrableOn_Iic_iff_integrableOn_Iio).mpr hneg
  rw [← integrableOn_univ, ← (Iic_union_Ioi (a := (0 : ℝ))), integrableOn_union]
  exact ⟨hneg', hpos⟩

lemma polynomial_exp_tendsto_zero (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => (1 + T) ^ k * Real.exp (-δ * T)) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℝ => (2 : ℝ) ^ k * (T ^ k * Real.exp (-δ * T)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) δ hδ).const_mul
      ((2 : ℝ) ^ k)
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hp : (1 + T) ^ k ≤ (2 : ℝ) ^ k * T ^ k := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith)
      linarith
    have h := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-δ * T)).le
    simpa only [mul_assoc] using h

lemma vertical_eq_of_rectangle {f : ℂ → ℂ} {a b : ℝ}
    (hrect : ∀ T : ℝ, VIntegral f b (-T) T = VIntegral f a (-T) T -
      HIntegral f a b (-T) + HIntegral f a b T)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)))
    (hlo : Tendsto (fun T : ℝ => HIntegral f a b (-T)) atTop (𝓝 0))
    (hhi : Tendsto (fun T : ℝ => HIntegral f a b T) atTop (𝓝 0)) :
    (∫ t : ℝ, f ((b : ℂ) + t * I)) = ∫ t : ℝ, f ((a : ℂ) + t * I) := by
  have hla := (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_smul
    (I : ℂ)
  have hlb := (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_smul
    (I : ℂ)
  have hl : Tendsto (fun T : ℝ => VIntegral f a (-T) T - HIntegral f a b (-T) +
      HIntegral f a b T) atTop (𝓝 (I • ∫ t : ℝ, f ((a : ℂ) + t * I))) := by
    simpa only [VIntegral, sub_zero, add_zero, id_eq] using (hla.sub hlo).add hhi
  have he : (fun T : ℝ => I • ∫ t in (-T)..T, f ((b : ℂ) + t * I)) =
      (fun T : ℝ => VIntegral f a (-T) T - HIntegral f a b (-T) + HIntegral f a b T) := by
    funext T
    exact hrect T
  simp only [id_eq] at hlb
  rw [he] at hlb
  have hu := tendsto_nhds_unique hlb hl
  simp only [smul_eq_mul] at hu
  exact mul_left_cancel₀ Complex.I_ne_zero hu

#print axioms integrable_polynomial_exp_abs
#print axioms polynomial_exp_tendsto_zero
#print axioms vertical_eq_of_rectangle

end LeanLab.HardyLittlewood1923.Task52
