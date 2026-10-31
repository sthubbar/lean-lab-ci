/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary mass and mean square bounds for the model in Lemma 3.2.
Source: pages 353 to 356.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelIntegral

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

/-- Absolute summability of the geometric model with arbitrary positive decay. -/
theorem damped_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => if 3 ≤ n then Real.exp (-t * n) else 0) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 0 ht
  simp only [pow_zero, one_mul] at h
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · split_ifs <;> positivity
  · split_ifs <;> first | exact le_rfl | positivity

/-- The mass starting at 3 is at most one divided by its positive decay. -/
theorem damped_mass_le (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, if 3 ≤ n then Real.exp (-t * n) else 0) ≤ 1 / t := by
  let b : ℕ → ℝ := fun n => if 3 ≤ n then Real.exp (-t * n) else 0
  let r := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := hasSum_geometric_of_lt_one hr.le hr1
  have hshift : (∑' n : ℕ, b (n + 1)) = ∑' n : ℕ, b n := by
    have h := (damped_summable t ht).sum_add_tsum_nat_add 1
    simpa [b] using h
  have he : ∀ n : ℕ, Real.exp (-t * (n + 1 : ℕ)) = r * r ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hs : Summable (fun n : ℕ => Real.exp (-t * (n + 1 : ℕ))) := by
    simp_rw [he]
    exact hgeom.summable.mul_left r
  have hle : ∀ n, b (n + 1) ≤ Real.exp (-t * (n + 1 : ℕ)) := by
    intro n
    unfold b
    split_ifs <;> first | exact le_rfl | positivity
  have hmass : (∑' n, b n) ≤ r / (1 - r) := by
    rw [← hshift]
    calc
      _ ≤ ∑' n : ℕ, Real.exp (-t * (n + 1 : ℕ)) :=
        Summable.tsum_le_tsum hle ((summable_nat_add_iff 1).mpr (damped_summable t ht)) hs
      _ = r / (1 - r) := by
        simp_rw [he]
        rw [tsum_mul_left, hgeom.tsum_eq]
        ring
  have hprod : r * Real.exp t = 1 := by
    change Real.exp (-t) * Real.exp t = 1
    rw [← Real.exp_add]
    simp
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) hr.le
  rw [hprod] at hh
  have hrat : r / (1 - r) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by linarith) ht]
    nlinarith
  exact hmass.trans hrat

/-- The model coefficient mass is at most N. -/
theorem modelMass_le (N : ℕ) (hN : 0 < N) : (∑' n, modelWeight N n) ≤ N := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := damped_mass_le (1 / N) (by positivity)
  have he : (fun n : ℕ => if 3 ≤ n then Real.exp (-(1 / (N : ℝ)) * n) else 0) =
      modelWeight N := by
    funext n
    unfold modelWeight
    congr 1
    congr 1
    ring
  rw [he] at h
  simpa using h

/-- The pointwise model bound used on page 354. -/
theorem norm_modelSum_le (N : ℕ) (hN : 0 < N) (α : ℝ) : ‖modelSum N α‖ ≤ N := by
  have h := le_of_tendsto ((continuous_norm.tendsto _).comp (modelPartial_tendsto hN α))
    (Eventually.of_forall fun M => norm_modelPartial_le hN M α)
  exact h.trans (modelMass_le N hN)

/-- The squared coefficient mass is at most N over 2. -/
theorem modelSquareMass_le (N : ℕ) (hN : 0 < N) :
    (∑' n, modelWeight N n ^ 2) ≤ (N : ℝ) / 2 := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : (fun n : ℕ => if 3 ≤ n then Real.exp (-(2 / (N : ℝ)) * n) else 0) =
      (fun n => modelWeight N n ^ 2) := by
    funext n
    unfold modelWeight
    split_ifs
    · rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    · norm_num
  have h := damped_mass_le (2 / N) (by positivity)
  rw [he] at h
  have hd : 1 / (2 / (N : ℝ)) = (N : ℝ) / 2 := by field_simp
  rw [hd] at h
  exact h

/-- Parseval for a finite model sum. -/
theorem modelPartial_parseval (N M : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖modelPartial N M α‖ ^ 2) =
      ∑ n ∈ Finset.range M, modelWeight N n ^ 2 := by
  let s : Finset ℤ := (Finset.range M).map Nat.castEmbedding
  let a : ℤ → ℂ := fun n => (modelWeight N n.toNat : ℂ)
  have he : ∀ α, modelPartial N M α = LeanLab.CircleOrth.S s a α := by
    intro α
    simp [modelPartial, LeanLab.CircleOrth.S, s, a]
  simp_rw [he]
  rw [parseval_norm]
  simp only [s, a, Finset.sum_map, Nat.castEmbedding_apply, Int.toNat_natCast,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The model mean square bound used in display 3.7. -/
theorem model_mean_square_le (N : ℕ) (hN : 0 < N) :
    (∫ α in (0 : ℝ)..1, ‖modelSum N α‖ ^ 2) ≤ (N : ℝ) / 2 := by
  have hs : Summable (fun n => modelWeight N n ^ 2) := by
    have he : (fun n : ℕ => if 3 ≤ n then Real.exp (-(2 / (N : ℝ)) * n) else 0) =
        (fun n => modelWeight N n ^ 2) := by
      funext n
      unfold modelWeight
      split_ifs
      · rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      · norm_num
    rw [← he]
    exact damped_summable _ (by positivity)
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (l := atTop)
    (F := fun M α => ‖modelPartial N M α‖ ^ 2)
    (f := fun α => ‖modelSum N α‖ ^ 2) (fun _ => (∑' n, modelWeight N n) ^ 2)
    (Eventually.of_forall fun M => ((continuous_modelPartial N M).norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun M => ae_of_all _ fun α _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_modelPartial_le hN M α) 2)
    intervalIntegrable_const
    (ae_of_all _ fun α _ => (((continuous_norm.tendsto _).comp
      (modelPartial_tendsto hN α)).pow 2))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro M
  rw [modelPartial_parseval]
  exact (hs.sum_le_tsum _ (fun n _ => sq_nonneg _)).trans (modelSquareMass_le N hN)

/-- The model cube integral has norm at most N squared over 2, as used in display 3.15. -/
theorem modelIntegral_norm_le (N : ℕ) (hN : 0 < N) :
    ‖modelIntegral N‖ ≤ (N : ℝ) ^ 2 / 2 := by
  unfold modelIntegral
  have hc := continuous_modelSum hN
  have hg : Continuous (fun α : ℝ => modelSum N α ^ 3 * ee (-((N : ℤ) * α))) :=
    (hc.pow 3).mul (continuous_ee.comp (continuous_const.mul continuous_id).neg)
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, ‖modelSum N α ^ 3 * ee (-((N : ℤ) * α))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ α in (0 : ℝ)..1, (N : ℝ) * ‖modelSum N α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hg.norm.intervalIntegrable 0 1)
        (((hc.norm.pow 2).const_mul N).intervalIntegrable 0 1)
      intro α hα
      rw [norm_mul, norm_ee, mul_one, norm_pow]
      calc
        ‖modelSum N α‖ ^ 3 = ‖modelSum N α‖ * ‖modelSum N α‖ ^ 2 := by ring
        _ ≤ (N : ℝ) * ‖modelSum N α‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_modelSum_le N hN α) (sq_nonneg _)
    _ = (N : ℝ) * ∫ α in (0 : ℝ)..1, ‖modelSum N α‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (N : ℝ) * ((N : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (model_mean_square_le N hN) (Nat.cast_nonneg _)
    _ = _ := by ring

end LeanLab.Zinoviev1997
