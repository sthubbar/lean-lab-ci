/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The elementary model in Lemma 3.3, pages 356 to 357.
We use the reflected Fourier convention of Series.lean.
The factor exp -1 follows the proof on page 356.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Theorem34

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

/-- The coefficients of the unweighted model starting at 3. -/
noncomputable def modelWeight (N n : ℕ) : ℝ :=
  if 3 ≤ n then Real.exp (- (n : ℝ) / N) else 0

/-- The reflected model series of Lemma 3.2, page 352. -/
noncomputable def modelSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑' n : ℕ, (modelWeight N n : ℂ) * ee (n * α)

/-- Finite truncations of the model series. -/
noncomputable def modelPartial (N M : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ range M, (modelWeight N n : ℂ) * ee (n * α)

/-- The model integral over a full period in the reflected convention. -/
noncomputable def modelIntegral (N : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, modelSum N α ^ 3 * ee (-((N : ℤ) * α))

theorem modelWeight_nonneg (N n : ℕ) : 0 ≤ modelWeight N n := by
  unfold modelWeight
  split_ifs <;> positivity

theorem summable_modelWeight {N : ℕ} (hN : 0 < N) : Summable (modelWeight N) := by
  have hr : (0 : ℝ) < 1 / N := by positivity
  have h := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  simp only [pow_zero, one_mul] at h
  refine Summable.of_nonneg_of_le (modelWeight_nonneg N) (fun n => ?_) h
  unfold modelWeight
  split_ifs
  · apply le_of_eq; congr 1; ring
  · positivity

theorem norm_modelTerm (N n : ℕ) (α : ℝ) :
    ‖(modelWeight N n : ℂ) * ee (n * α)‖ = modelWeight N n := by
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (modelWeight_nonneg N n)]

theorem modelPartial_tendsto {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Tendsto (fun M => modelPartial N M α) atTop (𝓝 (modelSum N α)) := by
  apply (Summable.of_norm (f := fun n : ℕ =>
    (modelWeight N n : ℂ) * ee (n * α)) ?_).hasSum.tendsto_sum_nat
  simp_rw [norm_modelTerm]
  exact summable_modelWeight hN

theorem continuous_modelPartial (N M : ℕ) : Continuous (modelPartial N M) := by
  unfold modelPartial
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id))

theorem continuous_modelSum {N : ℕ} (hN : 0 < N) : Continuous (modelSum N) := by
  exact continuous_tsum (fun n =>
    continuous_const.mul (continuous_ee.comp (continuous_const.mul continuous_id)))
    (summable_modelWeight hN) (fun n α => (norm_modelTerm N n α).le)

theorem norm_modelPartial_le {N : ℕ} (hN : 0 < N) (M : ℕ) (α : ℝ) :
    ‖modelPartial N M α‖ ≤ ∑' n, modelWeight N n := by
  unfold modelPartial
  calc
    ‖∑ n ∈ range M, (modelWeight N n : ℂ) * ee (n * α)‖ ≤
        ∑ n ∈ range M, ‖(modelWeight N n : ℂ) * ee (n * α)‖ := norm_sum_le _ _
    _ = ∑ n ∈ range M, modelWeight N n := by simp_rw [norm_modelTerm]
    _ ≤ ∑' n, modelWeight N n :=
      (summable_modelWeight hN).sum_le_tsum _ (fun n _ => modelWeight_nonneg N n)

/-- The model has the same total damping on every contributing triple. -/
theorem modelWeight_triple {N x y z : ℕ} (hN : 0 < N)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) (h : x + y + z = N) :
    modelWeight N x * modelWeight N y * modelWeight N z = Real.exp (-1) := by
  simp only [modelWeight, ite_eq_left hx, ite_eq_left hy, ite_eq_left hz]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : (x : ℝ) + y + z = N := by exact_mod_cast h
  field_simp
  linarith

/-- The finite model cube is a weighted triple count by orthogonality. -/
theorem modelPartial_cube (N M : ℕ) :
    ∫ α in (0 : ℝ)..1, modelPartial N M α ^ 3 * ee (-((N : ℤ) * α)) =
      ∑ x ∈ range M, ∑ y ∈ range M, ∑ z ∈ range M,
        if x + y + z = N then
          ((modelWeight N x * modelWeight N y * modelWeight N z : ℝ) : ℂ) else 0 := by
  let s : Finset ℤ := (range M).map Nat.castEmbedding
  let a : ℤ → ℂ := fun n => (modelWeight N n.toNat : ℂ)
  have he : ∀ α, modelPartial N M α = LeanLab.CircleOrth.S s a α := by
    intro α
    simp [modelPartial, LeanLab.CircleOrth.S, s, a]
  simp_rw [he]
  rw [ternary_orth]
  simp only [s, Finset.sum_map, Nat.castEmbedding_apply, a, Int.toNat_natCast]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  have hi : (x : ℤ) + y + z = N ↔ x + y + z = N := by omega
  simp only [hi, Complex.ofReal_mul]

/-- Once the cutoff exceeds N the finite model cube is S N divided by e. -/
theorem modelPartial_cube_count (N M : ℕ) (hN : 0 < N) (hM : N < M) :
    ∫ α in (0 : ℝ)..1, modelPartial N M α ^ 3 * ee (-((N : ℤ) * α)) =
      ((S N : ℝ) / Real.exp 1 : ℂ) := by
  rw [modelPartial_cube]
  let t := ((range M ×ˢ range M ×ˢ range M).filter
    (fun t => 3 ≤ t.1 ∧ 3 ≤ t.2.1 ∧ 3 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = N))
  have ht : t.card = S N := by
    apply congrArg Finset.card
    ext ⟨x, y, z⟩
    simp only [t, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hw : ∀ x y z : ℕ,
      (if x + y + z = N then
        ((modelWeight N x * modelWeight N y * modelWeight N z : ℝ) : ℂ) else 0) =
      if 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ x + y + z = N then
        (Real.exp (-1) : ℂ) else 0 := by
    intro x y z
    by_cases hx : 3 ≤ x <;> by_cases hy : 3 ≤ y <;>
      by_cases hz : 3 ≤ z <;> by_cases hs : x + y + z = N
    all_goals first
      | simp [hx, hy, hz, hs, modelWeight_triple hN hx hy hz hs]
      | simp [modelWeight, hx, hy, hz, hs]
  simp_rw [hw]
  have heq : (∑ x ∈ range M, ∑ y ∈ range M, ∑ z ∈ range M,
      if 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ x + y + z = N then
        (Real.exp (-1) : ℂ) else 0) = t.card * (Real.exp (-1) : ℂ) := by
    calc
      _ = ∑ v ∈ t, (Real.exp (-1) : ℂ) := by
        simp only [t, Finset.sum_filter, Finset.sum_product]
      _ = _ := by simp
  rw [heq, ht, Real.exp_neg]
  push_cast
  ring

/-- Lemma 3.3 has no GRH input. The integral equals the damped triple count. -/
theorem modelIntegral_eq_count {N : ℕ} (hN : 0 < N) :
    modelIntegral N = ((S N : ℝ) / Real.exp 1 : ℂ) := by
  set B := ∑' n, modelWeight N n
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (l := atTop)
    (F := fun M α => modelPartial N M α ^ 3 * ee (-((N : ℤ) * α)))
    (f := fun α => modelSum N α ^ 3 * ee (-((N : ℤ) * α))) (fun _ => B ^ 3)
    (Eventually.of_forall fun M => (((continuous_modelPartial N M).pow 3).mul
      (continuous_ee.comp (continuous_const.mul continuous_id).neg)).aestronglyMeasurable)
    (Eventually.of_forall fun M => ae_of_all _ fun α _ => by
      rw [norm_mul, norm_ee, mul_one, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_modelPartial_le hN _ α) 3)
    intervalIntegrable_const
    (ae_of_all _ fun α _ => ((modelPartial_tendsto hN α).pow 3).mul tendsto_const_nhds)
  have hc : Tendsto (fun M => ∫ α in (0 : ℝ)..1,
      modelPartial N M α ^ 3 * ee (-((N : ℤ) * α))) atTop
      (𝓝 (((S N : ℝ) / Real.exp 1 : ℂ))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop N] with M hM
    exact (modelPartial_cube_count N M hN hM).symm
  exact tendsto_nhds_unique h hc

/-- The exact polynomial form from the proof of Lemma 3.3. -/
theorem modelIntegral_eq_polynomial (N : ℕ) (hN : 8 ≤ N) :
    modelIntegral N =
      ((((N : ℝ) - 8) * ((N : ℝ) - 7) / 2 / Real.exp 1 : ℝ) : ℂ) := by
  rw [modelIntegral_eq_count (by omega)]
  have hc := lemma33_count N hN
  have hr : (2 : ℝ) * S N = ((N : ℝ) - 8) * ((N : ℝ) - 7) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hc
    push_cast [Nat.cast_sub hN, Nat.cast_sub (show 7 ≤ N by omega)] at h
    exact h
  rw [show (S N : ℝ) = ((N : ℝ) - 8) * ((N : ℝ) - 7) / 2 by nlinarith [hr]]
  push_cast
  rfl

/-- The bounded theta form used in the proof of Theorem 3.4. -/
theorem modelIntegral_theta (N : ℕ) (hN : 8 ≤ N) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ modelIntegral N =
      ((((N : ℝ) ^ 2 / 2 + 8 * θ * N) / Real.exp 1 : ℝ) : ℂ) := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  obtain ⟨θ, hθ, heq⟩ := lemma33_theta N hn
  exact ⟨θ, hθ, by rw [modelIntegral_eq_polynomial N hN, heq]⟩

/-- A concrete nonzero model integral. The only triple is 3 plus 3 plus 3. -/
theorem modelIntegral_nine : modelIntegral 9 = ((1 / Real.exp 1 : ℝ) : ℂ) := by
  rw [modelIntegral_eq_count (by norm_num : 0 < (9 : ℕ))]
  have hc : S 9 = 1 := by
    have h := lemma33_count 9 (by norm_num)
    norm_num at h
    omega
  rw [hc]
  norm_num

end LeanLab.Zinoviev1997
