/-
P0068 Zhan 1991, proof of the LEAF `moment_swap_leaf_S9` of SPLIT_fj0_moment_S9.lean, page 266,
the step from the first to the second line after "By Lemma 2" in the proof of Proposition 1:
integrate the pointwise bound in `t`, sum over the characters, and exchange the `t` and `v`
integrals. Burst 20261124, session S9, unit B-extra-4. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_fj0_moment_S9

namespace LeanLab.Zhan1991
open Finset Real MeasureTheory

noncomputable section

/-- PROVED: the translation `∫_{T₁+v}^{T₁+v+H} g = ∫_{T₁}^{T₁+H} g(t+v) dt`. -/
theorem shift_Ioc_S9 (g : ℝ → ℝ) (T1 H v : ℝ) (hH : 0 ≤ H) :
    ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g t = ∫ t in T1..(T1 + H), g (t + v) := by
  rw [intervalIntegral.integral_comp_add_right, intervalIntegral.integral_of_le (by linarith),
    show T1 + H + v = T1 + v + H by ring]

/-- PROVED: `t ↦ ∫_{-R}^{R} g(t+v) dv/(1+|v|)` is continuous for continuous `g`. -/
theorem Phi_cont_S9 (g : ℝ → ℝ) (hg : Continuous g) (R : ℝ) :
    Continuous (fun t => ∫ v in (-R)..R, g (t + v) / (1 + |v|)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hg.comp (by fun_prop)).div (by fun_prop) (fun p => by positivity)

/-- PROVED: `v ↦ ∫_{T₁}^{T₁+H} g(t+v) dt` is continuous for continuous `g`. -/
theorem W_cont_S9 (g : ℝ → ℝ) (hg : Continuous g) (T1 H : ℝ) :
    Continuous (fun v => ∫ t in T1..(T1 + H), g (t + v)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hg.comp (by fun_prop)

/-- PROVED: Tonelli for one character, page 266: the `t` and `v` integrals exchange. -/
theorem swap_one_S9 (g : ℝ → ℝ) (hg : Continuous g) (R T1 H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) :
    ∫ t in Set.Ioc T1 (T1 + H), ∫ v in Set.Ioc (-R) R, g (t + v) / (1 + |v|)
      = ∫ v in Set.Ioc (-R) R, (∫ t in Set.Ioc (T1 + v) (T1 + v + H), g t) / (1 + |v|) := by
  have hF : Continuous (fun p : ℝ × ℝ => g (p.1 + p.2) / (1 + |p.2|)) :=
    (hg.comp (by fun_prop)).div (by fun_prop) (fun p => by positivity)
  have hint : Integrable (Function.uncurry fun t v => g (t + v) / (1 + |v|))
      ((volume.restrict (Set.Ioc T1 (T1 + H))).prod (volume.restrict (Set.Ioc (-R) R))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [integral_integral_swap hint]
  congr 1; funext v
  rw [integral_div, shift_Ioc_S9 g T1 H v hH, intervalIntegral.integral_of_le (by linarith)]

/-- PROVED: the statement of the LEAF `moment_swap_leaf_S9`, page 266. -/
theorem moment_swap_proof_S9 {ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (hg0 : ∀ i ∈ s, ∀ t, 0 ≤ g i t) (K L R T1 H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (h : ∀ i ∈ s, ∀ t ∈ Set.Ioc T1 (T1 + H),
      f i t ≤ K * (L * (∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + 1)) :
    ∑ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H), f i t
      ≤ K * (L * (∫ v in Set.Ioc (-R) R,
          (∑ i ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g i t) / (1 + |v|)) + s.card * H) := by
  have hPc : ∀ i ∈ s, Continuous (fun t => ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) := by
    intro i hi
    have e : (fun t => ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) =
        fun t => ∫ v in (-R)..R, g i (t + v) / (1 + |v|) := by
      funext t; exact (intervalIntegral.integral_of_le (by linarith)).symm
    rw [e]; exact Phi_cont_S9 (g i) (hg i hi) R
  have hvol : volume.real (Set.Ioc T1 (T1 + H)) = H := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring
  have step1 : ∀ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H), f i t ≤
      K * (L * (∫ t in Set.Ioc T1 (T1 + H), ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + H) := by
    intro i hi
    have hP := hPc i hi
    have hc : Continuous (fun t =>
        K * (L * (∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + 1)) := by fun_prop
    calc ∫ t in Set.Ioc T1 (T1 + H), f i t
        ≤ ∫ t in Set.Ioc T1 (T1 + H),
            K * (L * (∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + 1) :=
          setIntegral_mono_on ((hf i hi).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
            (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc (h i hi)
      _ = K * (L * (∫ t in Set.Ioc T1 (T1 + H), ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|))
            + H) := by
          rw [integral_const_mul, integral_add, integral_const_mul, setIntegral_const, hvol,
            smul_eq_mul, mul_one]
          · exact (continuous_const.mul hP).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
          · exact continuous_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hWi : ∀ i ∈ s, Continuous (fun v =>
      (∫ t in Set.Ioc (T1 + v) (T1 + v + H), g i t) / (1 + |v|)) := by
    intro i hi
    have e : (fun v => (∫ t in Set.Ioc (T1 + v) (T1 + v + H), g i t) / (1 + |v|)) =
        fun v => (∫ t in T1..(T1 + H), g i (t + v)) / (1 + |v|) := by
      funext v; rw [shift_Ioc_S9 (g i) T1 H v hH]
    rw [e]
    exact (W_cont_S9 (g i) (hg i hi) T1 H).div (by fun_prop) (fun v => by positivity)
  have key : ∑ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H), ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)
      = ∫ v in Set.Ioc (-R) R,
          (∑ i ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g i t) / (1 + |v|) := by
    rw [Finset.sum_congr rfl (fun i hi => swap_one_S9 (g i) (hg i hi) R T1 H hR hH)]
    rw [← integral_finsetSum _ (fun i hi =>
      (hWi i hi).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
    congr 1; funext v; rw [Finset.sum_div]
  calc ∑ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H), f i t
      ≤ ∑ i ∈ s, K * (L * (∫ t in Set.Ioc T1 (T1 + H),
          ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + H) := Finset.sum_le_sum step1
    _ = K * (L * (∑ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H),
          ∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + s.card * H) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul]
    _ = _ := by rw [key]

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.shift_Ioc_S9
#print axioms LeanLab.Zhan1991.swap_one_S9
#print axioms LeanLab.Zhan1991.moment_swap_proof_S9
