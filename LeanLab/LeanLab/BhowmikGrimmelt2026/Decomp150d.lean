/-
Lemma 7.3, P0029 pages 26 and 27.
OPEN leaves for Jules. Every coefficient keeps its own smoothing scale N.
The assembly is CONDITIONAL. No varying family Parseval theorem is asserted.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.ApproximationError

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

private theorem integral_split_indicator150 {f : ℝ → ℂ} (hf : Continuous f) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (∫ α in (0 : ℝ)..1, f α) =
      (∫ α in (0 : ℝ)..1, Set.indicator s f α) +
      (∫ α in (0 : ℝ)..1, Set.indicator sᶜ f α) := by
  have hIoc : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hintf : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := hf.integrableOn_Ioc
  have hi1 : IntegrableOn f (Set.Ioc (0 : ℝ) 1 ∩ s) volume :=
    hintf.mono_set Set.inter_subset_left
  have hi2 : IntegrableOn f (Set.Ioc (0 : ℝ) 1 ∩ sᶜ) volume :=
    hintf.mono_set Set.inter_subset_left
  have hms1 : MeasurableSet (Set.Ioc (0 : ℝ) 1 ∩ s) := hIoc.inter hs
  have hms2 : MeasurableSet (Set.Ioc (0 : ℝ) 1 ∩ sᶜ) := hIoc.inter hs.compl
  have hdis : Disjoint (Set.Ioc (0 : ℝ) 1 ∩ s) (Set.Ioc (0 : ℝ) 1 ∩ sᶜ) := by
    rw [Set.disjoint_right]
    intro x hx hx'
    exact hx.2 hx'.2
  have hun : (Set.Ioc (0 : ℝ) 1 ∩ s) ∪ (Set.Ioc (0 : ℝ) 1 ∩ sᶜ) = Set.Ioc (0 : ℝ) 1 := by
    ext x
    simp
  have hiu : IntegrableOn f ((Set.Ioc (0 : ℝ) 1 ∩ s) ∪ (Set.Ioc (0 : ℝ) 1 ∩ sᶜ))
      (volume : Measure ℝ) := by
    rw [hun]
    exact hintf
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01,
    intervalIntegral.integral_of_le h01, setIntegral_indicator hs,
    setIntegral_indicator hs.compl]
  rw [← setIntegral_union hdis hms2 hi1 hi2, hun]

private theorem integral_split_if150 {f : ℝ → ℂ} (hf : Continuous f) (P : ℝ → Prop)
    (hs : MeasurableSet {α : ℝ | P α}) :
    (∫ α in (0 : ℝ)..1, f α) =
      (∫ α in (0 : ℝ)..1, if P α then f α else 0) +
      (∫ α in (0 : ℝ)..1, if P α then 0 else f α) := by
  have hind1 : (fun α => if P α then f α else 0) = Set.indicator {α : ℝ | P α} f := by
    funext α
    by_cases h : P α <;> simp [Set.indicator, h]
  have hind2 : (fun α => if P α then 0 else f α) = Set.indicator {α : ℝ | P α}ᶜ f := by
    funext α
    by_cases h : P α <;> simp [Set.indicator, h]
  rw [hind1, hind2, integral_split_indicator150 hf _ hs]

/-- LEAF. Page 26, exact error identity followed by the major and minor arc split.
OPEN elementary integrability step. ApproximationError already proves the unsplit identity. -/
theorem error_split150 {ϕ G : ℝ → ℝ} (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ) {η : ℝ} (hη : 0 < η) :
    (rphi ϕ N : ℂ) - (∫ α in (0 : ℝ)..1,
      Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
        (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))) =
      majorError150 ϕ G X N ϑ η + minorError150 ϕ G X N ϑ η := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXpos ϑ
  have hT : ∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ ϑ⌋₊, 0 < η * X * q / (X : ℝ) ^ ϑ := by
    intro q hqmem
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqmem).1
    have hq : 0 < (q : ℝ) := by exact_mod_cast hq1
    exact div_pos (mul_pos (mul_pos hη hXpos) hq) hR
  rw [rphi_sub_weighted_integral hG.supp hG.even ((X : ℝ) ^ ϑ)
    (fun q => η * X * q / (X : ℝ) ^ ϑ) hT ϕ N]
  have hcS := continuous_Sphi ϕ N
  have hcb := continuous_bRhat hG.supp hG.even ((X : ℝ) ^ ϑ)
    (fun q => η * X * q / (X : ℝ) ^ ϑ) hT
  have hce : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hfc : Continuous (fun α : ℝ => Sphi ϕ N α ^ 2 *
      (1 - bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) :=
    ((hcS.pow 2).mul (continuous_const.sub hcb)).mul hce
  rw [integral_split_if150 hfc (MajorArc X ((X : ℝ) ^ ϑ))
    (measurableSet_majorArc84 _ _)]
  rfl

/-- LEAF. Page 27, major arc contribution in the proof of 7.8.
OPEN family estimate. The written Parseval step uses one function, while Sphi depends on N.
A proof must control this actual varying family. Do not apply fixed function Bessel directly. -/
theorem major_family150 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF. Page 27, minor arc contribution in the proof of 7.8.
OPEN family estimate with the printed logarithm power five.
Both uniform smoothing control and the recorded logarithm question remain obligations. -/
theorem minor_family150 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- Exactly the sealed Lemma73 proposition. CONDITIONAL on the three OPEN leaves. -/
theorem lemma73_decomposed150 : Lemma73 := by
  intro ϕ G hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₁, hC₁, h₁⟩ := major_family150 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := minor_family150 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), ?_⟩
  intro X hX η hη hη' hscale
  have hmajor := h₁ X hX η hη hη' hscale
  have hminor := h₂ X hX η hη hη' hscale
  have hsum :
      (∑ N ∈ Finset.Icc 1 X, ‖(rphi ϕ N : ℂ) - ∫ α in (0 : ℝ)..1,
        Sphi ϕ N α ^ 2 * bRhat G ((X : ℝ) ^ ϑ)
          (fun q => η * X * q / (X : ℝ) ^ ϑ) α * ee (-(N * α))‖ ^ 2) ≤
      2 * ((∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) +
        ∑ N ∈ Finset.Icc 1 X, ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
    calc
      _ ≤ ∑ N ∈ Finset.Icc 1 X,
          2 * (‖majorError150 ϕ G X N ϑ η‖ ^ 2 + ‖minorError150 ϕ G X N ϑ η‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro N hN
        rw [error_split150 hG hX N ϑ hη]
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
      _ = _ := by rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hA : 0 ≤ ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) := by positivity
  have hB : 0 ≤ η ^ 4 := by positivity
  have hK : 0 ≤ (X : ℝ) ^ 3 * Real.log X ^ 5 := by
    have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
    positivity
  nlinarith [mul_nonneg hC₁ (mul_nonneg hA hK), mul_nonneg hC₂ (mul_nonneg hB hK)]

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.error_split150
#print axioms LeanLab.BhowmikGrimmelt2026.major_family150
#print axioms LeanLab.BhowmikGrimmelt2026.minor_family150
#print axioms LeanLab.BhowmikGrimmelt2026.lemma73_decomposed150
