/-
Elementary sampling for P0069 page 11 display 3.3.
Existing declarations move here with their sealed statements unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp513a
open Set MeasureTheory

/-- P0069 page 11 display 3.3 and page 12, the elementary local sampling step.
For a real C1 function, its value at any point of a unit interval is at most
its integral plus the integral of the absolute derivative on that interval.
This is a supporting calculus inequality, not an extra printed paper claim.
Mathlib supplies the integral mean value theorem and the fundamental theorem. -/
theorem unit_interval_sampling (f g : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (g u) u) (hg : Continuous g)
    (a t : ℝ) (ht : t ∈ Icc a (a + 1)) :
    f t ≤ (∫ u in a..(a + 1), f u) + (∫ u in a..(a + 1), |g u|) := by
  have hab : a ≤ a + 1 := by linarith
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun u => (hf u).continuousAt)
  obtain ⟨c, hc, heq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) hfc.continuousOn
    (intervalIntegrable_const (a := a) (b := a + 1) (c := (1 : ℝ)))
    (by intros; norm_num)
  have hc' : c ∈ Icc a (a + 1) := by simpa only [uIcc_of_le hab] using hc
  have heq' : (∫ u in a..(a + 1), f u) = f c := by
    simpa using heq
  have hsub : uIoc c t ⊆ uIoc a (a + 1) := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Ioc (le_min hc'.1 ht.1) (max_le hc'.2 ht.2)
  have hid : (∫ u in c..t, g u) = f t - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hf u) (hg.intervalIntegrable _ _)
  have habs : 0 ≤ ∫ u in a..(a + 1), |g u| :=
    intervalIntegral.integral_nonneg hab (fun u hu => abs_nonneg _)
  have hd : |f t - f c| ≤ ∫ u in a..(a + 1), |g u| := by
    rw [← hid]
    calc
      _ ≤ |(∫ u in c..t, |g u|)| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_abs_integral_norm (f := g) (a := c) (b := t))
      _ ≤ |(∫ u in a..(a + 1), |g u|)| :=
        intervalIntegral.abs_integral_mono_interval hsub
          (Filter.Eventually.of_forall (fun u => abs_nonneg (g u))) (hg.abs.intervalIntegrable _ _)
      _ = _ := abs_of_nonneg habs
  rw [heq']
  linarith [le_abs_self (f t - f c)]
/-- P0069 page 11 display 3.3, the finite sampling passage for one character fiber.
Unit intervals starting at distinct one-spaced times are disjoint. Summing the
local calculus estimate therefore costs only the integral over the containing interval.
This is an elementary supporting statement with no cited analytic hypothesis. -/
theorem finite_spaced_sampling {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (f g : ℝ → ℝ) (hf : ∀ u, HasDerivAt f (g u) u) (hg : Continuous g)
    (hf0 : ∀ u, 0 ≤ f u)
    (hspace : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → 1 ≤ |t r - t s|)
    {T : ℝ} (hT : 0 ≤ T) (ht : ∀ r ∈ S, |t r| ≤ T) :
    (∑ r ∈ S, f (t r)) ≤ ∫ u in (-T)..(T + 1), f u + |g u| := by
  classical
  let W : ℝ → ℝ := fun u => f u + |g u|
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun u => (hf u).continuousAt)
  have hW : Continuous W := hfc.add hg.abs
  have hW0 (u : ℝ) : 0 ≤ W u := add_nonneg (hf0 u) (abs_nonneg _)
  have hpair : Set.Pairwise (S : Set ι)
      (fun r s => Disjoint (Ioc (t r) (t r + 1)) (Ioc (t s) (t s + 1))) := by
    intro r hr s hs hne
    have hd := hspace r hr s hs hne
    rcases le_total (t r) (t s) with h | h
    · apply Ioc_disjoint_Ioc_of_le
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hd
      linarith
    · apply Disjoint.symm
      apply Ioc_disjoint_Ioc_of_le
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hd
      linarith
  have hsub : (⋃ r ∈ S, Ioc (t r) (t r + 1)) ⊆ Ioc (-T) (T + 1) := by
    intro u hu
    obtain ⟨r, hr, hu⟩ := mem_iUnion₂.mp hu
    have hh := abs_le.mp (ht r hr)
    exact ⟨lt_of_le_of_lt hh.1 hu.1, by linarith [hu.2]⟩
  calc
    _ ≤ ∑ r ∈ S, ∫ u in (t r)..(t r + 1), W u := by
      apply Finset.sum_le_sum
      intro r hr
      have h := unit_interval_sampling f g hf hg (t r) (t r) ⟨le_rfl, by linarith⟩
      simpa only [W, intervalIntegral.integral_add
        (hfc.intervalIntegrable _ _) (hg.abs.intervalIntegrable _ _)] using h
    _ = ∑ r ∈ S, ∫ u in Ioc (t r) (t r + 1), W u := by
      apply Finset.sum_congr rfl
      intro r hr
      exact intervalIntegral.integral_of_le (by linarith)
    _ = ∫ u in ⋃ r ∈ S, Ioc (t r) (t r + 1), W u :=
      (integral_biUnion_finset S (fun r hr => measurableSet_Ioc) hpair
        (fun r hr => (hW.intervalIntegrable _ _).1)).symm
    _ ≤ ∫ u in Ioc (-T) (T + 1), W u :=
      setIntegral_mono_set (hW.intervalIntegrable _ _).1
        (Filter.Eventually.of_forall hW0) hsub.eventuallySubset
    _ = _ := (intervalIntegral.integral_of_le (by linarith)).symm
/-- P0069 page 11 display 3.3, the elementary sampling passage for all characters.
Apply the proved disjoint interval estimate separately to each character fiber and
sum by Finset.sum_fiberwise. The containing interval is independent of the character.
No analytic mean value estimate is supplied by this statement. -/
theorem character_spaced_sampling {q : ℕ}
    (S : Finset (ℝ × DirichletCharacter ℂ q))
    (f g : DirichletCharacter ℂ q → ℝ → ℝ)
    (hf : ∀ χ u, HasDerivAt (f χ) (g χ u) u) (hg : ∀ χ, Continuous (g χ))
    (hf0 : ∀ χ u, 0 ≤ f χ u) (hspace : Thm4.WellSpaced S)
    {T : ℝ} (hT : 0 ≤ T) (ht : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, f p.2 p.1) ≤
      ∑ χ : DirichletCharacter ℂ q, ∫ u in (-T)..(T + 1), f χ u + |g χ u| := by
  classical
  rw [← Finset.sum_fiberwise S Prod.snd (fun p => f p.2 p.1)]
  apply Finset.sum_le_sum
  intro χ hχ
  let P := S.filter (fun p => p.2 = χ)
  have hsub : P ⊆ S := Finset.filter_subset _ _
  have heq (p) (hp : p ∈ P) : p.2 = χ := (Finset.mem_filter.mp hp).2
  have hPspace : ∀ p ∈ P, ∀ r ∈ P, p ≠ r → 1 ≤ |p.1 - r.1| := by
    intro p hp r hr hne
    exact hspace p (hsub hp) r (hsub hr) hne ((heq p hp).trans (heq r hr).symm)
  have hs := finite_spaced_sampling P Prod.fst (f χ) (g χ) (hf χ) (hg χ) (hf0 χ)
    hPspace hT (fun p hp => ht p (hsub hp))
  calc
    _ = ∑ p ∈ P, f χ p.1 := Finset.sum_congr rfl (fun p hp => by rw [heq p hp])
    _ ≤ _ := hs
end LeanLab.BHP1997.Decomp513a

namespace LeanLab.BHP1997.Decomp513a
open Set MeasureTheory

/-- The scaled Schwarz step in Montgomery1971 page 3 Lemma 1.4 display 1.7.
Young's inequality bounds the variation term by two continuous square energies. -/
theorem character_square_sampling_scaled {q : ℕ}
    (S : Finset (ℝ × DirichletCharacter ℂ q))
    (f g : DirichletCharacter ℂ q → ℝ → ℂ)
    (hf : ∀ χ u, HasDerivAt (f χ) (g χ u) u) (hg : ∀ χ, Continuous (g χ))
    (hspace : Thm4.WellSpaced S) {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (ht : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖f p.2 p.1‖ ^ 2) ≤
      (1 + L) * (∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-T)..(T + 1), ‖f χ u‖ ^ 2) +
      L⁻¹ * (∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-T)..(T + 1), ‖g χ u‖ ^ 2) := by
  have hfc (χ : DirichletCharacter ℂ q) : Continuous (f χ) :=
    continuous_iff_continuousAt.mpr (fun u => (hf χ u).continuousAt)
  have hd (χ : DirichletCharacter ℂ q) (u : ℝ) :
      HasDerivAt (fun t => ‖f χ t‖ ^ 2) (2 * inner ℝ (f χ u) (g χ u)) u :=
    (hf χ u).norm_sq
  have hc (χ : DirichletCharacter ℂ q) :
      Continuous (fun u => 2 * inner ℝ (f χ u) (g χ u)) := by
    exact continuous_const.mul ((hfc χ).inner (hg χ))
  have hs := character_spaced_sampling S (fun χ u => ‖f χ u‖ ^ 2)
    (fun χ u => 2 * inner ℝ (f χ u) (g χ u)) hd hc
    (fun χ u => sq_nonneg _) hspace hT ht
  apply hs.trans
  have hiF (χ : DirichletCharacter ℂ q) :
      IntervalIntegrable (fun u => ‖f χ u‖ ^ 2) volume (-T) (T + 1) :=
    ((hfc χ).norm.pow 2).intervalIntegrable _ _
  have hiG (χ : DirichletCharacter ℂ q) :
      IntervalIntegrable (fun u => ‖g χ u‖ ^ 2) volume (-T) (T + 1) :=
    ((hg χ).norm.pow 2).intervalIntegrable _ _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ hχ
  calc
    _ ≤ ∫ u in (-T)..(T + 1), (1 + L) * ‖f χ u‖ ^ 2 + L⁻¹ * ‖g χ u‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((((hfc χ).norm.pow 2).add (hc χ).abs).intervalIntegrable _ _)
        (((((hfc χ).norm.pow 2).const_mul (1 + L)).add
          (((hg χ).norm.pow 2).const_mul L⁻¹)).intervalIntegrable _ _)
      intro u hu
      change ‖f χ u‖ ^ 2 + |2 * inner ℝ (f χ u) (g χ u)| ≤
        (1 + L) * ‖f χ u‖ ^ 2 + L⁻¹ * ‖g χ u‖ ^ 2
      have hinner := abs_real_inner_le_norm (f χ u) (g χ u)
      have hyoung := two_mul_le_add_mul_sq (a := ‖f χ u‖) (b := ‖g χ u‖) hL
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    _ = _ := by
      rw [intervalIntegral.integral_add ((hiF χ).const_mul _) ((hiG χ).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end LeanLab.BHP1997.Decomp513a
