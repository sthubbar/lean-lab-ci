import LeanLab.ChenDoubleSieve.Decomp349bSplitSum

/-!
Proof of the LEAF `leaf_switched_integral_eval` of Decomp349bSplitSum, Wu 2004 page 41,
evaluation of the double integrals of 10.9 and 10.11. Source: https://arxiv.org/pdf/0705.1652.
The inner integral is done by partial fractions; for coordinates six and seven the outer
integral is transformed by s equal 1 over t minus 1.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory intervalIntegral
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- Partial fractions: the integral of 1 over u times c minus u from s to c/2 is
log of c minus s over s, divided by c. -/
theorem ie_inner_integral {c s : ℝ} (hs : 0 < s) (hsc : s ≤ c / 2) :
    ∫ u in s..c / 2, 1 / ((c - u) * u) = log ((c - s) / s) / c := by
  have hc : 0 < c := by linarith
  have key : ∀ u ∈ uIcc s (c / 2), 1 / ((c - u) * u) = (1 / c) * (u⁻¹ + (c - u)⁻¹) := by
    intro u hu
    rw [uIcc_of_le hsc] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hcu : 0 < c - u := by linarith [hu.2]
    field_simp
    ring
  have hi1 : IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume s (c / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu
    rw [uIcc_of_le hsc] at hu
    exact (by linarith [hu.1] : (0:ℝ) < u).ne'
  have hi2 : IntervalIntegrable (fun u : ℝ => (c - u)⁻¹) MeasureTheory.volume s (c / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro u hu
    rw [uIcc_of_le hsc] at hu
    exact (by linarith [hu.2] : (0:ℝ) < c - u).ne'
  have h1 : ∫ u in s..c / 2, u⁻¹ = log ((c / 2) / s) := integral_inv_of_pos hs (by linarith)
  have h2 : ∫ u in s..c / 2, (c - u)⁻¹ = log ((c - s) / (c - c / 2)) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) c (a := s) (b := c / 2)
    rw [this]
    exact integral_inv_of_pos (by linarith) (by linarith)
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi1 hi2, h1, h2,
    ← log_mul (by positivity) (by have : 0 < c - s := by linarith
                                  have : 0 < c - c / 2 := by linarith
                                  positivity)]
  rw [one_div_mul_eq_div]
  have hcc : c - c / 2 ≠ 0 := by
    have : 0 < c - c / 2 := by linarith
    exact this.ne'
  congr 2
  field_simp
  ring

/-- Wu 2004 page 41: the inner integral of the switched integrand, from a lower end s to
1 minus t over 2. -/
theorem ie_inner {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ (1 - t) / 2) :
    ∫ u in s..((1 - t) / 2), 1 / (t * u * (1 - t - u)) =
      log ((1 - t - s) / s) / (t * (1 - t)) := by
  have h := ie_inner_integral (c := 1 - t) hs hst
  have hfun : (fun u : ℝ => 1 / (t * u * (1 - t - u))) =
      fun u => (1 / t) * (1 / ((1 - t - u) * u)) := by
    funext u
    rw [one_div_mul_one_div]
    ring_nf
  rw [hfun, intervalIntegral.integral_const_mul, h]
  have h1t : (0 : ℝ) < 1 - t := by linarith
  field_simp

/-- Wu 2004 page 41, the substitution s equal 1 over t minus 1: for 0 < σ ≤ 1/3 the
integral from σ to 1/3 of log of 1 minus 2 t over t, over t times 1 minus t, equals the
integral from 2 to 1/σ minus 1 of log of s minus 1 over s. -/
theorem ie_subst {σ : ℝ} (hσ : 0 < σ) (hσ3 : σ ≤ 1 / 3) :
    ∫ t in σ..(1 / 3 : ℝ), log ((1 - t - t) / t) / (t * (1 - t)) =
      ∫ s in (2 : ℝ)..(1 / σ - 1), log (s - 1) / s := by
  set f : ℝ → ℝ := fun t => 1 / t - 1 with hf
  set f' : ℝ → ℝ := fun t => -(t ^ 2)⁻¹ with hf'
  set g : ℝ → ℝ := fun s => log (s - 1) / s with hg
  have hI : uIcc σ (1 / 3 : ℝ) = Icc σ (1 / 3) := uIcc_of_le hσ3
  have hderiv : ∀ x ∈ uIcc σ (1 / 3 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    rw [hI] at hx
    have hx0 : x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < x).ne'
    have := ((hasDerivAt_inv hx0).sub_const 1)
    simpa [hf, hf', one_div] using this
  have hcont' : ContinuousOn f' (uIcc σ (1 / 3 : ℝ)) := by
    rw [hI]
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (by linarith [hx.1] : (0 : ℝ) < x).ne'
  have himg : f '' uIcc σ (1 / 3 : ℝ) ⊆ Ici 2 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hI] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    simp only [hf, Set.mem_Ici]
    rw [le_sub_iff_add_le, le_div_iff₀ hx0]
    linarith [hx.2]
  have hgc : ContinuousOn g (f '' uIcc σ (1 / 3 : ℝ)) := by
    apply ContinuousOn.mono _ himg
    apply ContinuousOn.div _ continuousOn_id
    · intro s hs; exact (by linarith [Set.mem_Ici.mp hs] : (0 : ℝ) < s).ne'
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro s hs; exact (by linarith [Set.mem_Ici.mp hs] : (0 : ℝ) < s - 1).ne'
  have hcv := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hgc
  have hfa : f σ = 1 / σ - 1 := rfl
  have hfb : f (1 / 3) = 2 := by simp only [hf]; norm_num
  rw [hfa, hfb] at hcv
  have h2 := intervalIntegral.integral_symm (μ := volume) (f := g) (1 / σ - 1) 2
  change _ = ∫ s in (2 : ℝ)..(1 / σ - 1), g s
  rw [h2, ← hcv, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [hI] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hlog : (1 - x - x) / x = 1 / x - 1 - 1 := by field_simp
  simp only [Function.comp, hf, hf', hg]
  rw [hlog]
  field_simp

/-- `leaf_switched_integral_eval`, exactly as stated in Decomp349bSplitSum, Wu 2004
page 41: evaluation of the double integrals, giving the coefficients of 10.9 and 10.11. -/
theorem leaf_switched_integral_eval_proved :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      8 * switchedIntegral i =
        integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  have hs1 : (0 : ℝ) < sigma1 := by norm_num [sigma1]
  have hs2 : (0 : ℝ) < sigma2 := by norm_num [sigma2]
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hfree : ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 3 →
      ∫ t in σ..(1 / 3 : ℝ), ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u)) =
        ∫ s in (2 : ℝ)..(1 / σ - 1), log (s - 1) / s := by
    intro σ hσ hσ3
    rw [← ie_subst hσ hσ3]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hσ3] at ht
    exact ie_inner (by linarith [ht.1]) (by linarith [ht.1]) (by linarith [ht.2])
  rcases hi with rfl | rfl | rfl
  · simp only [switchedIntegral, show (6 : Fin 12) ≠ 9 by decide, ↓reduceIte]
    rw [hfree sigma1 hs1 (by norm_num [sigma1])]
    simp [integralTerms]
  · simp only [switchedIntegral, show (7 : Fin 12) ≠ 9 by decide,
      show (7 : Fin 12) ≠ 6 by decide, ↓reduceIte]
    rw [hfree sigma2 hs2 (by norm_num [sigma2])]
    simp [integralTerms]
  · simp only [switchedIntegral, ↓reduceIte]
    have hin : ∫ t in kappa2..sigma2, ∫ u in sigma2..((1 - t) / 2), 1 / (t * u * (1 - t - u)) =
        ∫ t in kappa2..sigma2, log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num [kappa2, sigma2])] at ht
      have hle : sigma2 ≤ (1 - t) / 2 := by
        have h3 : sigma2 ≤ 1 / 3 := by norm_num [sigma2]
        linarith [ht.2]
      dsimp only
      rw [ie_inner (by linarith [ht.1]) hs2 hle]
      congr 2
      field_simp
      ring
    rw [hin]
    simp [integralTerms]

end LeanLab.ChenDoubleSieve.Task349

