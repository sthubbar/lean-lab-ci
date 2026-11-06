import LeanLab.RamareSaouter2003.Decomp378a
import LeanLab.KadiriLumley2014.ZeroInterchange301

/-!
P0099 pp. 15 and 16, the integrated zero contributions of Lemma 4.
The psi1 form in Davenport Chapter 17 uses rho times rho plus one.
The existing PNTPort convergence theorem gives a uniform compact-interval majorant.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.ZeroPrimitive378
open Real Smooth L3Zeta Set MeasureTheory

/-- Derived auxiliary for P0099 p. 16, the convergent zero sum in Lemma 4.
The actual zero index including multiplicities is countable. -/
theorem index_countable : Countable ZI := by
  have : Countable LeanLab.PNTPort.ExplicitPsi1.Zall :=
    LeanLab.KadiriLumley2014.Task301.formula_zeros_countable.to_subtype
  infer_instance

/-- Derived auxiliary for P0099 p. 16 and the psi1 zero formula in Davenport Chapter 17.
On a positive interval from one through B, one zero primitive has norm at most
B squared times the reciprocal norm of rho times rho plus one. -/
theorem primitive_norm_le (y B : ℝ) (hy : 1 ≤ y) (hB : y ≤ B) (i : ZI) :
    ‖(y : ℂ) ^ ((i.1 : ℂ) + 1) / ((i.1 : ℂ) * ((i.1 : ℂ) + 1))‖ ≤
      B ^ 2 * (1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖) := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < y)]
  have hb : y ^ (((i.1 : ℂ) + 1).re) ≤ B ^ 2 := by
    simp only [Complex.add_re, Complex.one_re]
    calc
      _ ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by
        have hh : (i.1 : ℂ).re ≤ 1 := (bZ_mem i).2
        linarith)
      _ = y ^ 2 := by norm_cast
      _ ≤ B ^ 2 := pow_le_pow_left₀ (by linarith) hB 2
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hb (norm_nonneg _)

/-- Derived auxiliary for P0099 p. 16 and Davenport Chapter 17.
The actual psi1 zero primitive series converges absolutely at every y at least one. -/
theorem primitive_summable (y : ℝ) (hy : 1 ≤ y) :
    Summable (fun i : ZI =>
      (y : ℂ) ^ ((i.1 : ℂ) + 1) / ((i.1 : ℂ) * ((i.1 : ℂ) + 1))) :=
  Summable.of_norm_bounded (Decomp378a.reciprocal_product_summable.mul_left (y ^ 2))
    (primitive_norm_le y y hy le_rfl)

/-- Derived auxiliary for P0099 p. 16 and the psi1 formula in Davenport Chapter 17.
The primitive zero sum may be integrated term by term against the first derivative
of f_m at a positive affine scale. No count or explicit formula is assumed. -/
theorem weighted_primitive_interchange (m : ℕ) (A δ : ℝ) (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1,
      (∑' i : ZI, ((A * (1 + δ * t) : ℝ) : ℂ) ^ ((i.1 : ℂ) + 1) /
        ((i.1 : ℂ) * ((i.1 : ℂ) + 1))) *
          ((iteratedDeriv 1 (fm m) t : ℝ) : ℂ)) =
      ∑' i : ZI, ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ ((i.1 : ℂ) + 1) /
          ((i.1 : ℂ) * ((i.1 : ℂ) + 1))) *
            ((iteratedDeriv 1 (fm m) t : ℝ) : ℂ) := by
  haveI : Countable ZI := index_countable
  let B := A * (1 + δ)
  let D := iteratedDeriv 1 (fm m)
  let W : ZI → ℝ := fun i => 1 / ‖(i.1 : ℂ) * ((i.1 : ℂ) + 1)‖
  let F : ZI → ℝ → ℂ := fun i t =>
    (((A * (1 + δ * t) : ℝ) : ℂ) ^ ((i.1 : ℂ) + 1) /
      ((i.1 : ℂ) * ((i.1 : ℂ) + 1))) * (D t : ℂ)
  let bound : ZI → ℝ → ℝ := fun i t => B ^ 2 * W i * |D t|
  have hD : Continuous D := (Decomp1531a.contDiff_fm m).continuous_iteratedDeriv 1 (by simp)
  have hY (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 ≤ A * (1 + δ * t) ∧ A * (1 + δ * t) ≤ B := by
    dsimp only [B]
    have ha0 : 0 ≤ A := by linarith
    constructor
    · have hp : 0 ≤ A * (δ * t) := mul_nonneg ha0 (mul_nonneg hδ.le ht.1)
      nlinarith only [hA, hp]
    · apply mul_le_mul_of_nonneg_left _ ha0
      have hp := mul_nonneg hδ.le (sub_nonneg.mpr ht.2)
      nlinarith only [hp]
  have hcont (i : ZI) : ContinuousOn (F i) (Set.Icc 0 1) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div_const
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (by linarith [(hY t ht).1] : A * (1 + δ * t) ≠ 0))).comp_of_eq
          (by fun_prop : ContinuousAt (fun t : ℝ => A * (1 + δ * t)) t) rfl
    · exact (Complex.continuous_ofReal.comp hD).continuousOn
  have hmeas (i : ZI) : AEStronglyMeasurable (F i) (volume.restrict (Set.uIoc 0 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    exact ((hcont i).intervalIntegrable_of_Icc zero_le_one).1.aestronglyMeasurable
  have hb (i : ZI) : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ‖F i t‖ ≤ bound i t := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    dsimp only [F, bound, W]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (primitive_norm_le _ B (hY t ⟨ht.1.le, ht.2⟩).1 (hY t ⟨ht.1.le, ht.2⟩).2 i)
      (abs_nonneg _)
  have hs : Summable W := Decomp378a.reciprocal_product_summable
  have hsum : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → Summable (fun i => bound i t) := by
    exact Filter.Eventually.of_forall (fun t _ => (hs.mul_left (B ^ 2)).mul_right |D t|)
  have hint : IntervalIntegrable (fun t => ∑' i : ZI, bound i t) volume 0 1 := by
    simp only [bound, tsum_mul_right, tsum_mul_left]
    exact (continuous_const.mul hD.abs).intervalIntegrable 0 1
  have hlim : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → HasSum (fun i => F i t)
      ((∑' i : ZI, ((A * (1 + δ * t) : ℝ) : ℂ) ^ ((i.1 : ℂ) + 1) /
        ((i.1 : ℂ) * ((i.1 : ℂ) + 1))) * (D t : ℂ)) := by
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact (primitive_summable _ (hY t ⟨ht.1.le, ht.2⟩).1).hasSum.mul_right _
  exact (intervalIntegral.hasSum_integral_of_dominated_convergence bound hmeas hb hsum hint hlim).tsum_eq.symm

end LeanLab.RamareSaouter2003.ZeroPrimitive378
#print axioms LeanLab.RamareSaouter2003.ZeroPrimitive378.index_countable
#print axioms LeanLab.RamareSaouter2003.ZeroPrimitive378.primitive_norm_le
#print axioms LeanLab.RamareSaouter2003.ZeroPrimitive378.primitive_summable
#print axioms LeanLab.RamareSaouter2003.ZeroPrimitive378.weighted_primitive_interchange
