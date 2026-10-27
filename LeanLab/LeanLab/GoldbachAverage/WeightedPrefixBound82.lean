import LeanLab.GoldbachAverage.WeightedPrefix82

/-!
The Cauchy Schwarz step in P0051 page 10 eq. 54.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedPrefixBound82
open MeasureTheory Filter Set
open FloorVariance82 WeightedPrefix82

/-- The counting function R is in every Lp space on a finite positive interval.
Source: the integrals of R used in P0051 eqs. 51 and 54, page 10. -/
theorem R_memLp {x : ℝ} (hx : 0 ≤ x) (p : ENNReal) :
    MemLp psiFloorError p (volume.restrict (Ioc (0 : ℝ) x)) := by
  refine MemLp.of_bound measurable_psiFloorError.aestronglyMeasurable
    (Chebyshev.psi x + x + 1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, psiFloorError, abs_le]
  have h0 := Chebyshev.psi_nonneg t
  have h1 := Chebyshev.psi_nonneg x
  have h2 := Chebyshev.psi_mono ht.2
  have h3 := Int.fract_nonneg t
  have h4 := Int.fract_lt_one t
  constructor <;> linarith [ht.1, ht.2]

/-- LEAF. The weighted R integral has the Cauchy Schwarz bound used in eq. 54.
Source: P0051 page 10. -/
theorem weighted_R_integral_sq (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, psiFloorError t * Real.exp (-t / N)) ^ 2 ≤
      x * (∫ t in (0 : ℝ)..x, psiFloorError t ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hRa : MemLp (fun t : ℝ => |psiFloorError t|) (ENNReal.ofReal 2)
      (volume.restrict (Ioc (0 : ℝ) x)) := by
    simpa only [Real.norm_eq_abs] using (R_memLp hx (ENNReal.ofReal 2)).norm
  have hOne : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Ioc (0 : ℝ) x)) := by
    exact MemLp.of_bound measurable_const.aestronglyMeasurable 1
      (Eventually.of_forall fun _ => by simp)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc (0 : ℝ) x)) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall fun t => abs_nonneg (psiFloorError t))
    (Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1)) hRa hOne
  norm_num only [Real.rpow_two, one_pow, mul_one, sq_abs] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hcs : (∫ t in (0 : ℝ)..x, |psiFloorError t|) ≤
      Real.sqrt (∫ t in (0 : ℝ)..x, psiFloorError t ^ 2) * Real.sqrt x := by
    simpa [intervalIntegral.integral_of_le hx, max_eq_left hx] using hh
  have hRi : IntervalIntegrable psiFloorError volume 0 x := by
    refine ⟨memLp_one_iff_integrable.mp (R_memLp hx 1), ?_⟩
    rw [Set.Ioc_eq_empty_of_le hx]
    exact integrableOn_empty
  have hn : ‖∫ t in (0 : ℝ)..x, psiFloorError t * Real.exp (-t / N)‖ ≤
      ∫ t in (0 : ℝ)..x, |psiFloorError t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx ?_ hRi.abs
    exact Eventually.of_forall fun t ht => by
      have he : Real.exp (-t / N) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have ht0 : 0 ≤ t := le_of_lt ht.1
        simpa only [neg_div] using neg_nonpos.mpr (div_nonneg ht0 hN0.le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (psiFloorError t))
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..x, psiFloorError t ^ 2 :=
    intervalIntegral.integral_nonneg hx (fun _ _ => sq_nonneg _)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hn.trans hcs) 2
  rw [mul_pow, Real.sq_sqrt hnonneg, Real.sq_sqrt hx, Real.norm_eq_abs, sq_abs] at hs
  simpa only [mul_comm] using hs

/-- The finite weighted prefix is measurable as a function of its real endpoint.
Source: the square integral I1 in P0051 page 9 eq. 49. -/
theorem measurable_weightedPrefix (N : ℕ) : Measurable (weightedPrefix N) := by
  let g : ℕ → ℝ := fun m => ∑ n ∈ Finset.Icc 0 m, Real.exp (-(n : ℝ) / N) * cfr n
  exact (measurable_of_countable g).comp Nat.measurable_floor

/-- LEAF. P0051 page 10 eq. 54, with explicit constant eight.
For h at most N the integral of the weighted prefix squared is at most eight H h plus eight h. -/
theorem weighted_prefix_square_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ}
    (hh : 0 ≤ h) (hhN : h ≤ N) :
    (∫ t in (0 : ℝ)..h, weightedPrefix N t ^ 2) ≤ 8 * InghamTheta.H h + 8 * h := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR2i : IntervalIntegrable (fun t : ℝ => psiFloorError t ^ 2) volume 0 h := by
    refine ⟨(memLp_two_iff_integrable_sq measurable_psiFloorError.aestronglyMeasurable).mp
      (R_memLp hh 2), ?_⟩
    rw [Set.Ioc_eq_empty_of_le hh]
    exact integrableOn_empty
  set IR := ∫ t in (0 : ℝ)..h, psiFloorError t ^ 2 with hIRdef
  have hIR : 0 ≤ IR := intervalIntegral.integral_nonneg hh (fun _ _ => sq_nonneg _)
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) h, weightedPrefix N t ^ 2 ≤
      2 * psiFloorError t ^ 2 + 2 * h / (N : ℝ) ^ 2 * IR := by
    intro t ht
    have he : Real.exp (-t / N) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simpa only [neg_div] using neg_nonpos.mpr (div_nonneg ht.1 hN0.le)
    have he0 := Real.exp_pos (-t / N)
    have he2 : Real.exp (-t / N) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg he0.le (sub_nonneg.mpr he)]
    have hA : (psiFloorError t * Real.exp (-t / N)) ^ 2 ≤ psiFloorError t ^ 2 := by
      rw [mul_pow]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he2 (sq_nonneg (psiFloorError t))
    have hInt := weighted_R_integral_sq N hN ht.1
    have hmono := intervalIntegral.integral_mono_interval (μ := volume)
      (le_refl (0 : ℝ)) ht.1 ht.2
      (Eventually.of_forall fun u : ℝ => sq_nonneg (psiFloorError u)) hR2i
    have hI0 : 0 ≤ ∫ u in (0 : ℝ)..t, psiFloorError u ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 (fun _ _ => sq_nonneg _)
    have hmul : t * (∫ u in (0 : ℝ)..t, psiFloorError u ^ 2) ≤ h * IR :=
      mul_le_mul ht.2 hmono hI0 hh
    have hB : (1 / (N : ℝ) * ∫ u in (0 : ℝ)..t,
        psiFloorError u * Real.exp (-u / N)) ^ 2 ≤ h / (N : ℝ) ^ 2 * IR := by
      rw [mul_pow]
      have hb := mul_le_mul_of_nonneg_left (hInt.trans hmul) (sq_nonneg (1 / (N : ℝ)))
      convert hb using 1 <;> ring
    rw [weighted_prefix_abel N hN ht.1]
    calc (psiFloorError t * Real.exp (-t / N) +
          1 / (N : ℝ) * ∫ u in (0 : ℝ)..t, psiFloorError u * Real.exp (-u / N)) ^ 2
        ≤ 2 * (psiFloorError t * Real.exp (-t / N)) ^ 2 +
          2 * (1 / (N : ℝ) * ∫ u in (0 : ℝ)..t, psiFloorError u * Real.exp (-u / N)) ^ 2 := by
            nlinarith only [sq_nonneg (psiFloorError t * Real.exp (-t / N) -
              (1 / (N : ℝ) * ∫ u in (0 : ℝ)..t, psiFloorError u * Real.exp (-u / N)))]
      _ ≤ 2 * psiFloorError t ^ 2 + 2 * (h / (N : ℝ) ^ 2 * IR) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_left hB (by norm_num))
      _ = _ := by ring
  have hg : IntervalIntegrable
      (fun t : ℝ => 2 * psiFloorError t ^ 2 + 2 * h / (N : ℝ) ^ 2 * IR) volume 0 h :=
    (hR2i.const_mul 2).add intervalIntegrable_const
  have hi : IntervalIntegrable (fun t : ℝ => weightedPrefix N t ^ 2) volume 0 h := by
    refine hg.mono_fun' ((measurable_weightedPrefix N).pow_const 2).aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hh]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt t ⟨ht.1.le, ht.2⟩
  have hm := intervalIntegral.integral_mono_on hh hi hg hpt
  rw [intervalIntegral.integral_add (hR2i.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero] at hm
  have hq : h ^ 2 / (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
    exact pow_le_pow_left₀ hh hhN 2
  have hq' := mul_le_mul_of_nonneg_right hq (show 0 ≤ 2 * IR by positivity)
  have heq : h * (2 * h / (N : ℝ) ^ 2 * IR) = h ^ 2 / (N : ℝ) ^ 2 * (2 * IR) := by ring
  rw [heq] at hm
  have hf := floor_prefix_bound hh
  change IR ≤ 2 * InghamTheta.H h + 2 * h at hf
  change (∫ t in (0 : ℝ)..h, weightedPrefix N t ^ 2) ≤ 2 * IR + _ at hm
  nlinarith

end LeanLab.GoldbachAverage.WeightedPrefixBound82
