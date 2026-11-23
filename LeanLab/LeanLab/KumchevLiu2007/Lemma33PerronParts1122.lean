/-
P0088, Kumchev and Liu 2007, page 10, Lemma 3.3: PROVED helper pieces for the Perron route
to the LEAF `Lemma33Perron1122.lemma33_overlap`, the route of Kumchev 2006 Lemma 2.7.
Pieces: the separation identity for (k/u)^s, the norm of x^(c+it), the existence of a
maximizer on [-T, T], the norm bound for the normalized weights a', b', and the bound
4 log((c+T)/c) for the integral of 1/|c+it| over [-T, T].
Not yet done: the Perron error sum with LeanLab.DERZ1997.Perron136, whose import chain was
not built in this session, and the assembly. The LEAF is unchanged. Standard lemma, not new.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.KumchevLiu2007.Lemma33PerronParts1122

open Complex

/-- Separation identity, PROVED: for k > 0 and m + 1/2, the Perron variable splits. -/
theorem cpow_div_sep (k u : ℝ) (hk : 0 < k) (hu : 0 < u) (s : ℂ) :
    (((k / u : ℝ)) : ℂ) ^ s = (k : ℂ) ^ s * (u : ℂ) ^ (-s) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk.le (inv_nonneg.mpr hu.le)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

/-- Norm of a real positive base to a complex power, PROVED. -/
theorem norm_cpow_pos (x c t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Existence of a maximizer of a continuous function on [-T, T], PROVED. -/
theorem exists_max_on_Icc (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ) (hT : 0 ≤ T) :
    ∃ t0 ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T, g t ≤ g t0 := by
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show -T ≤ T by linarith)) hg.continuousOn
  exact ⟨t0, ht0, fun t ht => hmax ht⟩

/-- Pointwise bound on the Perron integrand denominator, PROVED. -/
theorem inv_norm_le (c t : ℝ) (hc : 0 < c) :
    ‖((c : ℂ) + t * I)‖⁻¹ ≤ c⁻¹ := by
  apply inv_anti₀ hc
  have : ((c : ℂ) + t * I).re = c := by simp
  calc c = |((c : ℂ) + t * I).re| := by rw [this, abs_of_pos hc]
    _ ≤ ‖((c : ℂ) + t * I)‖ := Complex.abs_re_le_norm _

/-- Normalized weights keep the norm bound, PROVED: the weight z (u/M)^(-c) u^(-i t) has
norm ‖z‖ (u/M)^(-c), at most ‖z‖ when u ≥ M and c ≥ 0. -/
theorem norm_weight_le (z : ℂ) (u M c t : ℝ) (hM : 0 < M) (hu : M ≤ u) (hc : 0 ≤ c) :
    ‖z * ((u / M : ℝ) : ℂ) ^ (-(c : ℂ)) * (u : ℂ) ^ (-(t : ℂ) * I)‖ ≤ ‖z‖ := by
  have hu0 : 0 < u := lt_of_lt_of_le hM hu
  have hq : 0 < u / M := div_pos hu0 hM
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hre : ((-(t : ℂ)) * I).re = 0 := by simp
  have hre2 : (-(c : ℂ)).re = -c := by simp
  rw [hre, hre2, Real.rpow_zero, mul_one]
  have h1 : (u / M) ^ (-c) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · rw [le_div_iff₀ hM]; linarith
    · linarith
  calc ‖z‖ * (u / M) ^ (-c) ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖z‖ := mul_one _

/-- Pointwise bound 1/|c+it| ≤ 2/(c+t) for t ≥ 0, PROVED. -/
theorem pt_bound (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    ‖((c : ℂ) + t * I)‖⁻¹ ≤ 2 * (c + t)⁻¹ := by
  have hn : ‖((c : ℂ) + t * I)‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring
  have hpos : 0 < c + t := by linarith
  have h1 : (c + t) / 2 ≤ Real.sqrt (c ^ 2 + t ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (c - t)]
  rw [hn]
  have hs : 0 < Real.sqrt (c ^ 2 + t ^ 2) := by linarith [half_pos hpos]
  rw [show 2 * (c + t)⁻¹ = ((c + t) / 2)⁻¹ by field_simp]
  exact inv_anti₀ (half_pos hpos) h1

/-- The integral of 1/|c+it| over [0, T] is at most 2 log((c+T)/c), PROVED. -/
theorem half_integral_bound (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, ‖((c : ℂ) + t * I)‖⁻¹ ≤ 2 * Real.log ((c + T) / c) := by
  have hcont : Continuous (fun t : ℝ => ‖((c : ℂ) + t * I)‖⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) (fun t => ?_)
    rw [norm_ne_zero_iff]; intro h
    have := congrArg Complex.re h; simp at this; linarith
  have hcont2 : ContinuousOn (fun t : ℝ => 2 * (c + t)⁻¹) (Set.Icc 0 T) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht; linarith [ht.1]
  calc ∫ t in (0:ℝ)..T, ‖((c : ℂ) + t * I)‖⁻¹
      ≤ ∫ t in (0:ℝ)..T, 2 * (c + t)⁻¹ := by
        apply intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable _ _)
        · exact (hcont2.mono (by rw [Set.uIcc_of_le hT])).intervalIntegrable
        · intro t ht; exact pt_bound c t hc ht.1
    _ = 2 * Real.log ((c + T) / c) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := T) c
        rw [show (fun t : ℝ => (c + t)⁻¹) = (fun t => (fun x : ℝ => x⁻¹) (c + t)) from rfl, this]
        rw [add_zero, integral_inv_of_pos hc (by linarith)]

/-- |c - it| = |c + it|, PROVED. -/
theorem norm_neg_t (c t : ℝ) : ‖((c : ℂ) + ((-t : ℝ) : ℂ) * I)‖ = ‖((c : ℂ) + t * I)‖ := by
  rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply]
  congr 1; simp

/-- The integral of 1/|c+it| over [-T, T] is at most 4 log((c+T)/c), PROVED. This is the
O(log(T/c)) factor of the Perron route. -/
theorem full_integral_bound (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖((c : ℂ) + t * I)‖⁻¹ ≤ 4 * Real.log ((c + T) / c) := by
  set f : ℝ → ℝ := fun t => ‖((c : ℂ) + t * I)‖⁻¹ with hf
  have hcont : Continuous f := by
    refine Continuous.inv₀ (by fun_prop) (fun t => ?_)
    rw [norm_ne_zero_iff]; intro h
    have := congrArg Complex.re h; simp at this; linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) (-T) 0) (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
  have hneg : ∫ t in (-T)..0, f t = ∫ t in (0:ℝ)..T, f t := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := T) f
    rw [neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hf]
    rw [norm_neg_t]
  rw [← hsplit, hneg]
  have := half_integral_bound c T hc hT
  linarith

end LeanLab.KumchevLiu2007.Lemma33PerronParts1122

#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.cpow_div_sep
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.norm_cpow_pos
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.exists_max_on_Icc
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.inv_norm_le
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.norm_weight_le
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.pt_bound
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.half_integral_bound
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.norm_neg_t
#print axioms LeanLab.KumchevLiu2007.Lemma33PerronParts1122.full_integral_bound
