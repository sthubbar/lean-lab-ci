import LeanLab.HelfgottMajor.DecompF1602

/-!
Conditional refutation of `SplitGaussian123.exp_branch_tsum_le` of DecompF1602.lean,
burst 20261122.

The sealed leaf has no hypothesis on the cutoff T. At T zero the integrand of
`TailIntegral123.expTailIntegral q 0` carries the term exp of minus 0.1598 t times 1 over 4t,
which is not integrable near zero, so the Lean integral is zero by convention. The left side
is a sum of nonnegative terms that is positive as soon as `L(·, χ)` has one zero in the open
strip with positive imaginary part. So the leaf fails for every character with such a zero.

For q one the character is trivial and `L` is the Riemann zeta function, which has the zero
near 1/2 + 14.1347 i; Mathlib does not yet record any nontrivial zeta zero, so that existence
is kept as the explicit hypothesis `hzero` here. Independently, the audit
notes/burst-20261122/HelfgottMajor-tail_branch_audit.md found the same inequality false for
positive cutoffs too, q one and T 101.3, 103.7 or 150, ratio up to 1.25, falsifier AGREE:
the bare density omits the boundary term that page 38 of P0014 drops after display 4.28.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122ExpBranch
open Real MeasureTheory

/-- A zero of `L(·, χ)` inside the open strip has multiplicity at least one. Copy of the
private lemma `one_le_mult` of DecompF1605.lean. -/
theorem one_le_mult_feed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (h1 : ρ.re < 1) :
    1 ≤ ZeroCount1623.mult χ ρ := by
  have hne1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro s hs
    exact (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hρmem : ρ ∈ ({1}ᶜ : Set ℂ) := by simpa using hne1
  have h2 : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) ≠ ⊤ := by
    have hz : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2)
        (Or.inr (by norm_num)) (by norm_num)
    have hzero : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) = 0 :=
      (han 2 h2mem).analyticOrderAt_eq_zero.mpr hz
    rw [hzero]; exact ENat.zero_ne_top
  have hρtop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected hpc h2mem hρmem h2
  have hρzero : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    have ha := han ρ hρmem
    rw [ha.analyticOrderAt_ne_zero, hρ]
  have hcast : (ZeroCount1623.mult χ ρ : ℕ∞) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ :=
    Nat.cast_analyticOrderNatAt hρtop
  have hge : (1 : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    rcases eq_or_ne (analyticOrderAt (DirichletCharacter.LFunction χ) ρ) 0 with h | h
    · exact absurd h hρzero
    · exact Order.one_le_iff_ne_zero.mpr h
  have : (1 : ℕ∞) ≤ (ZeroCount1623.mult χ ρ : ℕ∞) := by rw [hcast]; exact hge
  exact_mod_cast this

/-- The tail integral from zero vanishes in Lean, because its integrand is not integrable
near zero: the density carries the term 1 over 4t. -/
theorem expTailIntegral_zero (q : ℕ) [NeZero q] :
    TailIntegral123.expTailIntegral q 0 = 0 := by
  unfold TailIntegral123.expTailIntegral
  apply integral_undef
  intro hint
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  -- restrict to (0, 1]
  have hI : IntervalIntegrable
      (fun t : ℝ => exp (-0.1598 * t) * TailIntegral123.countDensity q t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact IntegrableOn.mono_set hint Set.Ioc_subset_Ioi_self
  -- the logarithmic part is integrable
  have hlog : IntervalIntegrable
      (fun t : ℝ => exp (-0.1598 * t) * (1 / (2 * π) * log (q * t / (2 * π))))
        volume 0 1 := by
    have h0 : IntervalIntegrable (fun t : ℝ => log t) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun t : ℝ => log (q * t / (2 * π))) volume 0 1 := by
      have hc : IntervalIntegrable (fun t : ℝ => log (q / (2 * π)) + log t) volume 0 1 :=
        intervalIntegrable_const.add h0
      refine (intervalIntegrable_congr (fun t ht => ?_)).mp hc
      have ht0 : 0 < t := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact ht.1
      have hq2 : (0 : ℝ) < q / (2 * π) := by positivity
      show log (q / (2 * π)) + log t = log (q * t / (2 * π))
      rw [show (q : ℝ) * t / (2 * π) = (q / (2 * π)) * t by ring,
        Real.log_mul hq2.ne' ht0.ne']
    have h2 := h1.const_mul (1 / (2 * π))
    exact h2.continuousOn_mul (by fun_prop)
  have hsub := hI.sub hlog
  have hrecip : IntervalIntegrable (fun t : ℝ => exp (-0.1598 * t) * (1 / (4 * t)))
      volume 0 1 := by
    refine (intervalIntegrable_congr (fun t _ => ?_)).mp hsub
    simp only [TailIntegral123.countDensity]
    ring
  -- compare with the reciprocal, which is not integrable
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 := by
    have hscaled : IntervalIntegrable
        (fun t : ℝ => (4 * exp (0.1598)) * (exp (-0.1598 * t) * (1 / (4 * t)))) volume 0 1 :=
      hrecip.const_mul _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hscaled ⊢
    refine hscaled.mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    have he : exp (0.1598) * exp (-0.1598 * t) ≥ 1 := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have : (4 * exp (0.1598)) * (exp (-0.1598 * t) * (1 / (4 * t)))
        = (exp (0.1598) * exp (-0.1598 * t)) * t⁻¹ := by
      field_simp
    rw [this]
    have hti : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  rw [intervalIntegrable_inv_iff] at hinv
  rcases hinv with h | h
  · norm_num at h
  · exact h (Set.left_mem_uIcc)

/-- Conditional refutation. For any character whose `L` function has a zero in the open
critical strip with positive imaginary part, the sealed statement of `exp_branch_tsum_le`
fails at cutoff zero, where the Lean tail integral is zero and the zero sum is positive. -/
theorem FALSE_feed1122_exp_branch_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im) :
    ¬ ∀ (T : ℝ)
      (_hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im} =>
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im))),
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ T < ρ.im},
          (ZeroCount1623.mult χ ρ.val : ℝ) * Real.exp (-0.1598 * ρ.val.im)) ≤
        TailIntegral123.expTailIntegral q T := by
  intro h
  obtain ⟨ρ, hρ, h0, h1, him⟩ := hzero
  have hs := SplitGaussian123.exp_branch_summable q χ 0
  have hle := h 0 hs
  rw [expTailIntegral_zero] at hle
  let ρ' : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ (0 : ℝ) < ρ.im} := ⟨ρ, hρ, h0, h1, him, him⟩
  have hterm := hs.le_tsum ρ' (fun _ _ => by positivity)
  have hm : (1 : ℝ) ≤ (ZeroCount1623.mult χ ρ : ℝ) := by
    exact_mod_cast one_le_mult_feed χ hρ h1
  have hpos : 0 < (ZeroCount1623.mult χ ρ : ℝ) * Real.exp (-0.1598 * ρ.im) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have : (ZeroCount1623.mult χ ρ'.val : ℝ) * Real.exp (-0.1598 * ρ'.val.im) ≤ 0 :=
    hterm.trans hle
  exact absurd this (not_le.mpr hpos)

end LeanLab.HelfgottMajor.Feed1122ExpBranch

