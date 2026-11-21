import LeanLab.ChirreHagen2025.Decomp608b
import LeanLab.ChirreHagen2025.Decomp608c
import LeanLab.ChirreHagen2025.Decomp608e
import LeanLab.ChirreHagen2025.Decomp358f
import LeanLab.PNTPort.StrongPNT.StrongPNT

/-!
Berndt 1972 pages 152 to 154, positive Laurent coefficients at a equal to one.
The analytic leaves are explicit. The degree-one Bernoulli exception is separate.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp608d
open MeasureTheory Set Decomp272a Decomp608b Decomp608c Decomp608e Polynomial Filter
open scoped Topology

/-- Berndt 1972 page 153, the shifted function f at x minus one when a equals one. -/
noncomputable def berndtKernel (n : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ n / (x * (n.factorial : ℝ))

/-- `B₁` of the fractional part is the fractional part minus one half. -/
private lemma periodicBernoulli_one_eq (x : ℝ) :
    periodicBernoulli 1 x = Int.fract x - 1 / 2 := by
  simp [periodicBernoulli, bernoulliFun_one]

/-- The first derivative polynomial of the Berndt kernel, evaluated. -/
private lemma derivativePoly_one_eval (n : ℕ) (y : ℝ) :
    (derivativePoly n 1).eval y =
      ((n : ℝ) * y ^ (n - 1) - y ^ n) * ((n.factorial : ℝ))⁻¹ := by
  have h0 : derivativePoly n 0 = C ((n.factorial : ℝ))⁻¹ * X ^ n := rfl
  rw [show derivativePoly n 1 =
      (derivativePoly n 0).derivative - C ((0 : ℕ) + 1 : ℝ) * derivativePoly n 0 from rfl, h0]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow,
    derivative_X, mul_one, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The `k`-th derivative polynomial has no constant term below the top index. -/
private lemma derivativePoly_eval_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (derivativePoly n k).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, derivativePoly_coeff, ite_eq_left (Nat.zero_le n), Nat.sub_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, signedFirst,
    Nat.stirlingFirst_eq_zero_of_lt (by omega : k + 1 < n + 1)]
  simp

/-- `{x} = x - j` on the open unit interval. -/
private lemma fract_eq_on_Ioo (j : ℕ) {x : ℝ} (hx : x ∈ Ioo (j : ℝ) ((j : ℝ) + 1)) :
    Int.fract x = x - (j : ℝ) := by
  have hf : ⌊x⌋ = (j : ℤ) := Int.floor_eq_iff.mpr ⟨hx.1.le, by exact_mod_cast hx.2⟩
  change x - (⌊x⌋ : ℝ) = _
  rw [hf]
  norm_cast

/-- The derivative of the `k`-th derivative of the Berndt kernel is the `(k+1)`-st. -/
private lemma hasDerivAt_kernel_deriv (n k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (derivativePoly n k).eval (Real.log y) / y ^ (k + 1))
      ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)) x := by
  have h := Decomp608e.hasDerivAt_eval_log_div_pow (derivativePoly n k) k hx
  rw [show derivativePoly n (k + 1) =
      (derivativePoly n k).derivative - C ((k : ℝ) + 1) * derivativePoly n k from rfl]
  convert h using 2

/-- The `k`-th derivative of the Berndt kernel is continuous on the positive axis. -/
private lemma continuousOn_g (n k : ℕ) :
    ContinuousOn (fun x : ℝ => (derivativePoly n k).eval (Real.log x) / x ^ (k + 1))
      (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    exact ne_of_gt hx
  have h1 : ContinuousOn (fun x : ℝ => (derivativePoly n k).eval (Real.log x)) (Ioi 0) :=
    (derivativePoly n k).continuous.comp_continuousOn hlog
  have h2 : ContinuousOn (fun x : ℝ => x ^ (k + 1)) (Ioi 0) := continuousOn_id.pow (k + 1)
  exact h1.div h2 (fun x hx => pow_ne_zero _ (ne_of_gt hx))

/-- The same derivative tends to zero at infinity. -/
private lemma tendsto_g_atTop (n k : ℕ) :
    Tendsto (fun x : ℝ => (derivativePoly n k).eval (Real.log x) / x ^ (k + 1))
      atTop (nhds 0) := by
  have hd : (derivativePoly n k).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [derivativePoly_coeff, ite_eq_right (by omega)]
  have ht (j : ℕ) : Tendsto (fun x : ℝ => (derivativePoly n k).coeff j *
      (Real.log x ^ j / x ^ (k + 1))) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (j : ℝ)
      (s := ((k + 1 : ℕ) : ℝ)) (by positivity)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, mul_zero] using h.const_mul ((derivativePoly n k).coeff j)
  have hs := tendsto_finsetSum (Finset.range (n + 1)) (fun j _ => ht j)
  simp only [Finset.sum_const_zero] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Bernoulli polynomials at the two endpoints of the unit interval agree above degree one. -/
private lemma bernoulliFun_succ_zero_one (k : ℕ) (hk : 1 ≤ k) :
    bernoulliFun (k + 1) 1 = bernoulliFun (k + 1) 0 := by
  rw [bernoulliFun_eval_one]
  rw [ite_eq_right (by omega : ¬ (k + 1 = 1))]
  ring

/-- The shifted Bernoulli polynomial is a primitive of the normed one. -/
private lemma hasDerivAt_shifted_bernoulli (k j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => bernoulliFun (k + 1) (y - (j : ℝ)) / ((k + 1).factorial : ℝ))
      (bernoulliFun k (x - (j : ℝ)) / (k.factorial : ℝ)) x := by
  have hder : HasDerivAt (fun y : ℝ => y - (j : ℝ)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const ((j : ℝ))
  have h := ((hasDerivAt_bernoulliFun (k + 1) (x - (j : ℝ))).comp x hder).div_const
    (((k + 1).factorial : ℝ))
  have hval : (↑(k + 1) * bernoulliFun (k + 1 - 1) (x - ↑j) * 1 / ↑(k + 1).factorial)
      = bernoulliFun k (x - ↑j) / ↑k.factorial := by
    rw [show k + 1 - 1 = k from rfl, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hval] at h
  simpa only [Function.comp_apply] using h

/-- One interval of the integration-by-parts chain for Berndt display 3.1. -/
private lemma interval_ibp (n k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (∫ x in (j : ℝ)..((j : ℝ) + 1), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)))
      + (∫ x in (j : ℝ)..((j : ℝ) + 1), periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      = (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ)) *
        (((derivativePoly n k).eval (Real.log ((j : ℝ) + 1)) / ((j : ℝ) + 1) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log (j : ℝ)) / (j : ℝ) ^ (k + 1))) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjlt : (j : ℝ) < (j : ℝ) + 1 := by linarith
  have hsub : ∀ x ∈ uIoo (j : ℝ) ((j : ℝ) + 1), Int.fract x = x - (j : ℝ) := by
    intro x hx
    rw [uIoo_of_lt hjlt] at hx
    exact fract_eq_on_Ioo j hx
  have hmono : ∀ x ∈ uIcc (j : ℝ) ((j : ℝ) + 1), (0 : ℝ) < x := by
    intro x hx
    rw [uIcc_of_le hjlt.le] at hx
    linarith [hx.1]
  have hcu : ContinuousOn (fun x : ℝ => (derivativePoly n k).eval (Real.log x) / x ^ (k + 1))
      (uIcc (j : ℝ) ((j : ℝ) + 1)) :=
    (continuousOn_g n k).mono (fun x hx => hmono x hx)
  have hcu' : ContinuousOn (fun x : ℝ => (derivativePoly n (k + 1)).eval (Real.log x) /
      x ^ (k + 2)) (uIcc (j : ℝ) ((j : ℝ) + 1)) :=
    (continuousOn_g n (k + 1)).mono (fun x hx => hmono x hx)
  have hcv : ContinuousOn (fun x : ℝ => bernoulliFun (k + 1) (x - (j : ℝ)) /
      ((k + 1).factorial : ℝ)) (uIcc (j : ℝ) ((j : ℝ) + 1)) :=
    (((continuous_bernoulliFun (k + 1)).comp
      (continuous_id.sub continuous_const)).div_const _).continuousOn
  have hv' : ContinuousOn (fun x : ℝ => bernoulliFun k (x - (j : ℝ)) / (k.factorial : ℝ))
      (uIcc (j : ℝ) ((j : ℝ) + 1)) :=
    (((continuous_bernoulliFun k).comp
      (continuous_id.sub continuous_const)).div_const _).continuousOn
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (j : ℝ)) (b := (j : ℝ) + 1)
    (u := fun x : ℝ => (derivativePoly n k).eval (Real.log x) / x ^ (k + 1))
    (v := fun x : ℝ => bernoulliFun (k + 1) (x - (j : ℝ)) / ((k + 1).factorial : ℝ))
    (u' := fun x : ℝ => (derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2))
    (v' := fun x : ℝ => bernoulliFun k (x - (j : ℝ)) / (k.factorial : ℝ))
    hcu hcv
    (by
      intro x hx
      simp only [min_eq_left hjlt.le, max_eq_right hjlt.le] at hx
      exact hasDerivAt_kernel_deriv n k (by linarith [hx.1]))
    (by intro x hx; exact hasDerivAt_shifted_bernoulli k j x)
    (hcu'.intervalIntegrable) (hv'.intervalIntegrable)
  -- rewrite both integrals in periodic form
  have e1 : (∫ x in (j : ℝ)..((j : ℝ) + 1), (fun x : ℝ =>
        (derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) x *
        (fun x : ℝ => bernoulliFun k (x - (j : ℝ)) / (k.factorial : ℝ)) x)
      = ∫ x in (j : ℝ)..((j : ℝ) + 1), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    simp only [periodicBernoulli, hsub x hx]
    ring
  have e2 : (∫ x in (j : ℝ)..((j : ℝ) + 1), (fun x : ℝ =>
        (derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)) x *
        (fun x : ℝ => bernoulliFun (k + 1) (x - (j : ℝ)) / ((k + 1).factorial : ℝ)) x)
      = ∫ x in (j : ℝ)..((j : ℝ) + 1), periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    simp only [periodicBernoulli, hsub x hx]
    ring
  rw [← e1, ← e2, hIBP]
  have hb1 : bernoulliFun (k + 1) ((j : ℝ) + 1 - (j : ℝ)) = bernoulliFun (k + 1) 0 := by
    rw [show (j : ℝ) + 1 - (j : ℝ) = 1 by ring, bernoulliFun_succ_zero_one k hk]
  have hb0 : bernoulliFun (k + 1) ((j : ℝ) - (j : ℝ)) = bernoulliFun (k + 1) 0 := by
    rw [sub_self]
  simp only [hb1, hb0]
  ring

/-- The `k`-th derivative of the Berndt kernel is integrable past one. -/
private lemma integrableOn_g (n k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (fun x : ℝ => (derivativePoly n k).eval (Real.log x) / x ^ (k + 1))
      (Ioi (1 : ℝ)) := by
  have hd : (derivativePoly n k).natDegree ≤ n := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [derivativePoly_coeff, ite_eq_right (by omega)]
  have hs : IntegrableOn (fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      (derivativePoly n k).coeff j * (Real.log x ^ j / x ^ (k + 1))) (Ioi (1 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => (Decomp608b.log_moment_integrable k j hk).const_mul _)
  refine hs.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The periodic Bernoulli weight times a kernel derivative is integrable. -/
private lemma integrableOn_periodic_mul_g (n k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (fun x : ℝ => periodicBernoulli k x *
      ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1))) (Ioi (1 : ℝ)) := by
  have hg := integrableOn_g n k hk
  have hm : Measurable (periodicBernoulli k) := by
    unfold periodicBernoulli bernoulliFun
    fun_prop
  refine hg.bdd_mul (c := 4 / (2 * Real.pi) ^ k) hm.aestronglyMeasurable ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using
    Decomp608c.periodicBernoulli_uniform_bound k hk x

/-- The finite telescoped form of the integration-by-parts chain. -/
private lemma finite_ibp (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) (N : ℕ) (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      = (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ)) *
        (((derivativePoly n k).eval (Real.log (N : ℝ)) / (N : ℝ) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1))) := by
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hint1 : ∀ j : ℕ, IntervalIntegrable (fun x : ℝ => periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)))
      volume ((j : ℝ) + 1) ((j : ℝ) + 1 + 1) := by
    intro j
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1)]
    refine (integrableOn_periodic_mul_g n k hk).mono_set ?_
    intro x hx
    simp only [mem_Ioc] at hx
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact show x ∈ Ioi (1 : ℝ) from by
      rw [mem_Ioi]
      linarith [hx.1, hj]
  have hint2 : ∀ j : ℕ, IntervalIntegrable (fun x : ℝ => periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      volume ((j : ℝ) + 1) ((j : ℝ) + 1 + 1) := by
    intro j
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1)]
    refine (integrableOn_periodic_mul_g n (k + 1) (by omega)).mono_set ?_
    intro x hx
    simp only [mem_Ioc] at hx
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact show x ∈ Ioi (1 : ℝ) from by
      rw [mem_Ioi]
      linarith [hx.1, hj]
  have hint : ∀ j : ℕ, IntervalIntegrable (fun x : ℝ => periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      volume ((j : ℝ) + 1) ((j : ℝ) + 1 + 1) :=
    fun j => (hint1 j).add (hint2 j)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) + 1) (f := fun x : ℝ => periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
    (n := N - 1) (fun j _ => by
      have h := hint j
      simpa only [Nat.cast_add, Nat.cast_one] using h)
  have hlast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    have h1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have hcast : (((N - 1) + 1 : ℕ) : ℝ) = (N : ℝ) := by
        rw [Nat.sub_add_cancel hN]
      push_cast at hcast
      linarith
    linarith
  have hterm : ∀ j ∈ Finset.range (N - 1),
      (∫ x in ((j : ℝ) + 1)..(((j + 1 : ℕ) : ℝ) + 1), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      = (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ)) *
        (((derivativePoly n k).eval (Real.log (((j + 1 : ℕ) : ℝ) + 1)) /
            (((j + 1 : ℕ) : ℝ) + 1) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log ((j + 1 : ℕ) : ℝ)) /
            ((j + 1 : ℕ) : ℝ) ^ (k + 1))) := by
    intro j _
    have hibp := interval_ibp n k (j + 1) hk (by omega)
    rw [intervalIntegral.integral_add
      (by simpa only [Nat.cast_add, Nat.cast_one] using hint1 j)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hint2 j)]
    push_cast at hibp ⊢
    exact hibp
  have htel : ∑ j ∈ Finset.range (N - 1),
      (((derivativePoly n k).eval (Real.log (((j + 1 : ℕ) : ℝ) + 1)) /
          (((j + 1 : ℕ) : ℝ) + 1) ^ (k + 1))
        - ((derivativePoly n k).eval (Real.log ((j + 1 : ℕ) : ℝ)) /
          ((j + 1 : ℕ) : ℝ) ^ (k + 1)))
      = ((derivativePoly n k).eval (Real.log (N : ℝ)) / (N : ℝ) ^ (k + 1))
        - ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1)) := by
    set f : ℕ → ℝ := fun i => (derivativePoly n k).eval (Real.log ((i : ℝ) + 1)) /
      ((i : ℝ) + 1) ^ (k + 1) with hf
    have hL : ∑ j ∈ Finset.range (N - 1),
        (((derivativePoly n k).eval (Real.log (((j + 1 : ℕ) : ℝ) + 1)) /
            (((j + 1 : ℕ) : ℝ) + 1) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log ((j + 1 : ℕ) : ℝ)) /
            ((j + 1 : ℕ) : ℝ) ^ (k + 1)))
        = ∑ j ∈ Finset.range (N - 1), (f (j + 1) - f j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hf]
      push_cast
      ring
    rw [hL, Finset.sum_range_sub, hf, ← hlast]
    norm_num
  rw [show (1 : ℝ) = ((0 : ℕ) : ℝ) + 1 by norm_num,
    show (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 from hlast.symm, ← hsum,
    Finset.sum_congr rfl hterm, ← Finset.mul_sum, htel, hlast]
  norm_num

/-- One step of the integration-by-parts chain in the improper limit. -/
private lemma ibp_step (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (∫ x in Ioi (1 : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)))
      + (∫ x in Ioi (1 : ℝ), periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2))) = 0 := by
  have hfint : IntegrableOn (fun x : ℝ => periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2))) (Ioi (1 : ℝ)) :=
    (integrableOn_periodic_mul_g n k hk).add (integrableOn_periodic_mul_g n (k + 1) (by omega))
  have hlim : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))
      atTop (nhds (∫ x in Ioi (1 : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2)))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hfint tendsto_natCast_atTop_atTop
  have hgk0 : (derivativePoly n k).eval (0 : ℝ) = 0 := derivativePoly_eval_zero n k hk hkn
  have hgk1 : (derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1) = 0 := by
    simp [hgk0]
  have htarget : Tendsto (fun N : ℕ =>
      (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ)) *
        (((derivativePoly n k).eval (Real.log (N : ℝ)) / (N : ℝ) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1)))) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => (derivativePoly n k).eval (Real.log (N : ℝ)) /
        (N : ℝ) ^ (k + 1)) atTop (nhds 0) :=
      (tendsto_g_atTop n k).comp tendsto_natCast_atTop_atTop
    have hconst : Tendsto (fun _ : ℕ => (derivativePoly n k).eval (Real.log 1) /
        (1 : ℝ) ^ (k + 1)) atTop
        (nhds ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1))) :=
      tendsto_const_nhds
    have h2 : Tendsto (fun N : ℕ => ((derivativePoly n k).eval (Real.log (N : ℝ)) /
        (N : ℝ) ^ (k + 1)) - ((derivativePoly n k).eval (Real.log 1) /
        (1 : ℝ) ^ (k + 1))) atTop
        (nhds ((0 : ℝ) - ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1)))) :=
      h1.sub hconst
    have h3 := h2.const_mul (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ))
    simpa [hgk0] using h3
  have hcongr : (fun N : ℕ => ∫ x in (1 : ℝ)..(N : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2))) =ᶠ[atTop]
      (fun N : ℕ => (bernoulliFun (k + 1) 0 / ((k + 1).factorial : ℝ)) *
        (((derivativePoly n k).eval (Real.log (N : ℝ)) / (N : ℝ) ^ (k + 1))
          - ((derivativePoly n k).eval (Real.log 1) / (1 : ℝ) ^ (k + 1)))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact finite_ibp n k hk hkn N hN
  have hzero : (∫ x in Ioi (1 : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)) +
        periodicBernoulli (k + 1) x *
        ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 2))) = 0 :=
    tendsto_nhds_unique (hlim.congr' hcongr) htarget
  rw [integral_add (integrableOn_periodic_mul_g n k hk)
    (integrableOn_periodic_mul_g n (k + 1) (by omega))] at hzero
  exact hzero

/-- Berndt display 3.1, the integration-by-parts chain down to degree one. -/
private lemma ibp_chain (n : ℕ) : ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (∫ x in Ioi (1 : ℝ), periodicBernoulli k x *
        ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1)))
      = (-1 : ℝ) ^ (k - 1) * (∫ x in Ioi (1 : ℝ), periodicBernoulli 1 x *
        ((derivativePoly n 1).eval (Real.log x) / x ^ 2)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
      intro hk hkn
      rcases Nat.lt_or_ge 1 (k + 1) with h1 | h1
      · have hk1 : 1 ≤ k := by omega
        have hstep := ibp_step n k hk1 (by omega)
        have hih := ih hk1 (by omega)
        have hnegsign : (∫ x in Ioi (1 : ℝ), periodicBernoulli (k + 1) x *
            ((derivativePoly n (k + 1)).eval (Real.log x) / x ^ (k + 1 + 1)))
            = -(∫ x in Ioi (1 : ℝ), periodicBernoulli k x *
              ((derivativePoly n k).eval (Real.log x) / x ^ (k + 1))) := by
          rw [show k + 1 + 1 = (k + 1) + 1 by omega]
          linarith [hstep]
        rw [hnegsign, hih]
        have hsign : (-1 : ℝ) ^ ((k + 1) - 1) = -(-1) ^ (k - 1) := by
          have hk' : (k + 1) - 1 = (k - 1) + 1 := by omega
          rw [hk', pow_succ]
          ring
        rw [hsign]
        ring
      · have hk1 : k + 1 = 1 := by omega
        rw [hk1]
        norm_num


/-- The logarithmic power is integrable against `u ^ (-3/2)` past one. -/
private lemma log_pow_mul_rpow_integrable (k : ℕ) :
    IntegrableOn (fun u : ℝ => Real.log u ^ k * u ^ (-(3 : ℝ) / 2)) (Ioi (1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using integrableOn_Ioi_rpow_of_lt (a := (-(3 : ℝ) / 2)) (by norm_num) one_pos
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (-(5 : ℝ) / 4)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (a := (-(5 : ℝ) / 4)) (by norm_num) one_pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine (hrpow.const_mul ((4 * (k : ℝ)) ^ k)).mono' ?_ ?_
  · have : Measurable (fun u : ℝ => Real.log u ^ k * u ^ (-(3 : ℝ) / 2)) := by fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hl : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hlog : Real.log u ≤ (4 * (k : ℝ)) * u ^ ((4 * (k : ℝ))⁻¹) := by
      have h := Real.log_le_rpow_div (x := u) hu0.le
        (show (0 : ℝ) < (4 * (k : ℝ))⁻¹ by positivity)
      rw [div_eq_mul_inv, inv_inv] at h
      calc Real.log u ≤ u ^ ((4 * (k : ℝ))⁻¹) * (4 * (k : ℝ)) := h
        _ = (4 * (k : ℝ)) * u ^ ((4 * (k : ℝ))⁻¹) := by ring
    have hpow : Real.log u ^ k ≤ ((4 * (k : ℝ)) ^ k) * u ^ ((1 : ℝ) / 4) := by
      have h1 := pow_le_pow_left₀ hl hlog k
      calc Real.log u ^ k ≤ ((4 * (k : ℝ)) * u ^ ((4 * (k : ℝ))⁻¹)) ^ k := h1
        _ = (4 * (k : ℝ)) ^ k * (u ^ ((4 * (k : ℝ))⁻¹)) ^ k := by rw [mul_pow]
        _ = (4 * (k : ℝ)) ^ k * u ^ ((1 : ℝ) / 4) := by
            have h4 : u ^ ((1 : ℝ) / 4) = (u ^ ((4 * (k : ℝ))⁻¹)) ^ ((k : ℝ)) := by
              rw [← Real.rpow_mul hu0.le]
              congr 1
              field_simp
            rw [h4, Real.rpow_natCast]
    have hstep : Real.log u ^ k * u ^ (-(3 : ℝ) / 2) ≤
        ((4 * (k : ℝ)) ^ k * u ^ ((1 : ℝ) / 4)) * u ^ (-(3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hu0.le _)
    have hcombine : ((4 * (k : ℝ)) ^ k * u ^ ((1 : ℝ) / 4)) * u ^ (-(3 : ℝ) / 2) =
        (4 * (k : ℝ)) ^ k * u ^ (-(5 : ℝ) / 4) := by
      rw [mul_assoc, ← Real.rpow_add hu0]
      norm_num
    have hnn : (0 : ℝ) ≤ Real.log u ^ k * u ^ (-(3 : ℝ) / 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [hcombine] at hstep
    exact hstep

/-- Derivative of the analytic kernel in the exponent. -/
private lemma hasDerivAt_cpow_exponent (u : ℝ) (hu : 1 ≤ u) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-2 - w))
      ((u : ℂ) ^ (-2 - z) * Complex.log (u : ℂ) * (-1)) z := by
  have hu0 : (u : ℂ) ≠ 0 := by
    have : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
    exact_mod_cast (ne_of_gt this)
  have hlin : HasDerivAt (fun w : ℂ => -2 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (-2 : ℂ)
  exact hlin.const_cpow (Or.inl hu0)

/-- The basic domination for the analytic kernel: `|log u| ^ k * u ^ (-3/2)`. -/
private lemma norm_cpow_le (u : ℝ) (hu : 1 ≤ u) (w : ℂ) (hw : -(1 : ℝ) / 2 ≤ w.re) (k : ℕ) :
    ‖(periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w)‖ ≤
      (1 / 2) * (Real.log u) ^ k * u ^ (-(3 : ℝ) / 2) := by
  have hu1 : (1 : ℝ) ≤ u := hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hl : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
  have hP : ‖(periodicBernoulli 1 u : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact periodicBernoulli_one_bound u
  have hlogn : ‖(-(Real.log u : ℂ)) ^ k‖ = (Real.log u) ^ k := by
    rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hcp : ‖(u : ℂ) ^ (-2 - w)‖ = u ^ ((-2 - w).re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have hexp : (-2 - w).re ≤ -(3 : ℝ) / 2 := by
    have h : (-2 - w).re = -2 - w.re := by simp
    rw [h]
    linarith
  have hle : u ^ ((-2 - w).re) ≤ u ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hu1 hexp
  calc ‖(periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w)‖
      = ‖(periodicBernoulli 1 u : ℂ)‖ * ‖(-(Real.log u : ℂ)) ^ k‖ * ‖(u : ℂ) ^ (-2 - w)‖ := by
        rw [norm_mul, norm_mul]
    _ = ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k * u ^ ((-2 - w).re) := by rw [hlogn, hcp]
    _ ≤ (1 / 2) * (Real.log u) ^ k * u ^ (-(3 : ℝ) / 2) := by
        have hk : (0 : ℝ) ≤ (Real.log u) ^ k := by positivity
        have hrp : (0 : ℝ) < u ^ ((-2 - w).re) := Real.rpow_pos_of_pos hu0 _
        calc ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k * u ^ ((-2 - w).re)
            ≤ (1 / 2) * (Real.log u) ^ k * u ^ ((-2 - w).re) := by
              apply mul_le_mul_of_nonneg_right _ hrp.le
              exact mul_le_mul_of_nonneg_right hP hk
          _ ≤ (1 / 2) * (Real.log u) ^ k * u ^ (-(3 : ℝ) / 2) := by
              apply mul_le_mul_of_nonneg_left hle
              positivity

/-- The integrand at the exponent `z` is integrable. -/
private lemma integrable_weight (k : ℕ) (z : ℂ) (hz : -(1 : ℝ) / 2 ≤ z.re) :
    Integrable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
      (u : ℂ) ^ (-2 - z)) (volume.restrict (Ioi (1 : ℝ))) := by
  have hdom : Integrable (fun u : ℝ => (1 / 2) * (Real.log u) ^ k *
      u ^ (-(3 : ℝ) / 2)) (volume.restrict (Ioi (1 : ℝ))) := by
    have h := (log_pow_mul_rpow_integrable k).const_mul (1 / 2)
    simpa only [mul_assoc] using h
  refine hdom.mono' ?_ ?_
  · have hmeas : Measurable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - z)) := by
      unfold periodicBernoulli bernoulliFun
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_cpow_le u hu.le z hz k

/-- The norm of the differentiated integrand, exactly. -/
private lemma norm_weight_deriv (u : ℝ) (hu : 1 ≤ u) (w : ℂ) (k : ℕ) :
    ‖(periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
      ((u : ℂ) ^ (-2 - w) * Complex.log (u : ℂ) * (-1))‖ =
    ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k *
      (u ^ ((-2 - w).re) * Real.log u) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hl : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu
  have hlogc : Complex.log (u : ℂ) = (Real.log u : ℂ) := by
    rw [← Complex.ofReal_log hu0.le]
  have hlogn : ‖(-(Real.log u : ℂ)) ^ k‖ = (Real.log u) ^ k := by
    rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hcp : ‖(u : ℂ) ^ (-2 - w)‖ = u ^ ((-2 - w).re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  simp only [norm_mul, norm_neg, norm_one, hlogc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hl, hlogn, hcp, mul_one]

/-- The parametric derivative of the analytic weight. -/
private lemma hasDerivAt_weight (k : ℕ) (z : ℂ) (hz : -(1 : ℝ) / 2 < z.re) :
    HasDerivAt (fun w : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w))
      (∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ (k + 1) * (u : ℂ) ^ (-2 - z)) z := by
  have hmem : {w : ℂ | -(1 : ℝ) / 2 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) *
      (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w)) (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards with w
    have hmeas : Measurable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w)) := by
      unfold periodicBernoulli bernoulliFun
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) *
      (-(Real.log u : ℂ)) ^ k * ((u : ℂ) ^ (-2 - z) * Complex.log (u : ℂ) * (-1)))
      (volume.restrict (Ioi (1 : ℝ))) := by
    have hmeas : Measurable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ k * ((u : ℂ) ^ (-2 - z) * Complex.log (u : ℂ) * (-1))) := by
      unfold periodicBernoulli bernoulliFun
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ w ∈ {w : ℂ | -(1 : ℝ) / 2 < w.re},
      ‖(periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
        ((u : ℂ) ^ (-2 - w) * Complex.log (u : ℂ) * (-1))‖ ≤
      (1 / 2) * (Real.log u) ^ (k + 1) * u ^ (-(3 : ℝ) / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
    have hl : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hP : ‖(periodicBernoulli 1 u : ℂ)‖ ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact periodicBernoulli_one_bound u
    rw [norm_weight_deriv u hu1 w k]
    have hexp : (-2 - w).re ≤ -(3 : ℝ) / 2 := by
      have h : (-2 - w).re = -2 - w.re := by simp
      rw [h]; linarith [hw]
    have hle : u ^ ((-2 - w).re) ≤ u ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hu1 hexp
    have hstep : u ^ ((-2 - w).re) * Real.log u ≤ u ^ (-(3 : ℝ) / 2) * Real.log u :=
      mul_le_mul_of_nonneg_right hle hl
    have hk : (0 : ℝ) ≤ (Real.log u) ^ k := by positivity
    have hmid : ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k ≤ (1 / 2) * (Real.log u) ^ k :=
      mul_le_mul_of_nonneg_right hP hk
    have hnn1 : (0 : ℝ) ≤ ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k := by positivity
    calc ‖(periodicBernoulli 1 u : ℂ)‖ * (Real.log u) ^ k *
          (u ^ ((-2 - w).re) * Real.log u)
        ≤ ((1 / 2) * (Real.log u) ^ k) * (u ^ (-(3 : ℝ) / 2) * Real.log u) := by
          apply mul_le_mul hmid hstep
          · positivity
          · positivity
      _ = (1 / 2) * (Real.log u) ^ (k + 1) * u ^ (-(3 : ℝ) / 2) := by
          rw [pow_succ]; ring
  have hbound_int : Integrable (fun u : ℝ => (1 / 2) * (Real.log u) ^ (k + 1) *
      u ^ (-(3 : ℝ) / 2)) (volume.restrict (Ioi (1 : ℝ))) := by
    have h := (log_pow_mul_rpow_integrable (k + 1)).const_mul (1 / 2)
    simpa only [mul_assoc] using h
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ w ∈ {w : ℂ | -(1 : ℝ) / 2 < w.re},
      HasDerivAt (fun w : ℂ => (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
        (u : ℂ) ^ (-2 - w))
        ((periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
          ((u : ℂ) ^ (-2 - w) * Complex.log (u : ℂ) * (-1))) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w _
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hbase := hasDerivAt_cpow_exponent u hu1 w
    have hconst : HasDerivAt (fun _ : ℂ => (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ k) 0 w := hasDerivAt_const w _
    have h := hconst.mul hbase
    convert h using 1
    ring
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ))) (x₀ := z)
    (F := fun w : ℂ => fun u : ℝ => (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
      (u : ℂ) ^ (-2 - w))
    (F' := fun w : ℂ => fun u : ℝ => (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
      ((u : ℂ) ^ (-2 - w) * Complex.log (u : ℂ) * (-1)))
    (bound := fun u : ℝ => (1 / 2) * (Real.log u) ^ (k + 1) * u ^ (-(3 : ℝ) / 2))
    hmem hF_meas (integrable_weight k z hz.le) hF'_meas hbound hbound_int hdiff
  have hval : (∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k *
      ((u : ℂ) ^ (-2 - z) * Complex.log (u : ℂ) * (-1)))
      = ∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ (k + 1) * (u : ℂ) ^ (-2 - z) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one (le_of_lt hu)
    rw [← Complex.ofReal_log hu0.le, pow_succ]
    ring
  rw [hval] at hderiv
  exact hderiv

/-- The `k`-th derivative of the analytic weight. -/
private lemma iteratedDeriv_weight (k : ℕ) (z : ℂ) (hz : -(1 : ℝ) / 2 < z.re) :
    iteratedDeriv k (fun w : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - w)) z
      = ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hopen : {w : ℂ | -(1 : ℝ) / 2 < w.re} ∈ 𝓝 z :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
      have heq : iteratedDeriv k (fun w : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - w)) =ᶠ[𝓝 z]
          (fun w => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (-(Real.log u : ℂ)) ^ k * (u : ℂ) ^ (-2 - w)) := by
        filter_upwards [hopen] with w hw
        exact ih w hw
      rw [heq.deriv_eq]
      exact (hasDerivAt_weight k z hz).deriv

/-- Integrability of the bare analytic kernel. -/
private lemma integrable_cpow_neg (z : ℂ) (hz : -(1 : ℝ) < z.re) :
    Integrable (fun u : ℝ => (u : ℂ) ^ (-2 - z)) (volume.restrict (Ioi (1 : ℝ))) := by
  have ha : (-2 - z : ℂ).re < -1 := by
    have h : (-2 - z).re = -2 - z.re := by simp
    rw [h]; linarith
  exact integrableOn_Ioi_cpow_of_lt ha one_pos

/-- The Laurent regular part in terms of the analytic weight. -/
private lemma regularPart_eq_weight (z : ℂ) (hz : -(1 : ℝ) / 2 < z.re) (hz0 : z ≠ 0) :
    regularPart z = 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
      (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z) := by
  have hs : (0 : ℂ).re < (1 + z).re := by
    have h : (1 + z : ℂ).re = 1 + z.re := by simp
    have h0 : (0 : ℂ).re = 0 := rfl
    rw [h, h0]; linarith
  have hs1 : (1 + z : ℂ) ≠ 1 := by
    intro h
    exact hz0 (by linear_combination h)
  have hζ := ZetaAltFormula (s := 1 + z) hs hs1
  have hexp : -(1 + z) - 1 = -2 - z := by ring
  have hzeta : riemannZeta (1 + z) = 1 + 1 / z - (1 + z) *
      ∫ u : ℝ in Ioi (1 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-2 - z) := by
    rw [hζ]
    unfold riemannZeta1
    rw [show (1 + z : ℂ) - 1 = z by ring, hexp]
  have hreg : regularPart z = riemannZeta₀ (1 + z) := Decomp358e.regularPart_eq z
  have hz1 : (1 + z : ℂ) ≠ 1 := hs1
  have h0 : riemannZeta₀ (1 + z) = riemannZeta (1 + z) - 1 / z := by
    rw [riemannZeta₀, if_neg hz1]
    congr 1
    ring
  have hfract : ∀ u : ℝ, ((Int.fract u : ℝ) : ℂ) = (periodicBernoulli 1 u : ℂ) + 1 / 2 := by
    intro u
    rw [show periodicBernoulli 1 u = Int.fract u - 1 / 2 by
      simp [periodicBernoulli, bernoulliFun_one]]
    push_cast
    ring
  have hz2 : -(1 : ℝ) / 2 ≤ z.re := by linarith
  have hint1 : Integrable (fun u : ℝ => (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z))
      (volume.restrict (Ioi (1 : ℝ))) := by
    have h := integrable_weight 0 z hz2
    simpa only [pow_zero, mul_one] using h
  have hz1' : -(1 : ℝ) < z.re := by linarith
  have hint2 : Integrable (fun u : ℝ => (u : ℂ) ^ (-2 - z))
      (volume.restrict (Ioi (1 : ℝ))) := integrable_cpow_neg z hz1'
  have hsplit : (∫ u : ℝ in Ioi (1 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-2 - z))
      = (∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z))
        + (1 / 2) * ∫ u : ℝ in Ioi (1 : ℝ), (u : ℂ) ^ (-2 - z) := by
    have h1 : (∫ u : ℝ in Ioi (1 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-2 - z))
        = ∫ u : ℝ in Ioi (1 : ℝ), ((periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)
          + (1 / 2) * (u : ℂ) ^ (-2 - z)) := by
      congr 1
      ext u
      rw [hfract u]
      ring
    rw [h1, integral_add hint1 (hint2.const_mul (1 / 2)), integral_const_mul]
  have hcval : (∫ u : ℝ in Ioi (1 : ℝ), (u : ℂ) ^ (-2 - z)) = 1 / (1 + z) := by
    have ha : (-2 - z : ℂ).re < -1 := by
      have h : (-2 - z).re = -2 - z.re := by simp
      rw [h]; linarith
    rw [integral_Ioi_cpow_of_lt ha one_pos]
    have h1 : (-2 - z : ℂ) + 1 = -(1 + z) := by ring
    rw [h1]
    have hne : (1 + z : ℂ) ≠ 0 := by
      intro h
      have hre : z.re = -1 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      linarith
    simp only [Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq, one_div]
  have hne : (1 + z : ℂ) ≠ 0 := by
    intro h
    have hre : z.re = -1 := by
      have := congrArg Complex.re h
      simp at this
      linarith
    linarith
  have hstep : (1 + z) * (1 / 2 * (1 / (1 + z))) = 1 / 2 := by
    field_simp
  rw [hreg, h0, hzeta, hsplit, hcval, mul_add, hstep]
  ring

/-- The weight is continuous at the origin. -/
private lemma continuousAt_weight_zero :
    ContinuousAt (fun w : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
      (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - w)) 0 := by
  have h := (hasDerivAt_weight 0 0 (by norm_num)).continuousAt
  simpa only [pow_zero, mul_one] using h

/-- The regular part equals the weight expression near the origin. -/
private lemma regularPart_eventuallyEq :
    (fun z : ℂ => regularPart z) =ᶠ[𝓝 0]
      (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) := by
  have hopen : {z : ℂ | -(1 : ℝ) / 2 < z.re} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hmem : ∀ᶠ z : ℂ in 𝓝[≠] 0, -(1 : ℝ) / 2 < z.re := nhdsWithin_le_nhds hopen
  have hpt : ∀ᶠ z : ℂ in 𝓝[≠] 0, regularPart z = 1 / 2 - (1 + z) *
      ∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z) := by
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hz0
    exact regularPart_eq_weight z hz hz0
  have hcont1 : ContinuousAt regularPart 0 :=
    Decomp358e.regularPart_entire.continuous.continuousAt
  have hcont2 : ContinuousAt (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
      (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) 0 := by
    refine ContinuousAt.sub continuousAt_const ?_
    refine ContinuousAt.mul ?_ continuousAt_weight_zero
    exact continuousAt_const.add continuousAt_id
  have h1 : Tendsto regularPart (𝓝[≠] 0) (𝓝 (regularPart 0)) :=
    hcont1.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
      (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) (𝓝[≠] 0)
      (𝓝 (1 / 2 - (1 + (0:ℂ)) * ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - (0:ℂ)))) :=
    hcont2.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : regularPart 0 = 1 / 2 - (1 + (0:ℂ)) * ∫ u : ℝ in Ioi (1 : ℝ),
      (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - (0:ℂ)) :=
    tendsto_nhds_unique (h1.congr' hpt) h2
  filter_upwards [hopen] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    exact h0
  · exact regularPart_eq_weight z hz hz0

/-- Leibniz for the linear factor times the weight, one step up. -/
private lemma iteratedDeriv_regularPart_expression (k : ℕ) (w : ℂ) (hw : -(1 : ℝ) / 2 < w.re) :
    iteratedDeriv (k + 1) (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w
      = -((1 + w) * iteratedDeriv (k + 1) (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w)
        - ((k : ℂ) + 1) * iteratedDeriv k (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w := by
  induction k generalizing w with
  | zero =>
      rw [Nat.zero_add, iteratedDeriv_one]
      have hI : HasDerivAt (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
          (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z))
          (iteratedDeriv 1 (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w) w := by
        have h := hasDerivAt_weight 0 w hw
        simp only [pow_zero, mul_one] at h
        refine h.congr_deriv ?_
        rw [iteratedDeriv_weight 1 w hw]
      have hlin : HasDerivAt (fun z : ℂ => 1 + z) 1 w := by
        simpa using (hasDerivAt_id w).const_add (1 : ℂ)
      have hH : HasDerivAt (fun z : ℂ => 1 / 2 - (1 + z) * (∫ u : ℝ in Ioi (1 : ℝ),
          (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)))
          (-(1 * (∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - w))
            + (1 + w) * iteratedDeriv 1 (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w)) w := by
        have h := (hasDerivAt_const w (1 / 2 : ℂ)).sub (hlin.mul hI)
        convert h using 1
        ring
      rw [hH.deriv]
      rw [iteratedDeriv_zero]
      ring
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hopen : {z : ℂ | -(1 : ℝ) / 2 < z.re} ∈ 𝓝 w :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
      have heq : iteratedDeriv (k + 1) (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) =ᶠ[𝓝 w]
          (fun z : ℂ => -((1 + z) * iteratedDeriv (k + 1) (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) z)
            - ((k : ℂ) + 1) * iteratedDeriv k (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) z) := by
        filter_upwards [hopen] with z hz
        exact ih z hz
      rw [heq.deriv_eq]
      -- derivatives of the two factors
      have hJ : ∀ m : ℕ, HasDerivAt (fun y : ℂ => iteratedDeriv m (fun z : ℂ =>
          ∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) y)
          (iteratedDeriv (m + 1) (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) w) w := by
        intro m
        have heq : (fun y : ℂ => iteratedDeriv m (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
            (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) y) =ᶠ[𝓝 w]
            (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) *
              (-(Real.log u : ℂ)) ^ m * (u : ℂ) ^ (-2 - y)) := by
          filter_upwards [hopen] with z hz
          exact iteratedDeriv_weight m z hz
        refine heq.hasDerivAt_iff.mpr ?_
        exact (hasDerivAt_weight m w hw).congr_deriv (iteratedDeriv_weight (m + 1) w hw).symm
      have hJk := hJ (k + 1)
      have hJk1 := hJ k
      have hlin : HasDerivAt (fun z : ℂ => 1 + z) 1 w := by
        simpa using (hasDerivAt_id w).const_add (1 : ℂ)
      have hmain0 : HasDerivAt (fun z : ℂ => -((1 + z) * iteratedDeriv (k + 1) (fun y : ℂ =>
            ∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) z)
            - ((k : ℂ) + 1) * iteratedDeriv k (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) z)
          (-(1 * iteratedDeriv (k + 1) (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) w
            + (1 + w) * iteratedDeriv (k + 1 + 1) (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) w)
            - ((k : ℂ) + 1) * iteratedDeriv (k + 1) (fun y : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
              (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - y)) w) w := by
        have h := (hlin.mul hJk).neg.sub (hJk1.const_mul ((k : ℂ) + 1))
        convert h using 1
      rw [hmain0.deriv]
      push_cast
      ring


/-- The `m`-th weight derivative at the origin is the real logarithmic moment. -/
private lemma iteratedDeriv_weight_zero (m : ℕ) :
    iteratedDeriv m (fun w : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - w)) 0
      = ((∫ u : ℝ in Ioi (1 : ℝ),
          (-1 : ℝ) ^ m * (periodicBernoulli 1 u * Real.log u ^ m / u ^ 2) : ℝ) : ℂ) := by
  rw [iteratedDeriv_weight m 0 (by norm_num)]
  have hsimp : (-2 - (0 : ℂ)) = (-2 : ℂ) := by norm_num
  simp only [hsimp]
  have hcongr : (∫ u : ℝ in Ioi (1 : ℝ), (periodicBernoulli 1 u : ℂ) *
        (-(Real.log u : ℂ)) ^ m * ((u : ℂ) ^ ((-2 : ℂ))))
      = ∫ u : ℝ in Ioi (1 : ℝ),
          ((((-1 : ℝ) ^ m * (periodicBernoulli 1 u * Real.log u ^ m / u ^ 2)) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    have hz : ((u : ℂ) ^ ((-2 : ℂ))) = ((1 / u ^ 2 : ℝ) : ℂ) := by
      have h1 : ((-2 : ℂ)) = ((-2 : ℝ) : ℂ) := by norm_num
      rw [h1, ← Complex.ofReal_cpow hu0.le]
      congr 1
      rw [Real.rpow_neg hu0.le, Real.rpow_two, inv_eq_one_div]
    have hl : (-(Real.log u : ℂ)) ^ m = (((-1 : ℝ) ^ m * Real.log u ^ m : ℝ) : ℂ) := by
      push_cast
      rw [neg_pow]
    rw [hz, hl]
    push_cast
    ring
  rw [hcongr]
  exact integral_ofReal

/-- The periodic weight times a logarithmic moment is integrable. -/
private lemma integrable_periodic_log (j : ℕ) :
    IntegrableOn (fun x : ℝ => periodicBernoulli 1 x * Real.log x ^ j / x ^ 2) (Ioi (1 : ℝ)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.log x ^ j / x ^ (1 + 1)) (Ioi (1 : ℝ)) :=
    Decomp608b.log_moment_integrable 1 j (by norm_num)
  have hm : Measurable (periodicBernoulli 1) := by
    unfold periodicBernoulli bernoulliFun
    fun_prop
  have h2 : IntegrableOn (fun x : ℝ => periodicBernoulli 1 x * (Real.log x ^ j / x ^ 2))
      (Ioi (1 : ℝ)) := by
    refine h1.bdd_mul (c := 1 / 2) hm.aestronglyMeasurable ?_
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using Decomp608c.periodicBernoulli_one_bound x
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro x _
  ring

/-- The degree-one integral of the chain. -/
private lemma integral_degree_one (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli 1 x *
        ((derivativePoly n 1).eval (Real.log x) / x ^ 2))
      = ((n : ℝ) * (∫ x : ℝ in Ioi (1 : ℝ),
            periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)
          - (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli 1 x * Real.log x ^ n / x ^ 2))
        * ((n.factorial : ℝ))⁻¹ := by
  have hpt : ∀ x : ℝ, periodicBernoulli 1 x * ((derivativePoly n 1).eval (Real.log x) / x ^ 2)
      = ((n : ℝ) * (periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)
        - periodicBernoulli 1 x * Real.log x ^ n / x ^ 2) * ((n.factorial : ℝ))⁻¹ := by
    intro x
    rw [derivativePoly_one_eval]
    ring
  have hint1 : IntegrableOn (fun x : ℝ => (n : ℝ) *
      (periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)) (Ioi (1 : ℝ)) :=
    (integrable_periodic_log (n - 1)).const_mul _
  have hint2 : IntegrableOn (fun x : ℝ =>
      periodicBernoulli 1 x * Real.log x ^ n / x ^ 2) (Ioi (1 : ℝ)) :=
    integrable_periodic_log n
  calc (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli 1 x *
        ((derivativePoly n 1).eval (Real.log x) / x ^ 2))
      = ∫ x : ℝ in Ioi (1 : ℝ), ((n : ℝ) * (periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)
          - periodicBernoulli 1 x * Real.log x ^ n / x ^ 2) * ((n.factorial : ℝ))⁻¹ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpt x
    _ = (∫ x : ℝ in Ioi (1 : ℝ), ((n : ℝ) * (periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)
          - periodicBernoulli 1 x * Real.log x ^ n / x ^ 2)) * ((n.factorial : ℝ))⁻¹ :=
        integral_mul_const _ _
    _ = _ := by
        rw [integral_sub hint1 hint2, integral_const_mul]

/-- The integral of the chain in degree one, and the whole chain. -/
private lemma integral_chain (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli n x *
        ((derivativePoly n n).eval (Real.log x) / x ^ (n + 1)))
      = ((-1 : ℝ) ^ (n - 1)) * (((n : ℝ) * (∫ x : ℝ in Ioi (1 : ℝ),
            periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)
          - (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli 1 x * Real.log x ^ n / x ^ 2))
        * ((n.factorial : ℝ))⁻¹) := by
  have hchain := ibp_chain n n hn le_rfl
  rw [hchain, integral_degree_one n hn]


/-- The Laurent coefficient as an explicit real moment combination. -/
private lemma laurentCoeff_moment_form (n : ℕ) (hn : 1 ≤ n) :
    laurentCoeff n = (((-1 : ℝ) ^ (n + 1) * (((∫ x : ℝ in Ioi (1 : ℝ),
        periodicBernoulli 1 x * Real.log x ^ n / x ^ 2)
      - (n : ℝ) * (∫ x : ℝ in Ioi (1 : ℝ),
        periodicBernoulli 1 x * Real.log x ^ (n - 1) / x ^ 2)) * ((n.factorial : ℝ))⁻¹)) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  have hreg : iteratedDeriv (m + 1) regularPart 0 =
      iteratedDeriv (m + 1) (fun z : ℂ => 1 / 2 - (1 + z) * ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) 0 :=
    regularPart_eventuallyEq.iteratedDeriv_eq (m + 1)
  have hexpr := iteratedDeriv_regularPart_expression m 0 (by norm_num)
  have hJ1 : iteratedDeriv (m + 1) (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) 0
      = ((-1 : ℝ) ^ (m + 1) * (∫ u : ℝ in Ioi (1 : ℝ),
          periodicBernoulli 1 u * Real.log u ^ (m + 1) / u ^ 2) : ℂ) := by
    rw [iteratedDeriv_weight_zero (m + 1), integral_const_mul]
    push_cast
    ring
  have hJ0 : iteratedDeriv m (fun z : ℂ => ∫ u : ℝ in Ioi (1 : ℝ),
        (periodicBernoulli 1 u : ℂ) * (u : ℂ) ^ (-2 - z)) 0
      = ((-1 : ℝ) ^ m * (∫ u : ℝ in Ioi (1 : ℝ),
          periodicBernoulli 1 u * Real.log u ^ m / u ^ 2) : ℂ) := by
    rw [iteratedDeriv_weight_zero m, integral_const_mul]
    push_cast
    ring
  rw [laurentCoeff, hreg, hexpr, hJ1, hJ0]
  push_cast
  have hs1 : (-1 : ℂ) ^ (m + 1) = -(-1 : ℂ) ^ m := by rw [pow_succ]; ring
  have hs2 : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by rw [pow_succ, hs1]; ring
  rw [hs1, hs2]
  have hfr : (((m + 1).factorial : ℝ) : ℂ) ≠ 0 := by
    have h : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  field_simp
  ring

/-- LEAF. Berndt 1972 page 153 display 3.1 at a equal to one.
The coefficients c_n equal the Laurent coefficients by page 152. -/
theorem leaf_laurent_integral (n : ℕ) (hn : 1 ≤ n) :
    laurentCoeff n = -((∫ x : ℝ in Ioi 1,
      periodicBernoulli n x * iteratedDeriv n (berndtKernel n) x : ℝ) : ℂ) := by
  have hker : (∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli n x *
        iteratedDeriv n (berndtKernel n) x)
      = ∫ x : ℝ in Ioi (1 : ℝ), periodicBernoulli n x *
        ((derivativePoly n n).eval (Real.log x) / x ^ (n + 1)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hk : berndtKernel n = fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ)) := rfl
    rw [hk, Decomp608e.iteratedDeriv_kernel_eq n n hx0]
  rw [hker, integral_chain n hn, laurentCoeff_moment_form n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  push_cast
  have hs : (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
    rw [pow_succ, show (-1 : ℂ) ^ (m + 1) = -(-1 : ℂ) ^ m by rw [pow_succ]; ring]
    ring
  rw [hs]
  have hfr : (((m + 1).factorial : ℝ) : ℂ) ≠ 0 := by
    have h : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  field_simp
  ring

/-- Berndt 1972 page 153 displays 3.2 and 3.3.
The absolute recurrence is Nat.stirlingFirst. The sign is minus one to j. -/
theorem leaf_log_power_derivative (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    iteratedDeriv n (berndtKernel n) x =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1)) := by
  rw [show berndtKernel n =
    (fun y : ℝ => Real.log y ^ n / (y * (n.factorial : ℝ))) from rfl]
  exact Decomp608e.iteratedDeriv_kernel_formula n (x := x) (lt_of_lt_of_le zero_lt_one hx)

/-! ### Low harmonics at the point one quarter

Writing `t = 1/4 + v`, the first four terms of the Fourier series of the normalized Bernoulli
polynomial are `cos (2πv)`, `-sin (4πv)/2^n`, `-cos (6πv)/3^n` and `sin (8πv)/4^n`. -/

private theorem sin_low_one (t : ℝ) :
    Real.sin (2 * Real.pi * 1 * t) = Real.cos (2 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 1 * t = Real.pi / 2 + 2 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private theorem sin_low_two (t : ℝ) :
    Real.sin (2 * Real.pi * 2 * t) = -Real.sin (4 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 2 * t = Real.pi + 4 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_pi, Real.cos_pi]
  ring

private theorem sin_low_three (t : ℝ) :
    Real.sin (2 * Real.pi * 3 * t) = -Real.cos (6 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 3 * t = 3 * Real.pi / 2 + 6 * Real.pi * (t - 1 / 4) := by ring
  have h2 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  have h1 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [h2, Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  have h3 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [h2, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  rw [h, Real.sin_add, h1, h3]
  ring

private theorem sin_low_four (t : ℝ) :
    Real.sin (2 * Real.pi * 4 * t) = Real.sin (8 * Real.pi * (t - 1 / 4)) := by
  have h : 2 * Real.pi * 4 * t = 2 * Real.pi + 8 * Real.pi * (t - 1 / 4) := by ring
  rw [h, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
  ring

/-- The quadratic lower bound for `1 - cos` used at odd degrees, coarse version. -/
private theorem sin_sq_lower_coarse (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) :
    15.5 * a ^ 2 ≤ 2 * Real.sin (Real.pi * a) ^ 2 := by
  have hp := Real.pi_gt_d6
  have hp2 : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have ha2 : a ^ 2 ≤ 1 / 16 := by nlinarith
  have hpnn : 0 ≤ Real.pi ^ 2 := by positivity
  have ha2nn : 0 ≤ a ^ 2 := by positivity
  have hsq : (Real.pi * a) ^ 2 ≤ 0.617 := by
    rw [mul_pow]
    calc Real.pi ^ 2 * a ^ 2 ≤ 9.87 * (1 / 16) :=
          mul_le_mul hp2 ha2 ha2nn (by norm_num)
      _ ≤ 0.617 := by norm_num
  have hpa : 0 ≤ Real.pi * a := by positivity
  have hs := Real.sin_ge_sub_cube (x := Real.pi * a) hpa
  have hstep : (Real.pi * a) ^ 3 / 6 ≤ 0.104 * (Real.pi * a) := by
    have h1 : (Real.pi * a) ^ 2 / 6 ≤ 0.104 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpa
    calc (Real.pi * a) ^ 3 / 6 = (Real.pi * a) * ((Real.pi * a) ^ 2 / 6) := by ring
      _ ≤ (Real.pi * a) * 0.104 := h2
      _ = 0.104 * (Real.pi * a) := by ring
  have hlin : 0.896 * (Real.pi * a) ≤ Real.sin (Real.pi * a) := by linarith
  have hnn : 0 ≤ 0.896 * (Real.pi * a) := by positivity
  have hsq2 : (0.896 * (Real.pi * a)) ^ 2 ≤ Real.sin (Real.pi * a) ^ 2 :=
    pow_le_pow_left₀ hnn hlin 2
  have hkey : 15.5 * a ^ 2 ≤ 2 * (0.896 * (Real.pi * a)) ^ 2 := by
    have hpi2 : 9.8696 ≤ Real.pi ^ 2 := by nlinarith
    calc 15.5 * a ^ 2 ≤ 2 * 0.896 ^ 2 * 9.8696 * a ^ 2 := by nlinarith
      _ ≤ 2 * 0.896 ^ 2 * Real.pi ^ 2 * a ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ ha2nn
          nlinarith
      _ = 2 * (0.896 * (Real.pi * a)) ^ 2 := by ring
  linarith

/-- The quadratic lower bound for `1 - cos` used at odd degrees, sharp near zero. -/
private theorem sin_sq_lower_fine (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 32) :
    19 * a ^ 2 ≤ 2 * Real.sin (Real.pi * a) ^ 2 := by
  have hp := Real.pi_gt_d6
  have hp2 : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have ha2 : a ^ 2 ≤ 1 / 1024 := by nlinarith
  have hpnn : 0 ≤ Real.pi ^ 2 := by positivity
  have ha2nn : 0 ≤ a ^ 2 := by positivity
  have hsq : (Real.pi * a) ^ 2 ≤ 0.00965 := by
    rw [mul_pow]
    calc Real.pi ^ 2 * a ^ 2 ≤ 9.87 * (1 / 1024) :=
          mul_le_mul hp2 ha2 ha2nn (by norm_num)
      _ ≤ 0.00965 := by norm_num
  have hpa : 0 ≤ Real.pi * a := by positivity
  have hs := Real.sin_ge_sub_cube (x := Real.pi * a) hpa
  have hstep : (Real.pi * a) ^ 3 / 6 ≤ 0.0017 * (Real.pi * a) := by
    have h1 : (Real.pi * a) ^ 2 / 6 ≤ 0.0017 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpa
    calc (Real.pi * a) ^ 3 / 6 = (Real.pi * a) * ((Real.pi * a) ^ 2 / 6) := by ring
      _ ≤ (Real.pi * a) * 0.0017 := h2
      _ = 0.0017 * (Real.pi * a) := by ring
  have hlin : 0.9983 * (Real.pi * a) ≤ Real.sin (Real.pi * a) := by linarith
  have hnn : 0 ≤ 0.9983 * (Real.pi * a) := by positivity
  have hsq2 : (0.9983 * (Real.pi * a)) ^ 2 ≤ Real.sin (Real.pi * a) ^ 2 :=
    pow_le_pow_left₀ hnn hlin 2
  have hkey : 19 * a ^ 2 ≤ 2 * (0.9983 * (Real.pi * a)) ^ 2 := by
    have hpi2 : 9.8696 ≤ Real.pi ^ 2 := by nlinarith
    calc 19 * a ^ 2 ≤ 2 * 0.9983 ^ 2 * 9.8696 * a ^ 2 := by nlinarith
      _ ≤ 2 * 0.9983 ^ 2 * Real.pi ^ 2 * a ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ ha2nn
          nlinarith
      _ = 2 * (0.9983 * (Real.pi * a)) ^ 2 := by ring
  linarith

/-- Step one of the tail estimate: a one-step telescoping majorant for `1/m^5`. -/
private lemma one_div_pow_five_le_telescope (j : ℕ) :
    (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ 5 ≤
      (1 / 4) * ((1 : ℝ) / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) := by
  set m : ℝ := ((j + 5 : ℕ) : ℝ) with hm
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hm2 : (2 : ℝ) ≤ m := by rw [hm]; push_cast; linarith
  have hc : ((j + 4 : ℕ) : ℝ) = m - 1 := by rw [hm]; push_cast; ring
  have h1 : (0 : ℝ) < m - 1 := by linarith
  have h2 : (0 : ℝ) < m := by linarith
  have hden : (0 : ℝ) < 4 * (m - 1) ^ 4 * m ^ 5 := by positivity
  have key : (1 / 4 : ℝ) * (1 / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) -
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ 5 =
      (10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4) / (4 * (m - 1) ^ 4 * m ^ 5) := by
    rw [hc, ← hm]
    field_simp
    ring
  have hnum : (0 : ℝ) ≤ 10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4 := by
    have hfac : 10 * m ^ 3 - 20 * m ^ 2 + 15 * m - 4 =
        10 * m ^ 2 * (m - 2) + (15 * m - 4) := by ring
    rw [hfac]
    have : (0 : ℝ) ≤ 10 * m ^ 2 * (m - 2) := by
      have := mul_nonneg (sq_nonneg m) (by linarith : (0:ℝ) ≤ m - 2)
      linarith
    linarith
  rw [← sub_nonneg, key]
  exact div_nonneg hnum hden.le

/-- Step two: the telescoped partial sums. -/
private lemma telescope_sum_range (J : ℕ) :
    ∑ j ∈ Finset.range J,
        ((1 : ℝ) / ((j + 4 : ℕ) : ℝ) ^ 4 - 1 / ((j + 5 : ℕ) : ℝ) ^ 4) =
      1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The terms beyond the fifth one, with the uniform geometric decay of the bound. -/
private lemma tail_bound (n : ℕ) (hn : 5 ≤ n) :
    (∑' j : ℕ, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) ≤ 0.001 / (5 : ℝ) ^ (n - 5) := by
  open Filter in
  have hterm : ∀ j : ℕ,
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        (1 / (5 : ℝ) ^ (n - 5)) * (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := by
    intro j
    set m : ℝ := ((j + 5 : ℕ) : ℝ) with hm
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hm5 : (5 : ℝ) ≤ m := by rw [hm]; push_cast; linarith
    have hm0 : (0 : ℝ) < m := by linarith
    have hpow : m ^ n = m ^ 5 * m ^ (n - 5) := by
      have h : n = 5 + (n - 5) := by omega
      conv_lhs => rw [h]
      rw [pow_add]
    have hmn : 0 < m ^ (n - 5) := pow_pos hm0 _
    have h2 : (1 : ℝ) / m ^ (n - 5) ≤ 1 / (5 : ℝ) ^ (n - 5) := by
      apply one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 5) _)
      exact pow_le_pow_left₀ (by norm_num) hm5 _
    have h3 : (1 : ℝ) / (5 : ℝ) ^ (n - 5) = 1 / (5 : ℝ) ^ (n - 5) := rfl
    calc (1 : ℝ) / m ^ n = (1 / m ^ 5) * (1 / m ^ (n - 5)) := by
          rw [hpow]; field_simp
      _ ≤ (1 / m ^ 5) * (1 / (5 : ℝ) ^ (n - 5)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / (5 : ℝ) ^ (n - 5)) * (1 / m ^ 5) := by rw [h3]; ring
  have hsummable : Summable (fun j : ℕ => (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) := by
    have h := (Real.summable_one_div_nat_pow (p := n)).mpr (by omega)
    exact h.comp_injective (fun a b hab => by simpa using hab)
  have hpartial : ∀ J : ℕ,
      ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        0.001 / (5 : ℝ) ^ (n - 5) := by
    intro J
    have h1 : ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n ≤
        (1 / (5 : ℝ) ^ (n - 5)) * ∑ j ∈ Finset.range J,
          (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := by
      calc ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n
          ≤ ∑ j ∈ Finset.range J,
              (1 / (5 : ℝ) ^ (n - 5)) * (1 / ((j + 5 : ℕ) : ℝ) ^ 5) :=
            Finset.sum_le_sum (fun j _ => hterm j)
        _ = (1 / (5 : ℝ) ^ (n - 5)) * ∑ j ∈ Finset.range J,
              (1 / ((j + 5 : ℕ) : ℝ) ^ 5) := (Finset.mul_sum _ _ _).symm
    have h2 : ∑ j ∈ Finset.range J, (1 / ((j + 5 : ℕ) : ℝ) ^ 5) ≤
        (1 / 4) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4) := by
      rw [← telescope_sum_range J, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => one_div_pow_five_le_telescope j)
    have h3 : (0 : ℝ) ≤ 1 / (5 : ℝ) ^ (n - 5) := by positivity
    have h4 : (1 / 4 : ℝ) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4) ≤ 1 / 1024 := by
      have hpos : (0 : ℝ) ≤ 1 / ((J + 4 : ℕ) : ℝ) ^ 4 := by positivity
      have heq : (1 / 4 : ℝ) * (1 / 4 ^ 4) = 1 / 1024 := by norm_num
      nlinarith
    calc ∑ j ∈ Finset.range J, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n
        ≤ (1 / (5 : ℝ) ^ (n - 5)) * ((1 / 4) * (1 / 4 ^ 4 - 1 / ((J + 4 : ℕ) : ℝ) ^ 4)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 h3)
      _ ≤ (1 / (5 : ℝ) ^ (n - 5)) * (1 / 1024) := mul_le_mul_of_nonneg_left h4 h3
      _ ≤ 0.001 / (5 : ℝ) ^ (n - 5) := by
          have h5p : (0 : ℝ) < (5 : ℝ) ^ (n - 5) := pow_pos (by norm_num) _
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) h5p]
          nlinarith
  have htend : Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J,
      (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n) atTop
        (nhds (∑' j : ℕ, (1 : ℝ) / ((j + 5 : ℕ) : ℝ) ^ n)) :=
    hsummable.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto htend tendsto_const_nhds (Eventually.of_forall hpartial)

/-- The quadratic lower bound for a cosine, from `1 - t^2/2 ≤ cos t`. -/
private theorem cos_lower_quadratic (v : ℝ) :
    1 - 178 * v ^ 2 ≤ Real.cos (6 * Real.pi * v) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := 6 * Real.pi * v)
  have hp : Real.pi ^ 2 ≤ 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hsq : (6 * Real.pi * v) ^ 2 / 2 ≤ 178 * v ^ 2 := by
    have he : (6 * Real.pi * v) ^ 2 / 2 = 18 * Real.pi ^ 2 * v ^ 2 := by ring
    rw [he]
    nlinarith
  linarith

/-- The squared sine only sees the absolute value. -/
private theorem sin_sq_abs (v : ℝ) :
    2 * Real.sin (Real.pi * v) ^ 2 = 2 * Real.sin (Real.pi * |v|) ^ 2 := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
  · rw [abs_of_nonpos hv]
    rw [show Real.pi * -v = -(Real.pi * v) by ring, Real.sin_neg]
    ring

/-- The size of the two even harmonics kept explicitly. -/
private theorem even_harmonic_coefficient (n : ℕ) (hn : 5 ≤ n) :
    4 * Real.pi / (2 : ℝ) ^ n + 8 * Real.pi / (4 : ℝ) ^ n ≤ 13.39 / (2 : ℝ) ^ n := by
  have hp := Real.pi_lt_d2
  have h2n : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2ge : (32 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : ((2:ℝ)) ^ 5 = 32 := by norm_num
    rw [← h]; exact h2n
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h4e : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
  have hfac : 4 * Real.pi / (2 : ℝ) ^ n + 8 * Real.pi / (4 : ℝ) ^ n =
      (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 2 / (2 : ℝ) ^ n) := by
    rw [h4e]
    field_simp
    ring
  rw [hfac]
  have hstep1 : 2 / (2 : ℝ) ^ n ≤ 1 / 16 := by
    rw [div_le_iff₀ h2pos]
    nlinarith
  have hstep2 : (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 2 / (2 : ℝ) ^ n) ≤
      (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 1 / 16) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hstep3 : (4 * Real.pi / (2 : ℝ) ^ n) * (1 + 1 / 16) ≤ 13.39 / (2 : ℝ) ^ n := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ h2pos.le
    nlinarith
  linarith

/-- `1/4^n` as a multiple of `1/3^n`. -/
private theorem inv_four_pow_eq (n : ℕ) :
    (1 : ℝ) / (4 : ℝ) ^ n = ((3 : ℝ) / 4) ^ n * (1 / (3 : ℝ) ^ n) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  rw [div_pow]
  field_simp

/-- `1/5^(n-5)` as a multiple of `1/3^n`. -/
private theorem inv_five_pow_eq (n : ℕ) (hn : 5 ≤ n) :
    0.001 / (5 : ℝ) ^ (n - 5) =
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n * (1 / (3 : ℝ) ^ n)) := by
  have h5 : (0 : ℝ) < (5 : ℝ) ^ n := by positivity
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hsplit : (5 : ℝ) ^ n = (5 : ℝ) ^ (n - 5) * (5 : ℝ) ^ 5 := by
    conv_lhs => rw [show n = (n - 5) + 5 by omega]
    rw [pow_add]
  rw [div_pow, hsplit]
  field_simp

/-- The numeric core of the sharp region estimate. -/
private theorem sharp_region_numeric (n : ℕ) (hn : 5 ≤ n) :
    (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 + 0.001 / (5 : ℝ) ^ (n - 5) ≤ 1 / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h34 : ((3 : ℝ) / 4) ^ n ≤ ((3 : ℝ) / 4) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h35 : ((3 : ℝ) / 5) ^ n ≤ ((3 : ℝ) / 5) ^ 5 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h4e : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hsq : (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 = 179.2921 / 73.04 * (1 / (4 : ℝ) ^ n) := by
    rw [h4e]
    field_simp
    ring
  rw [hsq, inv_four_pow_eq n, inv_five_pow_eq n hn]
  have key : 179.2921 / 73.04 * ((3 : ℝ) / 4) ^ n +
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n) ≤ 1 := by
    nlinarith [h34, h35]
  have hform : 179.2921 / 73.04 * (((3 : ℝ) / 4) ^ n * (1 / (3 : ℝ) ^ n)) +
      0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n * (1 / (3 : ℝ) ^ n)) =
      (1 / (3 : ℝ) ^ n) * (179.2921 / 73.04 * ((3 : ℝ) / 4) ^ n +
        0.001 * ((5 : ℝ) ^ 5 * ((3 : ℝ) / 5) ^ n)) := by
    field_simp
  rw [hform]
  exact mul_le_of_le_one_right (by positivity) key

/-- The sharp region `a ≤ 1/32`: the cosine term pays for the tail. -/
private theorem region_sharp (n : ℕ) (hn : 5 ≤ n) (a C : ℝ)
    (hC : C ≤ 13.39 / (2 : ℝ) ^ n) (hCn : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 32) :
    C * a + 0.001 / (5 : ℝ) ^ (n - 5) ≤
      2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3ge : (243 : ℝ) ≤ (3 : ℝ) ^ n := by
    have h : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
    linarith [h2 ▸ h]
  have hsq : 2 * Real.sin (Real.pi * a) ^ 2 ≥ 19 * a ^ 2 := sin_sq_lower_fine a ha0 ha
  have hfrac : 178 * a ^ 2 / (3 : ℝ) ^ n ≤ 0.74 * a ^ 2 := by
    rw [div_le_iff₀ h3]
    nlinarith [sq_nonneg a]
  have hkey : C * a - 18.26 * a ^ 2 ≤ 1 / (3 : ℝ) ^ n - 0.001 / (5 : ℝ) ^ (n - 5) := by
    have hmain : C ^ 2 / 73.04 ≤ 1 / (3 : ℝ) ^ n - 0.001 / (5 : ℝ) ^ (n - 5) := by
      have h1 : C ^ 2 ≤ (13.39 / (2 : ℝ) ^ n) ^ 2 := pow_le_pow_left₀ hCn hC 2
      have h2 : C ^ 2 / 73.04 ≤ (13.39 / (2 : ℝ) ^ n) ^ 2 / 73.04 :=
        div_le_div_of_nonneg_right h1 (by norm_num)
      have h3' := sharp_region_numeric n hn
      linarith
    have h4 : C * a - 18.26 * a ^ 2 ≤ C ^ 2 / 73.04 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [sq_nonneg (C - 36.52 * a)]
    nlinarith [sq_nonneg a]
  have hgoal : (1 - 178 * a ^ 2) / (3 : ℝ) ^ n = 1 / (3 : ℝ) ^ n - 178 * a ^ 2 / (3 : ℝ) ^ n := by
    rw [← sub_div]
  rw [hgoal]
  linarith

/-- The coarse region `1/32 ≤ a`: no use of the cosine sign. -/
private theorem region_coarse (n : ℕ) (hn : 5 ≤ n) (a C : ℝ)
    (hC : C ≤ 13.39 / (2 : ℝ) ^ n) (hCn : 0 ≤ C) (ha : 1 / 32 ≤ a) (ha4 : a ≤ 1 / 4) :
    C * a + 0.001 / (5 : ℝ) ^ (n - 5) ≤
      2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ n := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have ha0 : 0 ≤ a := by linarith
  have h2ge : (32 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h' : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (2 : ℝ) ^ 5 = 32 := by norm_num
    linarith [h2 ▸ h']
  have h3ge : (243 : ℝ) ≤ (3 : ℝ) ^ n := by
    have h' : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
    linarith [h2 ▸ h']
  have hsq : 2 * Real.sin (Real.pi * a) ^ 2 ≥ 15.5 * a ^ 2 := sin_sq_lower_coarse a ha0 ha4
  have hfrac : 178 * a ^ 2 / (3 : ℝ) ^ n ≤ 0.74 * a ^ 2 := by
    rw [div_le_iff₀ h3]
    nlinarith [sq_nonneg a]
  have hC32 : C ≤ 13.39 / 32 := by
    have h1 : 13.39 / (2 : ℝ) ^ n ≤ 13.39 / 32 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2ge
    linarith
  have hmono : 14.76 * (1 / 32) ^ 2 - C * (1 / 32) ≤ 14.76 * a ^ 2 - C * a := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1 / 32)
      (by linarith : (0 : ℝ) ≤ 14.76 * (a + 1 / 32) - C)]
  have htau : 0.001 / (5 : ℝ) ^ (n - 5) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ (n - 5) := one_le_pow₀ (by norm_num)
    nlinarith
  have hval : (14.76 : ℝ) * (1 / 32) ^ 2 = 14.76 / 1024 := by norm_num
  have hCs : C / 32 ≤ 13.39 / 1024 := by
    have h1 : C / 32 ≤ 13.39 / 32 / 32 := div_le_div_of_nonneg_right hC32 (by norm_num)
    have h2 : (13.39 : ℝ) / 32 / 32 = 13.39 / 1024 := by norm_num
    linarith [h2 ▸ h1]
  have hpos3 : (0 : ℝ) < 1 / (3 : ℝ) ^ n := by positivity
  have hfracgoal : (1 - 178 * a ^ 2) / (3 : ℝ) ^ n = 1 / (3 : ℝ) ^ n - 178 * a ^ 2 / (3 : ℝ) ^ n := by
    rw [← sub_div]
  rw [hfracgoal]
  nlinarith [hsq, hfrac, hmono, htau, hCs, hval]

set_option maxHeartbeats 2000000 in
/-- The sine series of Berndt display 3.7 is bounded by one at odd degrees. -/
private theorem abs_tsum_sin_le_one (n : ℕ) (hn : 5 ≤ n) (ho : Odd n)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ n * Real.sin (2 * Real.pi * m * t)| ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
  have hk : k ≠ 0 := by omega
  set v : ℝ := t - 1 / 4 with hv
  set a : ℝ := |v| with ha
  have hav : a ≤ 1 / 4 := by
    rw [ha, abs_le]
    constructor <;> rw [hv] <;> linarith
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg v
  set C : ℝ := 4 * Real.pi / (2 : ℝ) ^ (2 * k + 1) + 8 * Real.pi / (4 : ℝ) ^ (2 * k + 1)
    with hCdef
  have hCn : 0 ≤ C := by rw [hCdef]; positivity
  have hCbound : C ≤ 13.39 / (2 : ℝ) ^ (2 * k + 1) := by
    rw [hCdef]; exact even_harmonic_coefficient (2 * k + 1) (by omega)
  set F : ℕ → ℝ := fun m => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)
    with hF
  have hFsummable : Summable F := by
    have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
      (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
    refine Summable.of_norm_bounded hbase (fun m => ?_)
    rw [hF, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ) ^ (2 * k + 1))]
    have hs : |Real.sin (2 * Real.pi * m * t)| ≤ 1 := Real.abs_sin_le_one _
    have hnn : (0 : ℝ) ≤ 1 / (m : ℝ) ^ (2 * k + 1) := by positivity
    nlinarith
  have hsplit := hFsummable.sum_add_tsum_nat_add 5
  -- the first five terms
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = Real.cos (2 * Real.pi * v) := by
    simp only [hF, Nat.cast_one, one_pow, div_one, one_mul, sin_low_one, hv]
  have hF2 : F 2 = -(1 / (2 : ℝ) ^ (2 * k + 1)) * Real.sin (4 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_two]
    ring
  have hF3 : F 3 = -(1 / (3 : ℝ) ^ (2 * k + 1)) * Real.cos (6 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_three]
    ring
  have hF4 : F 4 = (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) := by
    simp only [hF, Nat.cast_ofNat, sin_low_four]
    ring
  have hterms : ∑ m ∈ Finset.range 5, F m =
      Real.cos (2 * Real.pi * v) - (1 / (2 : ℝ) ^ (2 * k + 1)) * Real.sin (4 * Real.pi * v)
        - (1 / (3 : ℝ) ^ (2 * k + 1)) * Real.cos (6 * Real.pi * v)
        + (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      hF0, hF1, hF2, hF3, hF4]
    ring
  -- the tail
  have htail : |∑' i : ℕ, F (i + 5)| ≤ 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
    have hsum_abs : Summable (fun i : ℕ => ‖F (i + 5)‖) := by
      have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
        (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
      have hcomp : Summable (fun i : ℕ => (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) :=
        hbase.comp_injective (fun x y hxy => by simpa using hxy)
      refine Summable.of_norm_bounded hcomp (fun i => ?_)
      have hval : ‖F (i + 5)‖ = (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
          |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| := by
        simp only [hF, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1))]
      rw [hval, Real.norm_of_nonneg (by positivity :
        (0 : ℝ) ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
          |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|)]
      have hs : |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| ≤ 1 := Real.abs_sin_le_one _
      have hnn : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by positivity
      calc (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
            |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|
          ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) * 1 := mul_le_mul_of_nonneg_left hs hnn
        _ = 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := mul_one _
    have hcompS : Summable (fun i : ℕ => (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) := by
      have hbase : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * k + 1)) :=
        (Real.summable_one_div_nat_pow (p := 2 * k + 1)).mpr (by omega)
      exact hbase.comp_injective (fun x y hxy => by simpa using hxy)
    calc |∑' i : ℕ, F (i + 5)|
        ≤ ∑' i : ℕ, ‖F (i + 5)‖ := norm_tsum_le_tsum_norm hsum_abs
      _ ≤ ∑' i : ℕ, (1 : ℝ) / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by
          apply Summable.tsum_le_tsum _ hsum_abs hcompS
          intro i
          have hval : ‖F (i + 5)‖ = (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
              |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| := by
            simp only [hF, Real.norm_eq_abs, abs_mul]
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1))]
          rw [hval]
          try rw [Real.norm_of_nonneg (by positivity :
            (0 : ℝ) ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
              |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|)]
          have hs : |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)| ≤ 1 := Real.abs_sin_le_one _
          have hnn : (0 : ℝ) ≤ 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := by positivity
          calc (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) *
                |Real.sin (2 * Real.pi * ((i + 5 : ℕ) : ℝ) * t)|
              ≤ (1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1)) * 1 := mul_le_mul_of_nonneg_left hs hnn
            _ = 1 / ((i + 5 : ℕ) : ℝ) ^ (2 * k + 1) := mul_one _
      _ ≤ 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := tail_bound (2 * k + 1) (by omega)
  -- elementary bounds on the individual harmonics
  have hsin4 : |Real.sin (4 * Real.pi * v)| ≤ 4 * Real.pi * a := by
    rw [ha]
    calc |Real.sin (4 * Real.pi * v)| ≤ |4 * Real.pi * v| := Real.abs_sin_le_abs
      _ = 4 * Real.pi * |v| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          norm_num
  have hsin8 : |Real.sin (8 * Real.pi * v)| ≤ 8 * Real.pi * a := by
    rw [ha]
    calc |Real.sin (8 * Real.pi * v)| ≤ |8 * Real.pi * v| := Real.abs_sin_le_abs
      _ = 8 * Real.pi * |v| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
          norm_num
  have hcos_eq : Real.cos (2 * Real.pi * v) = 1 - 2 * Real.sin (Real.pi * a) ^ 2 := by
    have hs := Real.sin_sq_eq_half_sub (Real.pi * v)
    have harg : 2 * (Real.pi * v) = 2 * Real.pi * v := by ring
    rw [harg] at hs
    have hsabs : 2 * Real.sin (Real.pi * v) ^ 2 = 2 * Real.sin (Real.pi * a) ^ 2 := by
      rw [ha]; exact sin_sq_abs v
    linarith
  have hcos_nonneg : 0 ≤ Real.cos (2 * Real.pi * v) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith [abs_le.mp hav, Real.pi_pos]
    · nlinarith [abs_le.mp hav, Real.pi_pos]
  -- upper bound for the first five terms
  have hupper : ∑ m ∈ Finset.range 5, F m ≤ 1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
    rw [hterms, hcos_eq]
    have h2 : -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)) ≤
        (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by
      have hs : -Real.sin (4 * Real.pi * v) ≤ 4 * Real.pi * a := by
        linarith [neg_abs_le (Real.sin (4 * Real.pi * v)), hsin4]
      calc -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v))
          = (1 / (2 : ℝ) ^ (2 * k + 1)) * (-Real.sin (4 * Real.pi * v)) := by ring
        _ ≤ (1 / (2 : ℝ) ^ (2 * k + 1)) * (4 * Real.pi * a) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by ring
    have h3 : -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) ≤
        -((1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1)) := by
      have hp : (0 : ℝ) < (3 : ℝ) ^ (2 * k + 1) := by positivity
      have hle : (1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1) ≤
          Real.cos (6 * Real.pi * v) / (3 : ℝ) ^ (2 * k + 1) := by
        rw [div_le_div_iff_of_pos_right hp]
        have hc := cos_lower_quadratic v
        have h2' : (1 : ℝ) - 178 * a ^ 2 = 1 - 178 * v ^ 2 := by rw [ha, sq_abs]
        rw [h2']
        exact hc
      have hstep : -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) =
          -(Real.cos (6 * Real.pi * v) / (3 : ℝ) ^ (2 * k + 1)) := by ring
      rw [hstep]
      exact neg_le_neg hle
    have h4 : 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) ≤
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      have hs : Real.sin (8 * Real.pi * v) ≤ 8 * Real.pi * a := le_trans (le_abs_self _) hsin8
      calc 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v)
          ≤ (1 / (4 : ℝ) ^ (2 * k + 1)) * (8 * Real.pi * a) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by ring
    have hcomb : C * a = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) +
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      rw [hCdef]; field_simp
    have hreg : C * a + 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) ≤
        2 * Real.sin (Real.pi * a) ^ 2 + (1 - 178 * a ^ 2) / (3 : ℝ) ^ (2 * k + 1) := by
      rcases le_total a (1 / 32) with hle | hgt
      · exact region_sharp (2 * k + 1) (by omega) a C hCbound hCn ha0 hle
      · exact region_coarse (2 * k + 1) (by omega) a C hCbound hCn hgt hav
    linarith [h2, h3, h4, hcomb, hreg]
  -- lower bound for the first five terms
  have hlower : -(1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5)) ≤ ∑ m ∈ Finset.range 5, F m := by
    rw [hterms]
    have h2 : -((4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1)) ≤
        -(1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)) := by
      have hs : Real.sin (4 * Real.pi * v) ≤ 4 * Real.pi * a := le_trans (le_abs_self _) hsin4
      have hup : 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v) ≤
          (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by
        calc 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)
            ≤ (1 / (2 : ℝ) ^ (2 * k + 1)) * (4 * Real.pi * a) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) := by ring
      exact neg_le_neg hup
    have h3 : -((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) ≤
        -(1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)) := by
      have hc : Real.cos (6 * Real.pi * v) ≤ 1 := Real.cos_le_one _
      have hup : 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v) ≤
          (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) := by
        calc 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)
            ≤ (1 / (3 : ℝ) ^ (2 * k + 1)) * 1 :=
              mul_le_mul_of_nonneg_left hc (by positivity)
          _ = (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) := by ring
      exact neg_le_neg hup
    have h4 : -((8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1)) ≤
        1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) := by
      have hs : -(8 * Real.pi * a) ≤ Real.sin (8 * Real.pi * v) := by
        linarith [neg_abs_le (Real.sin (8 * Real.pi * v)), hsin8]
      calc -((8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1))
          = (1 / (4 : ℝ) ^ (2 * k + 1)) * (-(8 * Real.pi * a)) := by ring
        _ ≤ (1 / (4 : ℝ) ^ (2 * k + 1)) * Real.sin (8 * Real.pi * v) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
    have hcomb : C * a = (4 * Real.pi * a) / (2 : ℝ) ^ (2 * k + 1) +
        (8 * Real.pi * a) / (4 : ℝ) ^ (2 * k + 1) := by
      rw [hCdef]; field_simp
    have hCsmall : C * a ≤ 0.12 := by
      have h1 : C ≤ 0.42 := by
        refine hCbound.trans ?_
        have hp2 : (32 : ℝ) ≤ (2 : ℝ) ^ (2 * k + 1) := by
          have h' : (2 : ℝ) ^ 5 ≤ (2 : ℝ) ^ (2 * k + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2 : (2 : ℝ) ^ 5 = 32 := by norm_num
          linarith [h2 ▸ h']
        have h2 : 13.39 / (2 : ℝ) ^ (2 * k + 1) ≤ 13.39 / 32 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
        linarith
      nlinarith
    have hpos3 : (0 : ℝ) < 1 / (3 : ℝ) ^ (2 * k + 1) := by positivity
    have htau : 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) ≤ 0.001 := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ (2 * k + 1 - 5) := one_le_pow₀ (by norm_num)
      nlinarith
    have hA : -(4 * Real.pi * a / (2 : ℝ) ^ (2 * k + 1)) - ((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) -
        (8 * Real.pi * a / (4 : ℝ) ^ (2 * k + 1)) ≤
        Real.cos (2 * Real.pi * v) - 1 / (2 : ℝ) ^ (2 * k + 1) * Real.sin (4 * Real.pi * v)
          - 1 / (3 : ℝ) ^ (2 * k + 1) * Real.cos (6 * Real.pi * v)
          + 1 / (4 : ℝ) ^ (2 * k + 1) * Real.sin (8 * Real.pi * v) := by
      linarith [h2, h3, h4, hcos_nonneg]
    have hB : -(0.12) - ((1 : ℝ) / 243) ≤
        -(4 * Real.pi * a / (2 : ℝ) ^ (2 * k + 1)) - ((1 : ℝ) / (3 : ℝ) ^ (2 * k + 1)) -
          (8 * Real.pi * a / (4 : ℝ) ^ (2 * k + 1)) := by
      have h1 : (1 : ℝ) / (3 : ℝ) ^ (2 * k + 1) ≤ 1 / 243 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have h' : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ (2 * k + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (3 : ℝ) ^ 5 = 243 := by norm_num
        linarith [h2 ▸ h']
      linarith [hcomb, hCsmall, h1]
    have hC'' : -(1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5)) ≤ -(0.12) - ((1 : ℝ) / 243) := by
      linarith [htau]
    linarith [hA, hB, hC'']
  -- assemble
  have hAB : |∑' m : ℕ, F m| ≤ 1 := by
    rw [← hsplit]
    have h1 : |∑ m ∈ Finset.range 5, F m + ∑' i : ℕ, F (i + 5)| ≤
        |∑ m ∈ Finset.range 5, F m| + |∑' i : ℕ, F (i + 5)| := abs_add_le _ _
    have h2 : |∑ m ∈ Finset.range 5, F m| ≤ 1 - 0.001 / (5 : ℝ) ^ (2 * k + 1 - 5) := by
      rw [abs_le]
      exact ⟨hlower, hupper⟩
    linarith [h1, h2, htail]
  exact hAB

set_option maxHeartbeats 1000000 in
/-- The normalized Bernoulli bound of Berndt display 3.7 from the sine series. -/
private theorem bernoulli_odd_half (n : ℕ) (hn : 5 ≤ n) (ho : Odd n) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |bernoulliFun n t / (n.factorial : ℝ)| ≤ 2 / (2 * Real.pi) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
  have hk : k ≠ 0 := by omega
  have hS := hasSum_one_div_nat_pow_mul_sin (k := k) hk (x := t) ⟨h0, by linarith⟩
  have hT : |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)| ≤ 1 :=
    abs_tsum_sin_le_one (2 * k + 1) (by omega) ⟨k, rfl⟩ t h0 h1
  have hp : (0 : ℝ) < (2 * Real.pi) ^ (2 * k + 1) := by positivity
  have hf : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcabs : |(-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 /
      ((2 * k + 1).factorial : ℝ)| =
      (2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ)) := by
    have hs : |(-1 : ℝ) ^ (k + 1)| = 1 := by
      rw [abs_pow, show |(-1 : ℝ)| = 1 by norm_num, one_pow]
    rw [abs_div, abs_div, abs_mul, hs, abs_of_pos hp, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos hf, one_mul, div_div]
  have hB : |bernoulliFun (2 * k + 1) t| *
      |(-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k + 1) / 2 / ((2 * k + 1).factorial : ℝ)| =
      |∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * k + 1) * Real.sin (2 * Real.pi * m * t)| := by
    rw [← abs_mul, hS.tsum_eq, mul_comm (bernoulliFun (2 * k + 1) t)]
    rfl
  rw [hcabs] at hB
  -- clear the constant
  have hkey : |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ) ≤ 2 := by
    have h1 : |bernoulliFun (2 * k + 1) t| *
        ((2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ))) ≤ 1 := by
      rw [hB]; exact hT
    calc |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ) =
        2 * (|bernoulliFun (2 * k + 1) t| *
          ((2 * Real.pi) ^ (2 * k + 1) / (2 * ((2 * k + 1).factorial : ℝ)))) := by
          field_simp
      _ ≤ 2 * 1 := by linarith
      _ = 2 := by ring
  rw [abs_div, abs_of_pos hf]
  have hgoal : |bernoulliFun (2 * k + 1) t| ≤
      (2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ) := by
    have hkey2 : |bernoulliFun (2 * k + 1) t| * (2 * Real.pi) ^ (2 * k + 1) ≤
        2 * ((2 * k + 1).factorial : ℝ) := (div_le_iff₀ hf).mp hkey
    have hstep : |bernoulliFun (2 * k + 1) t| ≤
        (2 * ((2 * k + 1).factorial : ℝ)) / (2 * Real.pi) ^ (2 * k + 1) :=
      (le_div_iff₀ hp).mpr hkey2
    calc |bernoulliFun (2 * k + 1) t| ≤ (2 * ((2 * k + 1).factorial : ℝ)) /
            (2 * Real.pi) ^ (2 * k + 1) := hstep
      _ = (2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ) := by ring
  calc |bernoulliFun (2 * k + 1) t| / ((2 * k + 1).factorial : ℝ)
      ≤ ((2 / (2 * Real.pi) ^ (2 * k + 1)) * ((2 * k + 1).factorial : ℝ)) /
          ((2 * k + 1).factorial : ℝ) := div_le_div_of_nonneg_right hgoal hf.le
    _ = 2 / (2 * Real.pi) ^ (2 * k + 1) := by
        field_simp

/-- LEAF. Berndt 1972 page 154 display 3.7, restricted to odd degrees at least three.
Berndt cites Ostrowski 1969 pages 202 to 206 for the constant two.
The degree-one exception is proved in Decomp608a. -/
theorem leaf_periodicBernoulli_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) (x : ℝ) :
    |periodicBernoulli n x| ≤ 2 / (2 * Real.pi) ^ n := by
  by_cases h3 : n = 3
  · subst n
    exact periodicBernoulli_three_bound x
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ho
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact h3 rfl
    have hy0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hy1 : Int.fract x < 1 := Int.fract_lt_one x
    have hper : periodicBernoulli (2 * k + 1) x =
        bernoulliFun (2 * k + 1) (Int.fract x) / ((2 * k + 1).factorial : ℝ) := rfl
    rw [hper]
    rcases le_total (Int.fract x) (1 / 2) with hle | hge
    · exact bernoulli_odd_half (2 * k + 1) (by omega) ⟨k, rfl⟩ _ hy0 hle
    · set y' : ℝ := 1 - Int.fract x with hy'def
      have hy0' : 0 ≤ y' := by rw [hy'def]; linarith
      have hy1' : y' ≤ 1 / 2 := by rw [hy'def]; linarith
      have hsym : bernoulliFun (2 * k + 1) (Int.fract x) = -bernoulliFun (2 * k + 1) y' := by
        have h := bernoulliFun_eval_one_sub (k := 2 * k + 1) (x := y')
        rw [show (1 : ℝ) - y' = Int.fract x by rw [hy'def]; ring] at h
        rw [h]
        have hodd : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, pow_mul]
          norm_num
        rw [hodd]
        ring
      rw [hsym, neg_div, abs_neg]
      exact bernoulli_odd_half (2 * k + 1) (by omega) ⟨k, rfl⟩ _ hy0' hy1'

/-- Berndt 1972 page 154 display 3.6.
The logarithmic derivative formula is supplied by the polynomial proof. -/
theorem kernel_derivative_majorant (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 1 ≤ x) :
    |iteratedDeriv n (berndtKernel n) x| ≤ logDerivativeMajorant n x := by
  rw [leaf_log_power_derivative n hn x hx]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), |(-1 : ℝ) ^ j *
        ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
        (Real.log x ^ j / x ^ (n + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ logDerivativeMajorant n x := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      calc
        _ = ((Nat.stirlingFirst (n + 1) (n + 1 - j) : ℝ) / j.factorial) *
            (Real.log x ^ j / x ^ (n + 1)) := by
          simp [abs_mul, abs_div, abs_pow, abs_of_nonneg hl,
            abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)]
        _ ≤ (n.choose j : ℝ) ^ 2 * (Real.log x ^ j / x ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right (Decomp608a.stirling_coefficient_le_choose_sq n j hjn)
            (by positivity)

/-- Berndt 1972 page 153, the exact first derivative of the degree-one kernel. -/
theorem kernel_one_derivative (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 1 (berndtKernel 1) x = (1 - Real.log x) / x ^ 2 := by
  have heq : berndtKernel 1 = fun y : ℝ => Real.log y / y := by
    funext y
    simp [berndtKernel]
  rw [heq, iteratedDeriv_one]
  have h := ((Real.hasDerivAt_log hx.ne').div (hasDerivAt_id x) hx.ne').deriv
  change deriv (Real.log / id) x = _
  rw [h]
  simp only [id_eq, mul_one, inv_mul_cancel₀ hx.ne']

/-- Berndt 1972 page 154, integral comparison after displays 3.6 and 3.7.
CONDITIONAL ON the Laurent integral leaf. -/
theorem laurentCoeff_norm_le_of_periodic_bound (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ x : ℝ, |periodicBernoulli n x| ≤ C / (2 * Real.pi) ^ n) :
    ‖laurentCoeff n‖ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
  rw [leaf_laurent_integral n hn, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hi := (logDerivativeMajorant_integrable n hn).const_mul (C / (2 * Real.pi) ^ n)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, C / (2 * Real.pi) ^ n * logDerivativeMajorant n x := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hP x) (kernel_derivative_majorant n hn x hx.le)
        (abs_nonneg _) (div_nonneg hC (by positivity))
    _ ≤ C / ((n : ℝ) * Real.pi ^ n) := by
      rw [integral_const_mul]
      exact scaled_integral_logDerivativeMajorant_le n hn C hC

/-- Berndt 1972 page 153 display 3.1, a separate proof for degree one.
CONDITIONAL ON the Laurent integral leaf only. It avoids display 3.7 at degree one. -/
theorem laurentCoeff_one_bound : ‖laurentCoeff 1‖ ≤ (5 / 8 : ℝ) := by
  rw [leaf_laurent_integral 1 (by decide), norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have heq : (∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * iteratedDeriv 1 (berndtKernel 1) x) =
      ∫ x : ℝ in Ioi 1, periodicBernoulli 1 x * ((1 - Real.log x) / x ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [kernel_one_derivative x (lt_trans zero_lt_one hx)]
  rw [heq]
  exact degree_one_remainder_bound _ (fun x _ => periodicBernoulli_one_bound x)

/-- Berndt 1972 Theorem 2, with the exact sealed target statement.
CONDITIONAL ON the Laurent integral and odd Bernoulli leaves. The constant coefficient is reused. -/
theorem laurent_coefficient_bounds :
    ‖laurentCoeff 0‖ ≤ (0.578 : ℝ) ∧
      ∀ n : ℕ, 1 ≤ n → ‖laurentCoeff n‖ ≤
        (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n) := by
  refine ⟨Decomp358f.laurentCoeff_zero_bound, ?_⟩
  intro n hn
  by_cases h1 : n = 1
  · subst n
    norm_num
    apply laurentCoeff_one_bound.trans
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d2]
  · by_cases he : Even n
    · rw [if_pos he]
      exact laurentCoeff_norm_le_of_periodic_bound n hn 4 (by norm_num)
        (periodicBernoulli_uniform_bound n hn)
    · rw [if_neg he]
      have ho : Odd n := (Nat.even_or_odd n).resolve_left he
      have hn3 : 3 ≤ n := by
        have h2 : n ≠ 2 := by
          rintro rfl
          norm_num at he
        omega
      exact laurentCoeff_norm_le_of_periodic_bound n hn 2 (by norm_num)
        (leaf_periodicBernoulli_odd n hn3 ho)

end LeanLab.ChirreHagen2025.Decomp608d
