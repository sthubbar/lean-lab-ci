/-
Split of theorem leaf_schur_kernel_comparison561 in
LeanLab.BHP1997.SPLIT_leaf_kernel_schur561: display 2.10 of page 8, the
Schur comparison for the weighted minor arc kernel. What is split here is the
pointwise two term geometric mean step on the four moduli, the change of
variable that makes the two crossed terms equal, the integral comparison that
follows from them, the restriction of the complete long energy to the minor
arc, and the pass that carries the pointwise short fibre bound through the
outer integral. The constant one is exhibited, so no optimization is left.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_kernel_schur561

set_option autoImplicit false

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- The kernel majorant is nonnegative once its height is. -/
private lemma kw561e_nonneg {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    0 ≤ kernelWeight561 H t := by
  unfold kernelWeight561
  split_ifs with h
  · exact hH
  · exact le_min hH (by positivity)

/-- The kernel majorant is bounded by its height. -/
private lemma kw561e_le {H : ℝ} (hH : 0 ≤ H) (t : ℝ) : kernelWeight561 H t ≤ H := by
  unfold kernelWeight561
  split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

/-- The kernel majorant never exceeds the absolute value of its height. -/
private lemma kw561e_abs_le (H t : ℝ) : |kernelWeight561 H t| ≤ |H| := by
  unfold kernelWeight561
  split_ifs with h
  · exact le_rfl
  · refine abs_le.mpr ⟨le_min (neg_abs_le H)
      ((neg_nonpos.mpr (abs_nonneg H)).trans (by positivity)),
      (min_le_left _ _).trans (le_abs_self H)⟩

/-- The kernel majorant is even in its second argument. -/
private lemma kw561e_sub_comm (H t s : ℝ) :
    kernelWeight561 H (t - s) = kernelWeight561 H (s - t) := by
  unfold kernelWeight561
  have h : ((2 * (t - s) : ℝ) : AddCircle (1 : ℝ)) =
      -((2 * (s - t) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [show 2 * (t - s) = -(2 * (s - t)) by ring, AddCircle.coe_neg]
  rw [h, norm_neg]

/-- The periodic kernel majorant is measurable. -/
private lemma kw561e_measurable (H : ℝ) : Measurable fun u : ℝ => kernelWeight561 H u := by
  have hc : Measurable fun u : ℝ => ‖((2 * u : ℝ) : AddCircle (1 : ℝ))‖ := by
    fun_prop
  unfold kernelWeight561
  exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
    measurable_const (measurable_const.min (measurable_const.div hc))

/-- The finite polynomial is continuous in the additive variable. -/
private lemma kw561e_continuous_polynomial512 (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous fun t : ℝ => polynomial512 S a t := by
  unfold polynomial512
  exact continuous_finsetSum _ fun k _ =>
    ((fourier (k : ℤ)).continuous.comp (by fun_prop)).const_mul (a k)

/-- A finite polynomial is bounded by the sum of the coefficient moduli. -/
private lemma kw561e_polynomial_bound (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖polynomial512 s c t‖ ≤ ∑ n ∈ s, ‖c n‖ := by
  unfold polynomial512
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The period is a bounded interval. -/
private lemma kw561e_period_subset (ε x : ℝ) :
    period512 ε x ⊆ Icc (1 / (order512 ε x : ℝ)) (1 + 1 / (order512 ε x : ℝ)) :=
  fun t ht => ⟨ht.1.le, ht.2⟩

/-- LEAF. The pointwise two term geometric mean step. For four nonnegative
reals the product of all four is at most the average of the two crossed
squares, which is the inequality between the geometric and the arithmetic mean
applied to the two products. No integral, no set and no constant appears. -/
theorem leaf_four_moduli_amgm561 (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    p * q * r * s ≤ (p ^ 2 * s ^ 2 + q ^ 2 * r ^ 2) / 2 := by
  nlinarith only [sq_nonneg (p * s - q * r)]


/-- LEAF. The change of variable in the crossed term. The kernel weight is
unchanged when the sign of its argument flips, so exchanging the two names of
integration turns the term with the short power of the outer variable into the
term with the short power of the inner variable. This is an identity for the
double integral over the symmetric product of the minor arc with itself. -/
theorem leaf_kernel_double_integral_transpose561 (ε D x : ℝ) (a b : ℕ → ℂ) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 *
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 *
            kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) =
      (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 *
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
            kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) := by
  sorry

/-- LEAF. The integral comparison. Integrating the pointwise geometric mean
step and using the change of variable of the crossed term leaves a single
double integral of the squared long modulus against the squared short modulus
and the kernel. Only nonnegativity and monotonicity of the set integral are
used; the weighted short energy bound is not a hypothesis here. -/
theorem leaf_schur_double_integral_le561 (ε D x : ℝ) (a b : ℕ → ℂ) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) ≤
      (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) := by
  by_cases hx : 0 ≤ x
  · have hH0 : 0 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
      Real.rpow_nonneg hx _
    let H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    let m : Set ℝ := minor512 ε D x
    let μ : Measure ℝ := volume.restrict m
    let sa := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊
    let sb := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
    let A : ℝ → ℝ := fun t => ‖polynomial512 sa a t‖
    let B : ℝ → ℝ := fun t => ‖polynomial512 sb b t‖
    let F : ℝ → ℝ → ℝ := fun t s => A t ^ 2 * B s ^ 2 * kernelWeight561 H (t - s)
    let Q : ℝ → ℝ → ℝ := fun t s => A t * A s * B t * B s * kernelWeight561 H (t - s)
    have hAc : Continuous A := (kw561e_continuous_polynomial512 sa a).norm
    have hBc : Continuous B := (kw561e_continuous_polynomial512 sb b).norm
    have hA0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
    have hB0 (t : ℝ) : 0 ≤ B t := norm_nonneg _
    have hmp : m ⊆ period512 ε x := fun t ht => ht.1
    have hpc := kw561e_period_subset ε x
    have hpfin : volume (period512 ε x) < ⊤ :=
      (measure_mono hpc).trans_lt isCompact_Icc.measure_lt_top
    haveI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.2 ((measure_mono hmp).trans_lt hpfin).ne
    let aa : ℝ := ∑ n ∈ sa, ‖a n‖
    let bb : ℝ := ∑ n ∈ sb, ‖b n‖
    have haa0 : 0 ≤ aa := Finset.sum_nonneg fun n hn => norm_nonneg _
    have hbb0 : 0 ≤ bb := Finset.sum_nonneg fun n hn => norm_nonneg _
    have hF0 (t s : ℝ) : 0 ≤ F t s :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (kw561e_nonneg hH0 _)
    have hQ0 (t s : ℝ) : 0 ≤ Q t s := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hA0 _) (hA0 _))
        (hB0 _)) (hB0 _)) (kw561e_nonneg hH0 _)
    have hFm : Measurable (Function.uncurry F) := by
      exact (((hAc.measurable.comp measurable_fst).pow_const 2).mul
        ((hBc.measurable.comp measurable_snd).pow_const 2)).mul
        ((kw561e_measurable H).comp (measurable_fst.sub measurable_snd))
    have hFi : Integrable (Function.uncurry F) (μ.prod μ) := by
      refine Integrable.of_bound hFm.aestronglyMeasurable (aa ^ 2 * bb ^ 2 * H) ?_
      filter_upwards [] with p
      change ‖F p.1 p.2‖ ≤ aa ^ 2 * bb ^ 2 * H
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 p.1 p.2)]
      apply mul_le_mul
      · exact mul_le_mul
          (pow_le_pow_left₀ (hA0 _) (kw561e_polynomial_bound sa a p.1) 2)
          (pow_le_pow_left₀ (hB0 _) (kw561e_polynomial_bound sb b p.2) 2)
          (sq_nonneg _) (sq_nonneg _)
      · exact kw561e_le hH0 _
      · exact kw561e_nonneg hH0 _
      · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hYoung (t s : ℝ) : Q t s ≤ (1 / 2 : ℝ) * (F t s + F s t) := by
      have h := leaf_four_moduli_amgm561 (A t) (A s) (B t) (B s)
        (hA0 t) (hA0 s) (hB0 t) (hB0 s)
      calc Q t s = (A t * A s * B t * B s) * kernelWeight561 H (t - s) := by
            dsimp [Q]
        _ ≤ ((A t ^ 2 * B s ^ 2 + A s ^ 2 * B t ^ 2) / 2) *
              kernelWeight561 H (t - s) :=
            mul_le_mul_of_nonneg_right h (kw561e_nonneg hH0 _)
        _ = (1 / 2 : ℝ) * (F t s + F s t) := by
            dsimp [F]
            rw [kw561e_sub_comm H s t]
            ring
    have hLi : Integrable (fun t => ∫ s, F t s ∂μ) μ := hFi.integral_prod_left
    have hRi : Integrable (fun t => ∫ s, F s t ∂μ) μ := hFi.integral_prod_right
    have hfirst : (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤ (∫ t, ∫ s, F t s ∂μ ∂μ) := by
      have hstep : (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤
          ∫ t, (1 / 2 : ℝ) * ((∫ s, F t s ∂μ) + (∫ s, F s t ∂μ)) ∂μ := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => integral_nonneg (hQ0 t))
          ((hLi.add hRi).const_mul (1 / 2))
        filter_upwards [hFi.prod_right_ae, hFi.prod_left_ae] with t ht hs
        change Integrable (fun s => F t s) μ at ht
        change Integrable (fun s => F s t) μ at hs
        have hinner := integral_mono_of_nonneg
          (Filter.Eventually.of_forall (hQ0 t)) ((ht.add hs).const_mul (1 / 2))
          (Filter.Eventually.of_forall (hYoung t))
        change (∫ s, Q t s ∂μ) ≤ (1 / 2 : ℝ) * ((∫ s, F t s ∂μ) + (∫ s, F s t ∂μ))
        change (∫ s, Q t s ∂μ) ≤ ∫ s, (1 / 2 : ℝ) * (F t s + F s t) ∂μ at hinner
        rw [integral_const_mul, integral_add ht hs] at hinner
        exact hinner
      rw [integral_const_mul, integral_add hLi hRi, ← integral_integral_swap hFi] at hstep
      linarith
    change (∫ t, ∫ s, Q t s ∂μ ∂μ) ≤ (∫ t, ∫ s, F t s ∂μ ∂μ)
    exact hfirst
  · have hx0 : x < 0 := not_le.mp hx
    have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have hempty : Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊ = ∅ := by
      rw [hfloor]
      exact Finset.Ioc_eq_empty_of_le (a := ⌊x - 2 * length512 ε x⌋₊) (b := 0) (Nat.zero_le _)
    have hzero : ∀ t : ℝ,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ = 0 := by
      intro t
      rw [hempty]
      simp [polynomial512]
    simp [hzero]


/-- LEAF. The long energy on the minor arc. The minor arc is a subset of the
period, so the long polynomial energy restricted to the minor arc is at most
the complete long energy. This is subset monotonicity for a nonnegative
integrand and carries no kernel, no short polynomial and no constant. -/
theorem leaf_long_energy_minor_le561 (ε D x : ℝ) (a : ℕ → ℂ) :
    (∫ t in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2) ≤
      longEnergy561 ε x a := by
  have hpc := kw561e_period_subset ε x
  have hAi : IntegrableOn
      (fun t : ℝ => ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2)
      (period512 ε x) :=
    (((kw561e_continuous_polynomial512 _ a).norm).pow 2).integrableOn_Icc.mono_set hpc
  exact setIntegral_mono_set hAi (Filter.Eventually.of_forall fun t => by positivity)
    (Filter.Eventually.of_forall fun t ht => ht.1)


/-- LEAF. The pointwise short fibre bound carried through the outer integral.
Fixing the outer variable leaves the short squared modulus against the kernel
inside the given uniform bound, and replacing the inner integral by that bound
factor by factor keeps the nonnegative long squared modulus. The result is the
same double integral dominated by the bound times the long energy on the minor
arc. The uniform bound is a hypothesis, so this step is strictly weaker than
the target. -/
theorem leaf_weighted_short_fibre_le561 (ε D x : ℝ) (a b : ℕ → ℂ) (W : ℝ)
    (hW : 0 ≤ W)
    (hE : ∀ t : ℝ, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W) :
    (∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2 * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s)) ≤
      Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W *
        (∫ t in minor512 ε D x,
          ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ ^ 2) := by
  let H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
  let m : Set ℝ := minor512 ε D x
  let μ : Measure ℝ := volume.restrict m
  let sa := Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊
  let sb := Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊
  let A : ℝ → ℝ := fun t => ‖polynomial512 sa a t‖
  let B : ℝ → ℝ := fun t => ‖polynomial512 sb b t‖
  let C : ℝ := Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W
  let F : ℝ → ℝ → ℝ := fun t s => A t ^ 2 * B s ^ 2 * kernelWeight561 H (t - s)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hAc : Continuous A := (kw561e_continuous_polynomial512 sa a).norm
  have hBc : Continuous B := (kw561e_continuous_polynomial512 sb b).norm
  have hA0 (t : ℝ) : 0 ≤ A t := norm_nonneg _
  have hB0 (t : ℝ) : 0 ≤ B t := norm_nonneg _
  have hmp : m ⊆ period512 ε x := fun t ht => ht.1
  have hpc := kw561e_period_subset ε x
  have hpfin : volume (period512 ε x) < ⊤ :=
    (measure_mono hpc).trans_lt isCompact_Icc.measure_lt_top
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 ((measure_mono hmp).trans_lt hpfin).ne
  let aa : ℝ := ∑ n ∈ sa, ‖a n‖
  let bb : ℝ := ∑ n ∈ sb, ‖b n‖
  have haa0 : 0 ≤ aa := Finset.sum_nonneg fun n hn => norm_nonneg _
  have hbb0 : 0 ≤ bb := Finset.sum_nonneg fun n hn => norm_nonneg _
  have hFm : Measurable (Function.uncurry F) := by
    exact (((hAc.measurable.comp measurable_fst).pow_const 2).mul
      ((hBc.measurable.comp measurable_snd).pow_const 2)).mul
      ((kw561e_measurable H).comp (measurable_fst.sub measurable_snd))
  have hFi : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (aa ^ 2 * bb ^ 2 * |H|) ?_
    filter_upwards [] with p
    change ‖F p.1 p.2‖ ≤ aa ^ 2 * bb ^ 2 * |H|
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (A p.1)),
      abs_of_nonneg (sq_nonneg (B p.2))]
    refine mul_le_mul (mul_le_mul ?_ ?_ (sq_nonneg _) (sq_nonneg _))
      (kw561e_abs_le H (p.1 - p.2)) (abs_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact pow_le_pow_left₀ (hA0 _) (kw561e_polynomial_bound sa a p.1) 2
    · exact pow_le_pow_left₀ (hB0 _) (kw561e_polynomial_bound sb b p.2) 2
  have hLi : Integrable (fun t => ∫ s, F t s ∂μ) μ := hFi.integral_prod_left
  have hAp : IntegrableOn (fun t => A t ^ 2) (period512 ε x) :=
    ((hAc.pow 2).integrableOn_Icc).mono_set hpc
  have hAi : Integrable (fun t => A t ^ 2) μ := hAp.mono_set hmp
  have hstep : (∫ t, ∫ s, F t s ∂μ ∂μ) ≤ ∫ t, A t ^ 2 * C ∂μ := by
    apply integral_mono_ae hLi (hAi.mul_const C)
    filter_upwards [] with t
    have hEt := hE t
    change (∫ s, F t s ∂μ) ≤ A t ^ 2 * C
    dsimp only [F]
    simp_rw [mul_assoc, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hEt (sq_nonneg _)
  have hEq : (∫ t, A t ^ 2 * C ∂μ) = C * (∫ t, A t ^ 2 ∂μ) := by
    rw [integral_mul_const]
    ring
  change (∫ t, ∫ s, F t s ∂μ ∂μ) ≤ C * ∫ t, A t ^ 2 ∂μ
  exact hstep.trans (le_of_eq hEq)


/-- The split assembly: display 2.10 of page 8 with constant one, proved
from the four leaves above and with no direct admission. -/
theorem leaf_schur_kernel_comparison561_split :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε D x : ℝ, ∀ a b : ℕ → ℂ,
      2 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) →
      ∀ W : ℝ, 0 ≤ W →
      (∀ t : ℝ, ∫ s in minor512 ε D x,
          ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ ^ 2 * kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W) →
      ∫ t in minor512 ε D x, ∫ s in minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a t‖ * ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) a s‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ * ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b s‖ *
          kernelWeight561 (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (t - s) ≤
        K * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) *
          Real.sqrt W := by
  refine ⟨1, le_rfl, ?_⟩
  intro ε D x a b hH W hW hE
  have h1 := leaf_schur_double_integral_le561 ε D x a b
  have h2 := leaf_weighted_short_fibre_le561 ε D x a b W hW hE
  have hC0 : 0 ≤ Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left (leaf_long_energy_minor_le561 ε D x a) hC0
  have h4 : Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W * longEnergy561 ε x a
      = 1 * longEnergy561 ε x a * Real.sqrt (shortEnergy561 ε x b) * Real.sqrt W := by
    ring
  exact h1.trans (h2.trans (h3.trans (le_of_eq h4)))

end LeanLab.BHP1997.Decomp561e
