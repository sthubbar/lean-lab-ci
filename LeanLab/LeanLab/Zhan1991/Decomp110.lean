import LeanLab.Zhan1991.Statements
import LeanLab.Zhan1991.Theorems235

/-!
Theorem 1, P0068, pages 269 to 271.
AI wrote the Lean code. Goldbach is open.
The minor reduction is CONDITIONAL on Theorems 2 and 3.
The final assembly also uses the major arc evaluation.
The major arc evaluation on page 271 cites Pan and Pan, reference 2.
-/

namespace LeanLab.Zhan1991

noncomputable section
open scoped BigOperators

/-- The unweighted prime sum used on page 270, with the lab window endpoints. -/
def primeSum110 (N : ℕ) (U α : ℝ) : ℂ :=
  ∑ p ∈ Win N U, ee ((p : ℝ) * α)

/-- The periodic major arcs on page 270, with Q₁ = log N ^ d and Q = U log N ^ -4. -/
def majorArcs110 (N : ℕ) (U d : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧
    ∃ a : ℤ, Int.gcd a q = 1 ∧ |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U}

/-- The real part of the major arc integral on pages 270 and 271. -/
def majorTerm110 (N : ℕ) (U d : ℝ) : ℝ :=
  (∫ α in Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N U d,
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re

/-- The minor arcs, defined as the complement of major arcs in the unit interval. -/
def minorArcs110 (N : ℕ) (U d : ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ majorArcs110 N U d

/-- The real part of the minor arc integral. -/
def minorTerm110 (N : ℕ) (U d : ℝ) : ℝ :=
  (∫ α in minorArcs110 N U d,
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re


open MeasureTheory

 /-- LEAF. The phase e of x has complex norm 1. Page 270, the phase in 3.20 and 3.21. -/
theorem ee_norm110 (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

 /-- LEAF. The phase of x plus y equals the product of the phases. Page 270, expansion in 3.21. -/
theorem ee_add110 (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee, Complex.ofReal_add, mul_add, Complex.exp_add]

 /-- LEAF. The integral of e of k alpha over the unit interval is 1 for integer k = 0 and 0 for every other integer k. Page 270, orthogonality in 3.21. -/
theorem ee_integral_int110 (k : ℤ) : (∫ α in (0 : ℝ)..1, ee ((k : ℝ) * α)) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    simp [ee]
  · have hz : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    have he : ∀ α : ℝ, ee ((k : ℝ) * α) = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (α : ℂ)) := by
      intro α
      simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]
      congr 1
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex hz]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

 /-- LEAF. The prime window exponential sum is continuous in alpha. Page 270, integrals in 3.20 and 3.21. -/
theorem primeSum_continuous110 (N : ℕ) (U : ℝ) : Continuous (primeSum110 N U) := by
  unfold primeSum110 ee
  fun_prop

 /-- LEAF. The periodic major arc set is Lebesgue measurable. Page 270, E1. -/
theorem majorArcs_measurable110 (N : ℕ) (U d : ℝ) : MeasurableSet (majorArcs110 N U d) := by
  have hset : majorArcs110 N U d = ⋃ (q : ℕ) (a : ℤ),
      {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1 ∧
        |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U} := by
    ext α
    simp only [majorArcs110, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1
  · simp only [h.1, h.2.1, h.2.2, true_and]
    exact isClosed_le (by fun_prop) continuous_const |>.measurableSet
  · have hfalse : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1 ∧
        |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U} = ∅ := by
      ext α
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [hfalse]
    exact MeasurableSet.empty



/-- LEAF. Page 270, display 3.21. The count T is the sum over three window primes of the indicator that their sum is N. -/
theorem triple_count110 (N : ℕ) (U : ℝ) : (T N U : ℂ) =
    ∑ p ∈ Win N U, ∑ q ∈ Win N U, ∑ r ∈ Win N U,
      if p + q + r = N then (1 : ℂ) else 0 := by
  classical
  unfold T
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hS : ∀ r ∈ Win N U, 0 < r := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.pos
  by_cases hpq : p + q < N
  · have he : ∀ r : ℕ, p + q + r = N ↔ r = N - p - q := by omega
    simp only [he, Finset.sum_ite_eq', hpq, true_and]
  · have he : ∀ r ∈ Win N U, p + q + r ≠ N := by
      intro r hr
      have := hS r hr
      omega
    simp only [hpq, false_and, ite_false]
    symm
    exact Finset.sum_eq_zero fun r hr => ite_eq_right (he r hr)


/-- LEAF. Page 270, display 3.21. The cubed prime sum times the negative N phase expands into integer frequencies p plus q plus r minus N. -/
theorem primeSum_cube110 (N : ℕ) (U α : ℝ) :
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) =
      ∑ p ∈ Win N U, ∑ q ∈ Win N U, ∑ r ∈ Win N U,
        ee (((p : ℤ) + q + r - N : ℤ) * α) := by
  classical
  simp only [primeSum110, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [← ee_add110, ← ee_add110, ← ee_add110]
  congr 1
  push_cast
  ring


/-- LEAF. Page 270, display 3.21. The full unit interval integral of the cubed prime sum times the negative N phase equals T. -/
theorem triple_orthogonality110 (N : ℕ) (U : ℝ) :
    (∫ α in (0 : ℝ)..1, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) = (T N U : ℂ) := by
  classical
  simp_rw [primeSum_cube110]
  rw [intervalIntegral.integral_finsetSum]
  · rw [triple_count110]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [ee_integral_int110]
        have he : (p : ℤ) + q + r - N = 0 ↔ p + q + r = N := by omega
        simp only [he]
      · intro r hr
        apply Continuous.intervalIntegrable
        unfold ee
        fun_prop
    · intro q hq
      apply Continuous.intervalIntegrable
      unfold ee
      fun_prop
  · intro p hp
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop


/-- Page 270. Conjugation reverses the phase. -/
theorem ee_conj226 (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  rw [ee, ← Complex.exp_conj]
  simp [ee, map_mul, map_ofNat]

/-- Page 270. Orthogonality gives the exact second moment. -/
theorem primeSum_L2_226 (N : ℕ) (U : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) = (Win N U).card := by
  classical
  have hexpand (α : ℝ) : ((‖primeSum110 N U α‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ Win N U, ∑ q ∈ Win N U, ee (((p : ℤ) - q : ℤ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [primeSum110, map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [ee_conj226, ← ee_add110]
    congr 1
    push_cast
    ring
  have hcomplex : (∫ α in (0 : ℝ)..1, ((‖primeSum110 N U α‖ ^ 2 : ℝ) : ℂ)) =
      ((Win N U).card : ℂ) := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum]
    · calc
        _ = ∑ p ∈ Win N U, ∑ q ∈ Win N U,
              if p = q then (1 : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [intervalIntegral.integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro q hq
            rw [ee_integral_int110]
            simp only [sub_eq_zero, Int.natCast_inj]
          · intro q hq
            apply Continuous.intervalIntegrable
            unfold ee
            fun_prop
        _ = _ := by simp
    · intro p hp
      apply Continuous.intervalIntegrable
      unfold ee
      fun_prop
  rw [intervalIntegral.integral_of_le (by norm_num), integral_complex_ofReal] at hcomplex
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact_mod_cast hcomplex

/-- Page 270. The window has at most its real length plus one members. -/
theorem win_card_le226 (N : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ((Win N U).card : ℝ) ≤ 2 * U + 1 := by
  have hc : (Win N U).card ≤ (Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊).card :=
    Finset.card_filter_le _ _
  rw [Nat.card_Icc] at hc
  have hright : 0 ≤ (N : ℝ) / 3 + U := by positivity
  have hf := Nat.floor_le hright
  have he := Nat.le_ceil ((N : ℝ) / 3 - U)
  by_cases h : ⌈(N : ℝ) / 3 - U⌉₊ ≤ ⌊(N : ℝ) / 3 + U⌋₊ + 1
  · have hc' : ((Win N U).card : ℝ) ≤
        (⌊(N : ℝ) / 3 + U⌋₊ : ℝ) + 1 - ⌈(N : ℝ) / 3 - U⌉₊ := by
      have hcR := (Nat.cast_le (α := ℝ)).mpr hc
      rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one] at hcR
      exact hcR
    linarith
  · have hz : (Win N U).card = 0 := by omega
    simp only [hz, Nat.cast_zero]
    linarith

/-- Page 270. Dirichlet approximation in the exact condition 1.2. -/
theorem dirichlet_Cond12_226 (α τ : ℝ) (hτ : 1 ≤ τ) :
    ∃ (a : ℤ) (q : ℕ) (lam : ℝ), Cond12 α τ a q lam := by
  have hfloor : 0 < ⌊τ⌋₊ := by
    exact Nat.floor_pos.mpr hτ
  obtain ⟨r, herr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  refine ⟨r.num, r.den, α - r, ?_⟩
  refine ⟨?_, ?_, ?_, r.pos, ?_⟩
  · rw [← Rat.cast_def]
    ring
  · exact r.reduced
  · calc
      |α - (r : ℝ)| ≤ 1 / (((⌊τ⌋₊ : ℝ) + 1) * r.den) := herr
      _ ≤ 1 / ((r.den : ℝ) * τ) := by
        apply one_div_le_one_div_of_le
        · positivity
        · have ht := Nat.lt_floor_add_one τ
          have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
          nlinarith
  · exact (Nat.cast_le.mpr hden).trans (Nat.floor_le (by linarith))

/-- Page 270. The count bound used in display 3.20 requires U at least one. -/
theorem win_card_three226 (N : ℕ) (U : ℝ) (hU : 1 ≤ U) :
    ((Win N U).card : ℝ) ≤ 3 * U := by
  have h := win_card_le226 N U (by linarith)
  linarith

/-- The unrestricted auxiliary leaf in DecompJ822 is false for negative radii.
This is a question about the lab statement, not the paper. -/
theorem not_win_card_unrestricted226 :
    ¬ ∀ (N : ℕ) (U : ℝ), ((Win N U).card : ℝ) ≤ 3 * U := by
  intro h
  have hbad := h 0 (-1)
  have hn := Nat.cast_nonneg (α := ℝ) (Win 0 (-1)).card
  linarith

/-- Page 270, display 3.21. The minor integral is the count minus the major integral. -/
theorem minor_identity226 (N : ℕ) (U d : ℝ) :
    (T N U : ℝ) - majorTerm110 N U d =
      (∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs110 N U d,
        primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re := by
  have hf : Continuous (fun α => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) := by
    have := primeSum_continuous110 N U
    unfold ee
    fun_prop
  have hsplit := integral_inter_add_sdiff (s := Set.Icc (0 : ℝ) 1) (μ := volume) (majorArcs_measurable110 N U d) hf.integrableOn_Icc
  have hfull := triple_orthogonality110 N U
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at hfull
  rw [hfull] at hsplit
  have hre := congrArg Complex.re hsplit
  simp only [Complex.add_re, Complex.natCast_re] at hre
  unfold majorTerm110
  linarith

/-- Page 270, display 3.20. A pointwise bound times the second moment controls the minor integral. -/
theorem minor_difference_bound226 (N : ℕ) (U d M : ℝ) (hM : 0 ≤ M)
    (hsup : ∀ α ∈ Set.Icc (0 : ℝ) 1 \ majorArcs110 N U d,
      ‖primeSum110 N U α‖ ≤ M) :
    |(T N U : ℝ) - majorTerm110 N U d| ≤ M * ((Win N U).card : ℝ) := by
  let s := Set.Icc (0 : ℝ) 1 \ majorArcs110 N U d
  let f := fun α => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)
  have hsm : MeasurableSet s := measurableSet_Icc.diff (majorArcs_measurable110 N U d)
  have hf : Continuous f := by
    have := primeSum_continuous110 N U
    dsimp [f]
    unfold ee
    fun_prop
  have hg : Continuous (fun α => ‖primeSum110 N U α‖ ^ 2) :=
    (primeSum_continuous110 N U).norm.pow 2
  have hfi : IntegrableOn f s := hf.integrableOn_Icc.mono_set Set.sdiff_subset
  have hgi : IntegrableOn (fun α => ‖primeSum110 N U α‖ ^ 2) s :=
    hg.integrableOn_Icc.mono_set Set.sdiff_subset
  have hb : ∫ α in s, ‖f α‖ ≤ ∫ α in s, M * ‖primeSum110 N U α‖ ^ 2 := by
    apply setIntegral_mono_on hfi.norm (hgi.const_mul M) hsm
    intro α hα
    dsimp [f]
    rw [norm_mul, norm_pow, ee_norm110, mul_one]
    calc
      ‖primeSum110 N U α‖ ^ 3 = ‖primeSum110 N U α‖ * ‖primeSum110 N U α‖ ^ 2 := by ring
      _ ≤ M * ‖primeSum110 N U α‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hsup α hα) (sq_nonneg _)
  have hsub : (∫ α in s, ‖primeSum110 N U α‖ ^ 2) ≤
      ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum110 N U α‖ ^ 2 := by
    apply integral_mono_measure (Measure.restrict_mono Set.sdiff_subset le_rfl)
      (Filter.Eventually.of_forall (fun α => sq_nonneg _)) hg.integrableOn_Icc
  have hL2 : (∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum110 N U α‖ ^ 2) = (Win N U).card := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    exact primeSum_L2_226 N U
  rw [minor_identity226]
  calc
    _ ≤ ‖∫ α in s, f α‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ α in s, ‖f α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in s, M * ‖primeSum110 N U α‖ ^ 2 := hb
    _ = M * ∫ α in s, ‖primeSum110 N U α‖ ^ 2 := integral_const_mul _ _
    _ ≤ M * ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum110 N U α‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsub hM
    _ = _ := by rw [hL2]

/-- LEAF. Page 260, Theorem 2, used at B = 3 on page 269.
Analytic input. This theorem is cited, not proved here. -/
theorem zhan_theorem2_226 : Theorem2 := by
  sorry

/-- LEAF. Page 260, Theorem 3, used at B = 3 on page 269.
This theorem is cited, not proved here. -/
theorem zhan_theorem3_226 : Theorem3 := by
  sorry

/-- Pages 269 and 270. Theorems 2 and 3 supply a common B = 3 estimate.
CONDITIONAL on the two named paper inputs. -/
theorem Sexp_minor_parameters226 (h2 : Theorem2) (h3 : Theorem3) :
    ∃ c1 c2 c3 K N₀ : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 ≤ K ∧
      ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ), N₀ ≤ N →
        (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
        Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
        (Real.log N ^ c2 ≤ q ∨ Real.log N ^ (4 : ℝ) / A ≤ |lam|) →
        ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-3 : ℝ) := by
  obtain ⟨c1, c2, c32, hc1, hc2, hc32, K2, N2, hlarge⟩ := h2 3 (by norm_num)
  obtain ⟨c33, hc33, K3, N3, hsmall⟩ := h3 c1 c2 3 hc1 hc2 (by norm_num)
  refine ⟨c1, c2, max c32 c33, max 0 (max K2 K3),
    max (max N2 N3) (Real.exp 1), hc1, hc2, lt_of_lt_of_le hc32 (le_max_left _ _),
    le_max_left _ _, ?_⟩
  intro N A α lam a q hN hA hAN hcond hor
  have hN2 : N2 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N3 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp (by norm_num)).trans he
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hL0 : 0 ≤ Real.log N := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hL0 _)).trans hA
  have hA2 : (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c32 ≤ A := by
    apply le_trans (mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (3 / 5 : ℝ) ≤ 5 / 8))
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _))
      (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hN0 _)) hA
  have hA3 : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c33 ≤ A := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _))
      (Real.rpow_nonneg hN0 _)).trans hA
  by_cases hq : Real.log N ^ c2 ≤ q
  · apply (hlarge N A α lam a q hN2 hA2 hAN hcond hq).trans
    gcongr
    exact (le_max_left K2 K3).trans (le_max_right 0 _)
  · have hq' : (q : ℝ) ≤ Real.log N ^ c2 := le_of_lt (lt_of_not_ge hq)
    have hlam : Real.log N ^ (3 + 1 : ℝ) / A ≤ |lam| := by
      simpa only [show (3 + 1 : ℝ) = 4 by norm_num] using hor.resolve_left hq
    apply (hsmall N A α lam a q hN3 hA3 hAN hcond hq' hlam).trans
    gcongr
    exact (le_max_right K2 K3).trans (le_max_right 0 _)

/-- Page 270. Freeze the logarithm on one window whose width is at most half its endpoint. -/
theorem log_window_error226 (m x A : ℝ) (hm : 0 < m) (hx : m / 2 ≤ x)
    (hxm : x ≤ m) (hA : m - x ≤ A) :
    |Real.log x - Real.log m| ≤ 2 * A / m := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ Real.log m := Real.log_le_log hx0 hxm
  rw [abs_of_nonpos (sub_nonpos.mpr hlog)]
  have hupper := Real.log_le_sub_one_of_pos (div_pos hm hx0)
  rw [Real.log_div hm.ne' hx0.ne'] at hupper
  have hdiff : m / x - 1 = (m - x) / x := by field_simp
  rw [hdiff] at hupper
  have hA0 : 0 ≤ A := by linarith
  calc
    -(Real.log x - Real.log m) ≤ (m - x) / x := by linarith
    _ ≤ A / x := div_le_div_of_nonneg_right hA hx0.le
    _ ≤ 2 * A / m := by
      apply (div_le_div_iff₀ hx0 hm).mpr
      nlinarith

/-- Page 270. One frozen logarithm compares weighted and unweighted prime phases.
The error uses the full window, not estimates on its subwindows. -/
theorem freeze_log_sum226 (s : Finset ℕ) (m A α : ℝ) (hm : 0 < m)
    (hs : ∀ p ∈ s, m / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ m ∧ m - p ≤ A) :
    ‖(∑ p ∈ s, (Real.log p : ℂ) * ee ((p : ℝ) * α)) -
      (Real.log m : ℂ) * ∑ p ∈ s, ee ((p : ℝ) * α)‖ ≤
      (s.card : ℝ) * (2 * A / m) := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ s, ‖(Real.log p : ℂ) * ee ((p : ℝ) * α) -
        (Real.log m : ℂ) * ee ((p : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ s, 2 * A / m := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← sub_mul, norm_mul, ee_norm110, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      exact log_window_error226 m p A hm (hs p hp).1 (hs p hp).2.1 (hs p hp).2.2
    _ = _ := by simp

open scoped ArithmeticFunction.vonMangoldt

/-- Page 270. Removing prime powers from the weighted sum costs at most psi minus theta. -/
theorem Sexp_prime_error226 (N : ℕ) (A α : ℝ) :
    ‖Sexp α N A - ∑ p ∈ (shortWin N A).filter Nat.Prime,
      (Real.log p : ℂ) * ee ((p : ℝ) * α)‖ ≤
      Chebyshev.psi N - Chebyshev.theta N := by
  classical
  have hprime : (∑ p ∈ (shortWin N A).filter Nat.Prime,
      (Real.log p : ℂ) * ee ((p : ℝ) * α)) =
      ∑ p ∈ (shortWin N A).filter Nat.Prime, (Λ p : ℂ) * ee ((p : ℝ) * α) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [hprime]
  have hsplit := Finset.sum_filter_add_sum_filter_not (shortWin N A) Nat.Prime
    (fun p => (Λ p : ℂ) * ee ((p : ℝ) * α))
  have hid : Sexp α N A - ∑ p ∈ (shortWin N A).filter Nat.Prime,
      (Λ p : ℂ) * ee ((p : ℝ) * α) =
      ∑ p ∈ (shortWin N A).filter (fun p => ¬p.Prime), (Λ p : ℂ) * ee ((p : ℝ) * α) := by
    unfold Sexp
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit.symm)
  rw [hid]
  calc
    _ ≤ ∑ p ∈ (shortWin N A).filter (fun p => ¬p.Prime),
        ‖(Λ p : ℂ) * ee ((p : ℝ) * α)‖ := norm_sum_le _ _
    _ = ∑ p ∈ (shortWin N A).filter (fun p => ¬p.Prime), Λ p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, ee_norm110, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ p ∈ (Finset.Ioc 0 N).filter (fun p => ¬p.Prime), Λ p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hwin := Finset.mem_filter.mp hp'.1
        have hi := Finset.mem_Icc.mp hwin.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hi.2⟩, hp'.2⟩
      · intro p hp hnot
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp

/-- Page 270. A reduced small denominator approximation off the major arcs has large error. -/
theorem off_major_lambda226 (N : ℕ) (U d α lam : ℝ) (a : ℤ) (q : ℕ)
    (hα : α ∉ majorArcs110 N U d) (heq : α = (a : ℝ) / q + lam)
    (hgcd : Int.gcd a q = 1) (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ Real.log N ^ d) :
    Real.log N ^ (4 : ℝ) / U < |lam| := by
  by_contra h
  apply hα
  refine ⟨q, hq1, hq, a, hgcd, ?_⟩
  rw [heq]
  simpa only [add_sub_cancel_left] using le_of_not_gt h

/-- Page 270. A larger cutoff includes every small denominator for the endpoint scale. -/
theorem minor_denominator_dichotomy226 (N M : ℕ) (U A c2 d α lam : ℝ)
    (a : ℤ) (q : ℕ) (hM : Real.exp 1 ≤ (M : ℝ)) (hMN : M ≤ N)
    (hU : 0 < U) (hUA : U ≤ A) (hc2 : 0 < c2) (hcd : c2 ≤ d)
    (hα : α ∉ majorArcs110 N U d) (heq : α = (a : ℝ) / q + lam)
    (hgcd : Int.gcd a q = 1) (hq1 : 1 ≤ q) :
    Real.log M ^ c2 ≤ q ∨ Real.log M ^ (4 : ℝ) / A ≤ |lam| := by
  have hMpos : (0 : ℝ) < M := (Real.exp_pos 1).trans_le hM
  have hNpos : (0 : ℝ) < N := hMpos.trans_le (Nat.cast_le.mpr hMN)
  have hlog : Real.log M ≤ Real.log N := Real.log_le_log hMpos (Nat.cast_le.mpr hMN)
  have hLM : 1 ≤ Real.log M := by simpa using Real.log_le_log (Real.exp_pos 1) hM
  have hLN : 1 ≤ Real.log N := hLM.trans hlog
  by_cases hq : Real.log M ^ c2 ≤ q
  · exact Or.inl hq
  · right
    have hqN : (q : ℝ) ≤ Real.log N ^ d := calc
      _ ≤ Real.log M ^ c2 := le_of_lt (lt_of_not_ge hq)
      _ ≤ Real.log N ^ c2 := Real.rpow_le_rpow (by linarith) hlog hc2.le
      _ ≤ Real.log N ^ d := Real.rpow_le_rpow_of_exponent_le hLN hcd
    have hlarge := off_major_lambda226 N U d α lam a q hα heq hgcd hq1 hqN
    apply le_trans ?_ hlarge.le
    have hApos : 0 < A := hU.trans_le hUA
    calc
      Real.log M ^ (4 : ℝ) / A ≤ Real.log N ^ (4 : ℝ) / A :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (by linarith) hlog (by norm_num : (0 : ℝ) ≤ 4)) hApos.le
      _ ≤ Real.log N ^ (4 : ℝ) / U :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hU hUA


/-- Pages 269 and 270. Dirichlet approximation forces a case of the B = 3 estimate.
CONDITIONAL on Theorems 2 and 3. The remaining scale assumptions are explicit. -/
theorem Sexp_off_major226 (h2 : Theorem2) (h3 : Theorem3) :
    ∃ c1 c2 c3 K M₀ : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 ≤ K ∧
      ∀ (N M : ℕ) (U A d α : ℝ), M₀ ≤ M → M ≤ N →
        0 < U → U ≤ A → c2 ≤ d →
        (M : ℝ) ^ (5 / 8 : ℝ) * Real.log M ^ c3 ≤ A → A ≤ M →
        1 ≤ A ^ 2 / M * Real.log M ^ (-c1) →
        α ∉ majorArcs110 N U d →
        ‖Sexp α M A‖ ≤ K * A * Real.log M ^ (-3 : ℝ) := by
  obtain ⟨c1, c2, c3, K, M₀, hc1, hc2, hc3, hK, hb⟩ := Sexp_minor_parameters226 h2 h3
  refine ⟨c1, c2, c3, K, max M₀ (Real.exp 1), hc1, hc2, hc3, hK, ?_⟩
  intro N M U A d α hM hMN hU hUA hcd hsize hAM hτ hα
  obtain ⟨a, q, lam, hcond⟩ := dirichlet_Cond12_226 α _ hτ
  apply hb M A α lam a q ((le_max_left _ _).trans hM) hsize hAM hcond
  exact minor_denominator_dichotomy226 N M U A c2 d α lam a q
    ((le_max_right _ _).trans hM) hMN hU hUA hc2 hcd hα
    hcond.1 hcond.2.1 hcond.2.2.2.1

/-- Page 270. An integer endpoint window is a shortWin with the exact integer width. -/
theorem shortWin_integer226 (M l : ℕ) (hl : 1 ≤ l) :
    shortWin M ((M : ℝ) - l + 1) = Finset.Icc l M := by
  classical
  ext n
  simp only [shortWin, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn, hnM⟩, hreal⟩
    have hr : (l : ℝ) < n + 1 := by linarith
    have hi : l < n + 1 := by exact_mod_cast hr
    exact ⟨by omega, hnM⟩
  · rintro ⟨hln, hnM⟩
    refine ⟨⟨hl.trans hln, hnM⟩, ?_⟩
    have hr : (l : ℝ) ≤ n := by exact_mod_cast hln
    linarith

/-- Page 270. The lab prime window is the prime part of one exact shortWin. -/
theorem shortWin_prime_window226 (N : ℕ) (U : ℝ)
    (hl : 1 ≤ ⌈(N : ℝ) / 3 - U⌉₊) :
    (shortWin ⌊(N : ℝ) / 3 + U⌋₊
      ((⌊(N : ℝ) / 3 + U⌋₊ : ℝ) - ⌈(N : ℝ) / 3 - U⌉₊ + 1)).filter Nat.Prime =
      Win N U := by
  rw [shortWin_integer226 _ _ hl]
  rfl

/-- Page 270. The exact shortWin width differs from 2U by less than one. -/
theorem window_width226 (N : ℕ) (U : ℝ) (hU : 0 ≤ U) (hlo : 0 ≤ (N : ℝ) / 3 - U) :
    let A := (⌊(N : ℝ) / 3 + U⌋₊ : ℝ) - ⌈(N : ℝ) / 3 - U⌉₊ + 1
    2 * U - 1 < A ∧ A ≤ 2 * U + 1 := by
  dsimp
  have hhi : 0 ≤ (N : ℝ) / 3 + U := by positivity
  have hf := Nat.floor_le hhi
  have hf' := Nat.lt_floor_add_one ((N : ℝ) / 3 + U)
  have hc := Nat.le_ceil ((N : ℝ) / 3 - U)
  have hc' := Nat.ceil_lt_add_one hlo
  constructor <;> linarith

/-- Page 270. The frozen logarithm and prime power removal give an explicit prime sum bound. -/
theorem primeSum_weighted_bound226 (N M : ℕ) (U A α : ℝ) (hM : 1 < (M : ℝ))
    (hA : A ≤ (M : ℝ) / 2)
    (hwin : (shortWin M A).filter Nat.Prime = Win N U) :
    ‖primeSum110 N U α‖ ≤
      (‖Sexp α M A‖ + (Chebyshev.psi M - Chebyshev.theta M) +
        ((Win N U).card : ℝ) * (2 * A / M)) / Real.log M := by
  classical
  have hM0 : (0 : ℝ) < M := by linarith
  let W := ∑ p ∈ Win N U, (Real.log p : ℂ) * ee ((p : ℝ) * α)
  have hpowers : ‖Sexp α M A - W‖ ≤ Chebyshev.psi M - Chebyshev.theta M := by
    simpa only [hwin] using Sexp_prime_error226 M A α
  have hfreeze : ‖W - (Real.log M : ℂ) * primeSum110 N U α‖ ≤
      ((Win N U).card : ℝ) * (2 * A / M) := by
    apply freeze_log_sum226 (Win N U) M A α hM0
    intro p hp
    rw [← hwin] at hp
    have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
    have hpM : (p : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hmem.1).2
    exact ⟨by linarith [hmem.2], hpM, by linarith [hmem.2]⟩
  have htriangle : ‖(Real.log M : ℂ) * primeSum110 N U α‖ ≤
      ‖Sexp α M A‖ + ‖Sexp α M A - W‖ +
        ‖W - (Real.log M : ℂ) * primeSum110 N U α‖ := by
    calc
      _ = ‖Sexp α M A - (Sexp α M A - W) -
          (W - (Real.log M : ℂ) * primeSum110 N U α)‖ := by congr 1; ring
      _ ≤ ‖Sexp α M A - (Sexp α M A - W)‖ +
          ‖W - (Real.log M : ℂ) * primeSum110 N U α‖ := norm_sub_le _ _
      _ ≤ ‖Sexp α M A‖ + ‖Sexp α M A - W‖ +
          ‖W - (Real.log M : ℂ) * primeSum110 N U α‖ :=
        by linarith [norm_sub_le (Sexp α M A) (Sexp α M A - W)]
  have hL : 0 < Real.log M := Real.log_pos hM
  have hnorm : ‖(Real.log M : ℂ) * primeSum110 N U α‖ =
      Real.log M * ‖primeSum110 N U α‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  apply (le_div_iff₀ hL).mpr
  rw [mul_comm, ← hnorm]
  linarith

open Filter Asymptotics

/-- Page 270. The integer endpoint stays between N divided by four and N divided by two. -/
theorem endpoint_bounds226 (N : ℕ) (U : ℝ) (hN : (24 : ℝ) ≤ N)
    (hU : 1 ≤ U) (hsmall : 24 * U ≤ N) :
    (N : ℝ) / 4 ≤ (⌊(N : ℝ) / 3 + U⌋₊ : ℝ) ∧
      (⌊(N : ℝ) / 3 + U⌋₊ : ℝ) ≤ (N : ℝ) / 2 ∧
      1 ≤ ⌈(N : ℝ) / 3 - U⌉₊ := by
  have hhi : 0 ≤ (N : ℝ) / 3 + U := by positivity
  have hf := Nat.floor_le hhi
  have hf' := Nat.lt_floor_add_one ((N : ℝ) / 3 + U)
  have hc := Nat.le_ceil ((N : ℝ) / 3 - U)
  refine ⟨by linarith, by linarith, ?_⟩
  have : (1 : ℝ) ≤ (⌈(N : ℝ) / 3 - U⌉₊ : ℝ) := by linarith
  exact_mod_cast this

/-- Page 270. Logarithms at comparable endpoints differ by at most a factor two. -/
theorem endpoint_log_bounds226 (N M : ℕ) (hN : (16 : ℝ) ≤ N)
    (hlo : (N : ℝ) / 4 ≤ M) (hhi : M ≤ N) :
    Real.log M ≤ Real.log N ∧ Real.log N ≤ 2 * Real.log M := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  refine ⟨Real.log_le_log hM0 (by exact_mod_cast hhi), ?_⟩
  have hsquare : (N : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hlog := Real.log_le_log hN0 hsquare
  rw [Real.log_pow] at hlog
  simpa using hlog

/-- Page 270. Every fixed logarithmic window is eventually narrower than N divided by 24 log cubed N. -/
theorem window_eventually_small226 (c : ℝ) :
    ∃ N₀ : ℝ, ∀ x : ℝ, N₀ ≤ x →
      24 * (x ^ (5 / 8 : ℝ) * Real.log x ^ c) * Real.log x ^ (3 : ℝ) ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop (c + 3)
    (by norm_num : (0 : ℝ) < 3 / 8)).bound (by norm_num : (0 : ℝ) < 1 / 24)
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp h
  refine ⟨max N₀ (Real.exp 1), ?_⟩
  intro x hx
  have hxN : N₀ ≤ x := (le_max_left _ _).trans hx
  have he : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le he
  have hL : 0 < Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) he
    rw [Real.log_exp] at this
    linarith
  have hb := hN x hxN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL.le _), abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx0.le (5 / 8 : ℝ))
  have hpow : x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  rw [Real.rpow_add hL] at hmul
  nlinarith [hpow]

/-- Page 270. A squared window size bound ensures the Dirichlet parameter is at least one. -/
theorem tau_ge_one226 (N M : ℕ) (U A c1 : ℝ) (hM : 1 < (M : ℝ))
    (hMN : M ≤ N) (hc1 : 0 ≤ c1) (hU : 0 ≤ U) (hUA : U ≤ A)
    (hsq : (N : ℝ) * Real.log N ^ c1 ≤ U ^ 2) :
    1 ≤ A ^ 2 / M * Real.log M ^ (-c1) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hLM : 0 < Real.log M := Real.log_pos hM
  have hlog : Real.log M ≤ Real.log N := Real.log_le_log hM0 (Nat.cast_le.mpr hMN)
  have hp : (M : ℝ) * Real.log M ^ c1 ≤ (N : ℝ) * Real.log N ^ c1 := by
    exact mul_le_mul (Nat.cast_le.mpr hMN) (Real.rpow_le_rpow hLM.le hlog hc1)
      (Real.rpow_nonneg hLM.le _) (Nat.cast_nonneg _)
  have hsq' : U ^ 2 ≤ A ^ 2 := by nlinarith
  rw [Real.rpow_neg hLM.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hLM _), one_mul]
  apply (le_div_iff₀ hM0).mpr
  nlinarith

/-- Page 270. The chosen logarithmic exponent supplies the square size bound for tau. -/
theorem window_square_lower226 (x c c1 : ℝ) (hx : 1 ≤ x) (hL : 1 ≤ Real.log x)
    (hc : 0 ≤ c) (hcc : c1 ≤ c) :
    x * Real.log x ^ c1 ≤ (x ^ (5 / 8 : ℝ) * Real.log x ^ c) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ Real.log x := by linarith
  have hn : x ≤ x ^ (5 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 5 / 4)
  have hl : Real.log x ^ c1 ≤ Real.log x ^ (c * 2) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hp := mul_le_mul hn hl (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hx0 (5 / 4 : ℝ))
  have hn2 : (x ^ (5 / 8 : ℝ)) ^ 2 = x ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hl2 : (Real.log x ^ c) ^ 2 = Real.log x ^ (c * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  simpa only [mul_pow, hn2, hl2] using hp

/-- Page 270. Prime powers are absorbed by the window after three logarithms. -/
theorem sqrt_window_lower226 (x c : ℝ) (hx : 1 ≤ x) (hL : 1 ≤ Real.log x) (hc : 3 ≤ c) :
    Real.sqrt x * Real.log x ^ (3 : ℝ) ≤ x ^ (5 / 8 : ℝ) * Real.log x ^ c := by
  rw [Real.sqrt_eq_rpow]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 2 : ℝ) ≤ 5 / 8))
    (Real.rpow_le_rpow_of_exponent_le hL hc)
    (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)

/-- Page 270. Comparable logarithms preserve the inverse cube saving. -/
theorem log_inverse_cube226 (L l : ℝ) (hL : 0 < L) (_hl : 0 < l) (hc : L ≤ 2 * l) :
    l ^ (-3 : ℝ) ≤ 8 * L ^ (-3 : ℝ) := by
  have h := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < L / 2)
    (by linarith : L / 2 ≤ l) (by norm_num : (-3 : ℝ) ≤ 0)
  calc
    l ^ (-3 : ℝ) ≤ (L / 2) ^ (-3 : ℝ) := h
    _ = 8 * L ^ (-3 : ℝ) := by
      rw [Real.div_rpow hL.le (by norm_num)]
      norm_num
      ring

/-- Page 270. The frozen logarithm error is absorbed by a log cubed width condition. -/
theorem freeze_error_scale226 (N M : ℕ) (U A L : ℝ) (hM : 0 < (M : ℝ))
    (hU : 0 ≤ U) (hL : 0 < L) (hc : ((Win N U).card : ℝ) ≤ 3 * U)
    (hA0 : 0 ≤ A) (hA : A ≤ 3 * U) (hMN : (N : ℝ) / 4 ≤ M)
    (hsmall : U * L ^ (3 : ℝ) ≤ N) :
    ((Win N U).card : ℝ) * (2 * A / M) ≤ 72 * U * L ^ (-3 : ℝ) := by
  have hprod : ((Win N U).card : ℝ) * (2 * A) ≤ 18 * U ^ 2 := by
    have := mul_le_mul hc (by linarith : 2 * A ≤ 6 * U) (by linarith : 0 ≤ 2 * A)
      (by linarith : 0 ≤ 3 * U)
    nlinarith
  have hsmall' : U * L ^ 3 ≤ 4 * M := by
    norm_num at hsmall
    linarith
  calc
    _ = (((Win N U).card : ℝ) * (2 * A)) / M := by ring
    _ ≤ (18 * U ^ 2) / M := div_le_div_of_nonneg_right hprod hM.le
    _ ≤ 72 * U / L ^ 3 := by
      apply (div_le_div_iff₀ hM (pow_pos hL 3)).mpr
      have := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 18 * U)
      nlinarith
    _ = _ := by norm_num; ring

/-- Page 270. The weighted minor estimate and the two explicit errors give log power minus four. -/
theorem primeSum_bound_of_scale226 (N M : ℕ) (U A α K C L : ℝ)
    (hM : 1 < (M : ℝ)) (hU : 0 ≤ U) (hL : 0 < L)
    (hlog : L ≤ 2 * Real.log M) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (_hA0 : 0 ≤ A) (hA : A ≤ 3 * U) (hhalf : A ≤ (M : ℝ) / 2)
    (hwin : (shortWin M A).filter Nat.Prime = Win N U)
    (hS : ‖Sexp α M A‖ ≤ K * A * Real.log M ^ (-3 : ℝ))
    (hpowers : Chebyshev.psi M - Chebyshev.theta M ≤ C * Real.sqrt M)
    (hsqrt : Real.sqrt M ≤ U * L ^ (-3 : ℝ))
    (hfreeze : ((Win N U).card : ℝ) * (2 * A / M) ≤ 72 * U * L ^ (-3 : ℝ)) :
    ‖primeSum110 N U α‖ ≤ (48 * K + 2 * C + 144) * U * L ^ (-4 : ℝ) := by
  have hLM : 0 < Real.log M := Real.log_pos hM
  have hL3 : 0 ≤ L ^ (-3 : ℝ) := Real.rpow_nonneg hL.le _
  have hS' : ‖Sexp α M A‖ ≤ 24 * K * U * L ^ (-3 : ℝ) := by
    apply hS.trans
    calc
      K * A * Real.log M ^ (-3 : ℝ) ≤ K * (3 * U) * (8 * L ^ (-3 : ℝ)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hA hK)
          (log_inverse_cube226 L (Real.log M) hL hLM hlog)
          (Real.rpow_nonneg hLM.le _) (by positivity)
      _ = _ := by ring
  have hp' : Chebyshev.psi M - Chebyshev.theta M ≤ C * U * L ^ (-3 : ℝ) := by
    apply hpowers.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsqrt hC
  have hb := primeSum_weighted_bound226 N M U A α hM hhalf hwin
  have hnum : ‖Sexp α M A‖ + (Chebyshev.psi M - Chebyshev.theta M) +
      ((Win N U).card : ℝ) * (2 * A / M) ≤ (24 * K + C + 72) * U * L ^ (-3 : ℝ) := by
    nlinarith
  have hcoef : 0 ≤ (24 * K + C + 72) * U * L ^ (-3 : ℝ) := by positivity
  calc
    _ ≤ (24 * K + C + 72) * U * L ^ (-3 : ℝ) / Real.log M :=
      hb.trans (div_le_div_of_nonneg_right hnum hLM.le)
    _ ≤ (24 * K + C + 72) * U * L ^ (-3 : ℝ) / (L / 2) :=
      div_le_div_of_nonneg_left hcoef (by linarith) (by linarith)
    _ = _ := by
      have h4 : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) / L := by
        rw [show (-4 : ℝ) = -3 - 1 by norm_num, Real.rpow_sub hL, Real.rpow_one]
      rw [h4]
      field_simp
      ring

/-- Page 270. A larger logarithmic exponent gives the short interval size required at the endpoint. -/
theorem endpoint_size_lower226 (N M : ℕ) (c c3 : ℝ) (hM : 1 < (M : ℝ))
    (hMN : M ≤ N) (hL : 1 ≤ Real.log N) (hc3 : 0 ≤ c3) (hcc : c3 ≤ c) :
    (M : ℝ) ^ (5 / 8 : ℝ) * Real.log M ^ c3 ≤
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog : Real.log M ≤ Real.log N := Real.log_le_log hM0 (Nat.cast_le.mpr hMN)
  calc
    _ ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 :=
      mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hMN) (by norm_num))
        (Real.rpow_le_rpow (Real.log_pos hM).le hlog hc3)
        (Real.rpow_nonneg (Real.log_pos hM).le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hcc)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Pages 269 and 270. The minor arc supremum bound follows from Theorems 2 and 3.
CONDITIONAL on the two paper inputs. -/
theorem minor_sup_from_paper226 (h2 : Theorem2) (h3 : Theorem3) (d₀ : ℝ) :
    ∃ d c K N₀ : ℝ, d₀ ≤ d ∧ 0 < c ∧ 0 ≤ K ∧
      ∀ N : ℕ, N₀ ≤ N →
        1 ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c ∧
        ∀ α : ℝ, α ∉ majorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d →
          ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α‖ ≤
            K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) * Real.log N ^ (-4 : ℝ) := by
  obtain ⟨c1, c2, c3, K, M₀, hc1, hc2, hc3, hK, hS⟩ := Sexp_off_major226 h2 h3
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C₀ := max 0 C
  let c := max 3 (max c1 c3)
  have hc : 3 ≤ c := le_max_left _ _
  have hc0 : 0 ≤ c := by linarith
  have hcc1 : c1 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcc3 : c3 ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Ns, hNs⟩ := window_eventually_small226 c
  refine ⟨max d₀ c2, c, 48 * K + 2 * C₀ + 144,
    max Ns (max 24 (max (4 * Real.exp 1) (4 * M₀))),
    le_max_left _ _, by linarith, by dsimp [C₀]; positivity, ?_⟩
  intro N hN
  have hNs' : Ns ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have h24 : (24 : ℝ) ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have h4e : 4 * Real.exp 1 ≤ (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h4M : 4 * M₀ ≤ (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have heN : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_pos (1 : ℝ)]
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) heN
  have hL0 : 0 < Real.log N := by linarith
  let U := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c
  have hU1 : 1 ≤ U :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 (by norm_num)) (Real.one_le_rpow hL1 hc0)
  have hU0 : 0 ≤ U := by linarith
  have hsmall : 24 * U * Real.log N ^ (3 : ℝ) ≤ N := hNs N hNs'
  have hL3 : 1 ≤ Real.log N ^ (3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hsmall' : 24 * U ≤ N := by nlinarith
  let M := ⌊(N : ℝ) / 3 + U⌋₊
  let l := ⌈(N : ℝ) / 3 - U⌉₊
  let A := (M : ℝ) - l + 1
  have hend := endpoint_bounds226 N U h24 hU1 hsmall'
  have hMlo : (N : ℝ) / 4 ≤ M := hend.1
  have hMhi : (M : ℝ) ≤ (N : ℝ) / 2 := hend.2.1
  have hl : 1 ≤ l := hend.2.2
  have hMN : M ≤ N := by exact_mod_cast (show (M : ℝ) ≤ N by linarith)
  have hMexp : Real.exp 1 ≤ (M : ℝ) := by linarith
  have hM1 : 1 < (M : ℝ) := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hMexp
  have hMpos : (0 : ℝ) < M := by linarith
  have hwidth := window_width226 N U hU0 (by linarith : 0 ≤ (N : ℝ) / 3 - U)
  have hUA : U ≤ A := by dsimp [A, M, l]; dsimp at hwidth; linarith
  have hA3 : A ≤ 3 * U := by dsimp [A, M, l]; dsimp at hwidth; linarith
  have hA0 : 0 ≤ A := hU0.trans hUA
  have hhalf : A ≤ (M : ℝ) / 2 := by linarith
  have hwin : (shortWin M A).filter Nat.Prime = Win N U := shortWin_prime_window226 N U hl
  have hsize : (M : ℝ) ^ (5 / 8 : ℝ) * Real.log M ^ c3 ≤ A :=
    (endpoint_size_lower226 N M c c3 hM1 hMN hL1 hc3.le hcc3).trans hUA
  have hAM : A ≤ M := by linarith
  have htau : 1 ≤ A ^ 2 / M * Real.log M ^ (-c1) :=
    tau_ge_one226 N M U A c1 hM1 hMN hc1.le hU0 hUA
      (window_square_lower226 N c c1 hN1 hL1 hc0 hcc1)
  have hMlarge : M₀ ≤ (M : ℝ) := by linarith
  have hlog := endpoint_log_bounds226 N M (by linarith) hMlo hMN
  have hsqr : Real.sqrt M ≤ U * Real.log N ^ (-3 : ℝ) := by
    have hh := sqrt_window_lower226 (N : ℝ) c hN1 hL1 hc
    have hm := Real.sqrt_le_sqrt (Nat.cast_le.mpr hMN : (M : ℝ) ≤ N)
    have hdiv : Real.sqrt N ≤ U / Real.log N ^ 3 := by
      apply (le_div_iff₀ (pow_pos hL0 3)).mpr
      norm_num at hh
      exact hh
    apply hm.trans
    norm_num at hdiv ⊢
    simpa only [div_eq_mul_inv] using hdiv
  have hfreeze : ((Win N U).card : ℝ) * (2 * A / M) ≤
      72 * U * Real.log N ^ (-3 : ℝ) := by
    apply freeze_error_scale226 N M U A (Real.log N) hMpos hU0 hL0
      (win_card_three226 N U hU1) hA0 hA3 hMlo
    nlinarith [Real.rpow_nonneg hL0.le (3 : ℝ)]
  refine ⟨hU1, ?_⟩
  intro α hα
  apply primeSum_bound_of_scale226 N M U A α K C₀ (Real.log N) hM1 hU0 hL0 hlog.2 hK
    (le_max_left _ _) hA0 hA3 hhalf hwin
  · exact hS N M U A (max d₀ c2) α hMlarge hMN (by linarith) hUA
      (le_max_right _ _) hsize hAM htau hα
  · exact (hC M).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  · exact hsqr
  · exact hfreeze

/-- LEAF. Page 269, display 3.20. Supremum bound of the exponential sum on the minor arcs.
The analytic evaluation requires Zhan Theorems 2 and 3 and the zero density theorem. -/
theorem minor_sup110 (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ, 0 ≤ K ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
      ∀ α ∈ minorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d,
        ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α‖
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) * Real.log N ^ (-4 : ℝ) := by
  obtain ⟨d, c, K, N₀, hd, hc, hK, hs⟩ :=
    minor_sup_from_paper226 zhan_theorem2_226 zhan_theorem3_226 d₀
  have _hdpos : 0 < d := hd₀.trans_le hd
  refine ⟨d, c, hd, hc, K, N₀, hK, ?_⟩
  intro N _hodd hN α hα
  exact (hs N hN).2 α hα.2

/-- LEAF. Page 270, L2 integral. Parseval identity for the prime window sum.
The integral of the norm squared equals the cardinality of the window primes. -/
theorem primeSum_L2_110 (N : ℕ) (U : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) = (Win N U).card := by
  exact primeSum_L2_226 N U

/-- LEAF. Integration identity: The triple count minus the major term equals the minor term. -/
theorem minor_integral_identity110 (N : ℕ) (U d : ℝ) :
    |(T N U : ℝ) - majorTerm110 N U d| ≤ |minorTerm110 N U d| := by
  rw [minor_identity226]
  exact le_rfl


/-- The unrestricted auxiliary integral leaf in DecompJ822 is false for a negative bound constant.
This is a question about the lab statement, not the paper. -/
theorem not_minor_integral_unrestricted226 :
    ¬ ∀ (N : ℕ) (U d K : ℝ),
      (∀ α ∈ minorArcs110 N U d,
        ‖primeSum110 N U α‖ ≤ K * U * Real.log N ^ (-4 : ℝ)) →
      |minorTerm110 N U d| ≤
        (K * U * Real.log N ^ (-4 : ℝ)) *
          (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := by
  have hL : 1 ≤ Real.log (9 : ℝ) := by
    have he : Real.exp 1 ≤ (9 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hempty : minorArcs110 9 1 1 = ∅ := by
    ext α
    simp only [minorArcs110, Set.mem_sdiff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false,
      not_and, not_not]
    intro hα
    refine ⟨1, by norm_num, ?_, 0, by norm_num, ?_⟩
    · simpa using hL
    · norm_num
      rw [abs_of_nonneg hα.1]
      exact hα.2.trans (by simpa using Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 4))
  have hcard : ((Win (9 : ℝ) 1).card : ℝ) = 2 := by
    norm_num [Win]
    exact_mod_cast (show ((Finset.Icc 2 4).filter Nat.Prime).card = 2 by decide)
  intro h
  have hb := h 9 1 1 (-1) (by simp [hempty])
  rw [primeSum_L2_110] at hb
  norm_num at hb
  rw [hcard] at hb
  have hp : 0 < Real.log (9 : ℝ) ^ (-4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hn := abs_nonneg (minorTerm110 9 1 1)
  norm_num at hb hp
  have hi := inv_pos.mpr hp
  nlinarith

/-- LEAF. Page 271, the major arc display after 3.21.
The logarithmic cutoff can be made sufficiently large for an error of order U² log N ^ -4.
Source for the unproved analytic evaluation: Pan and Pan, reference 2 of P0068.
The periodic interval and inclusive endpoints must be justified with this leaf. -/
theorem major_evaluation110 :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  sorry

/-- Pages 269 and 270, displays 3.20 and 3.21. The exact minor reduction is conditional only on the two named paper statements. -/
theorem minor_reduction_from_paper226 (h2 : Theorem2) (h3 : Theorem3) (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  obtain ⟨d, c, K, N₀, hd, hc, hK, hs⟩ :=
    minor_sup_from_paper226 h2 h3 d₀
  refine ⟨d, c, hd, hc, 3 * K, max N₀ (Real.exp 1), ?_⟩
  have _hdpos : 0 < d := hd₀.trans_le hd
  intro N _hodd hN
  have hNs := hs N ((le_max_left _ _).trans hN)
  let U := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c
  have hU : 1 ≤ U := hNs.1
  have hU0 : 0 ≤ U := by linarith
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL : 0 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) he
    rw [Real.log_exp] at this
    linarith
  have hbound0 : 0 ≤ K * U * Real.log N ^ (-4 : ℝ) :=
    mul_nonneg (mul_nonneg hK hU0) (Real.rpow_nonneg hL _)
  have hb := minor_difference_bound226 N U d (K * U * Real.log N ^ (-4 : ℝ)) hbound0
    (fun α hα => hNs.2 α hα.2)
  calc
    _ ≤ (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ) := hb
    _ ≤ (K * U * Real.log N ^ (-4 : ℝ)) * (3 * U) :=
      mul_le_mul_of_nonneg_left (win_card_three226 N U hU) hbound0
    _ = _ := by ring


/-- LEAF. Pages 269 and 270, displays 3.20 and 3.21.
Choose the logarithmic window exponent and arc cutoff so the minor contribution
is bounded by U² log N ^ -4. This includes the orthogonality identity for T.
The paper uses Theorems 2 and 3, Dirichlet approximation, and the second moment.
The cutoff d can be increased to meet the major arc threshold. -/
theorem minor_reduction110 (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  exact minor_reduction_from_paper226 zhan_theorem2_226 zhan_theorem3_226 d₀ hd₀


/-- The assembly for minor_reduction110 using the leaves.
Pages 269 and 270, displays 3.20 and 3.21. -/
theorem minor_reduction110_assembly (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  exact minor_reduction110 d₀ hd₀

/-- Theorem 1 with its exact cited Prop, assembled from the leaves.
CONDITIONAL on minor_reduction110 and major_evaluation110. -/
theorem theorem1_decomp110 : Theorem1 := by
  obtain ⟨d₀, hd₀, hmajor⟩ := major_evaluation110
  obtain ⟨d, c, hd, hc, Km, Nm, hminor⟩ := minor_reduction110 d₀ hd₀
  obtain ⟨KM, NM, hM⟩ := hmajor d hd c hc
  refine ⟨c, hc, Km + KM, max Nm NM, ?_⟩
  intro N hN hlarge
  have hm := hminor N hN ((le_max_left _ _).trans hlarge)
  have hM' := hM N hN ((le_max_right _ _).trans hlarge)
  calc
    _ ≤ |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d| +
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hm hM'
    _ = _ := by ring


/-- Page 272. The first elementary rational function increases before alpha = 2. -/
theorem section4_f1_mono226 (a b : ℝ) (hab : a ≤ b) (hb : b < 2) :
    3 / (2 - a) ≤ 3 / (2 - b) := by
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- Page 272. The first rational function has the displayed endpoint value. -/
theorem section4_f1_endpoint226 : 3 / (2 - (3 / 4 : ℝ)) = 12 / 5 := by
  norm_num

/-- Page 272. The second rational function has the displayed endpoint value. -/
theorem section4_f2_endpoint226 (lam : ℝ) :
    ((6 * lam + 2) * (3 / 4 : ℝ) - 4 * lam - 1) /
      ((3 / 4 : ℝ) ^ 2 + 3 / 4 - 1) = 8 / 5 * (1 + lam) := by
  ring

/-- Page 272. The displayed endpoint bounds the second rational function in the needed range. -/
theorem section4_f2_bound226 (a lam : ℝ) (ha : 3 / 4 ≤ a) (_ha1 : a ≤ 1)
    (hl : 1 / 2 ≤ lam) (hl1 : lam ≤ 2 / 3) :
    ((6 * lam + 2) * a - 4 * lam - 1) / (a ^ 2 + a - 1) ≤ 8 / 5 * (1 + lam) := by
  have hden : 0 < a ^ 2 + a - 1 := by nlinarith
  apply (div_le_iff₀ hden).mpr
  have hfirst : 0 ≤ 4 * a - 3 := by linarith
  have hsecond : 0 ≤ (2 * lam + 2) * a - (4 * lam - 1) := by nlinarith
  have hprod := mul_nonneg hfirst hsecond
  nlinarith

/-- Page 272. The second rational function is decreasing on the stated interval. -/
theorem section4_f2_antitone226 (lam : ℝ) (hl : 1 / 2 ≤ lam) (hl1 : lam ≤ 2 / 3) :
    AntitoneOn (fun a : ℝ => ((6 * lam + 2) * a - 4 * lam - 1) / (a ^ 2 + a - 1))
      (Set.Icc (3 / 4 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxden : 0 < x ^ 2 + x - 1 := by nlinarith [hx.1]
  have hyden : 0 < y ^ 2 + y - 1 := by nlinarith [hy.1]
  apply (div_le_div_iff₀ hyden hxden).mpr
  have hbr : 0 ≤ (6 * lam + 2) * x * y - (4 * lam + 1) * (x + y) + 2 * lam + 1 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 6 * lam + 2)
      (mul_nonneg (by linarith [hx.1] : 0 ≤ x - 3 / 4) (by linarith [hy.1] : 0 ≤ y - 3 / 4))
    have hq := mul_nonneg (by linarith : 0 ≤ lam / 2 + 1 / 2)
      (by linarith [hx.1, hy.1] : 0 ≤ x + y - 3 / 2)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hxy) hbr
  nlinarith

/-- Page 272. Better fourth moment exponents give smaller short window exponents. -/
theorem section4_exponent_mono226 (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    (8 * a + 3) / (8 * a + 8) ≤ (8 * b + 3) / (8 * b + 8) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- Page 272. The two substitutions in the final conditional range calculation. -/
theorem section4_exponent_values226 :
    (8 * (2 / 3 : ℝ) + 3) / (8 * (2 / 3 : ℝ) + 8) = 5 / 8 ∧
      (8 * (9 / 16 : ℝ) + 3) / (8 * (9 / 16 : ℝ) + 8) = 3 / 5 := by
  norm_num


/-- Page 260. The triangle inequality gives only the global Chebyshev bound without cancellation. -/
theorem Sexp_trivial_bound226 (N : ℕ) (A α : ℝ) :
    ‖Sexp α N A‖ ≤ (Real.log 4 + 4) * N := by
  have hb : ‖Sexp α N A‖ ≤ Chebyshev.psi N := by
    calc
      _ ≤ ∑ p ∈ shortWin N A, ‖(Λ p : ℂ) * ee ((p : ℝ) * α)‖ := norm_sum_le _ _
      _ = ∑ p ∈ shortWin N A, Λ p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_mul, ee_norm110, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ∑ p ∈ Finset.Ioc 0 N, Λ p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
        · intro p hp hnot
          exact ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by simp [Chebyshev.psi]
  exact hb.trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))

/-- Page 270. A global bound of order N is larger than the needed minor scale.
This records the loss in the elementary triangle estimate. -/
theorem global_bound_loses_minor_scale226 (N U L : ℝ) (hN : 0 < N)
    (hU : 0 ≤ U) (hsmall : 24 * U ≤ N) (hL : 1 ≤ L) :
    U * L ^ (-3 : ℝ) < N := by
  have hp : L ^ (-3 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (-3 : ℝ) ≤ 0)
  have hb := mul_le_mul_of_nonneg_left hp hU
  nlinarith

end
end LeanLab.Zhan1991
