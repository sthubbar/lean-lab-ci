/-
Deepening of `leaf_R1_trivial_bound` of `Feed1122LeafEvenMoment`, the trivial bound before
display 33 of Brudern-Perelli 1998, P0082, p. 368: `|R₁(m)| ≤ ∫_0^1 |S(α)|² dα ≪ X log X`.
The Chebyshev half, `Σ_{P<p≤X} (log p)² ≤ 2 X log X`, is proved here from the primorial
bound of Mathlib; the analytic half, `‖R₁(m)‖ ≤ Σ_{P<p≤X} (log p)²`, is proved too, by session S91.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real Finset MeasureTheory

/-- `conj e(x) = e(-x)`. -/
theorem r1p_conj_eC (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

/-- `e(x + y) = e(x) e(y)`. -/
theorem r1p_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Orthogonality: `∫_0^1 e(αk) dα` is `1` at `k = 0` and `0` otherwise. -/
theorem r1p_integral_eC_int (k : ℤ) : ∫ α in (0:ℝ)..1, eC (α * k) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [eC]
  · have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [Complex.I_ne_zero, hpi, this]
    have h := integral_exp_mul_complex (a := 0) (b := 1) hc
    have e : (fun α : ℝ => eC (α * k)) = fun α : ℝ => Complex.exp (2 * Real.pi * Complex.I * k * α) := by
      funext α; unfold eC; congr 1; push_cast; ring
    rw [e, h]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * k * ((1:ℝ):ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one, show (2 * Real.pi * Complex.I * k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

/-- `S(α)` is continuous. -/
theorem r1p_cont_Sp (P X : ℝ) : Continuous (fun α => Sp P X α) := by
  unfold Sp eC; fun_prop

/-- Parseval for `S`, P0082 p. 368 before display 33: `∫_0^1 |S(α)|² dα = Σ_{P<p≤X} (log p)²`. -/
theorem r1p_integral_normSq_Sp (P X : ℝ) :
    ∫ α in Set.Icc (0:ℝ) 1, ‖Sp P X α‖ ^ 2 =
      ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  set T := (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpt : ∀ α : ℝ, ((‖Sp P X α‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ T, ∑ q ∈ T, ((Real.log p * Real.log q : ℝ) : ℂ) * eC (α * ((p : ℤ) - (q : ℤ) : ℤ)) := by
    intro α
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold Sp
    rw [map_sum, sum_mul_sum]
    refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
    rw [map_mul, r1p_conj_eC, Complex.conj_ofReal]
    have : eC (α * ((p : ℤ) - (q : ℤ) : ℤ)) = eC (α * p) * eC (-(α * q)) := by
      rw [← r1p_eC_add]; congr 1; push_cast; ring
    rw [this]; push_cast; ring
  simp_rw [hpt]
  have hint : ∀ (c : ℂ) (k : ℤ), IntervalIntegrable (fun α : ℝ => c * eC (α * k)) volume 0 1 := by
    intro c k
    apply Continuous.intervalIntegrable
    unfold eC; fun_prop
  rw [intervalIntegral.integral_finsetSum (fun p _ => ?_), Complex.ofReal_sum]
  · refine sum_congr rfl (fun p hp => ?_)
    rw [intervalIntegral.integral_finsetSum (fun q _ => hint _ _)]
    simp_rw [intervalIntegral.integral_const_mul, r1p_integral_eC_int, sub_eq_zero, Nat.cast_inj,
      mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq, if_pos hp]; push_cast; ring
  · apply Continuous.intervalIntegrable
    unfold eC; fun_prop

/-- Formerly a MEDIUM LEAF, PROVED by session S91: the first inequality before display 33 of P0082, p. 368, together with Parseval:
`‖R₁(m)‖ ≤ ∫_𝔐 |S(α)|² dα ≤ ∫_0^1 |S(α)|² dα = Σ_{P<p≤X} (log p)²`, the last step by the
orthogonality of `e(αk)` on `[0,1]`, proved by the norm of a set integral, monotonicity in
the set `𝔐 ⊆ [0,1]`, and Parseval for a finite trigonometric sum. -/
theorem leaf_R1_le_sum_log_sq (P X : ℝ) (m : ℤ) :
    ‖R1 P X m‖ ≤ ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  rw [← r1p_integral_normSq_Sp P X]
  have hnorm : ∀ α : ℝ, ‖Sp P X α ^ 2 * eC (-(α * m))‖ = ‖Sp P X α‖ ^ 2 := by
    intro α; rw [norm_mul, norm_pow, norm_eC, mul_one]
  have hc : Continuous (fun α => ‖Sp P X α‖ ^ 2) := (r1p_cont_Sp P X).norm.pow 2
  calc ‖R1 P X m‖ ≤ ∫ α in majorArcs P X ∩ Set.Icc 0 1, ‖Sp P X α ^ 2 * eC (-(α * m))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ α in majorArcs P X ∩ Set.Icc 0 1, ‖Sp P X α‖ ^ 2 := by simp_rw [hnorm]
    _ ≤ ∫ α in Set.Icc (0:ℝ) 1, ‖Sp P X α‖ ^ 2 :=
        setIntegral_mono_set (hc.integrableOn_Icc) (Filter.Eventually.of_forall (fun α => by positivity))
          (Set.inter_subset_right.eventuallyLE)

/-- Chebyshev's bound in the form used before display 33 of P0082: for `X ≥ 2`,
`Σ_{P<p≤X} (log p)² ≤ log X · θ(X) ≤ (log 4) X log X ≤ 2 X log X`. Proved from
`primorial_le_four_pow`. -/
theorem prime_log_sq_sum_le (P X : ℝ) (hX : 2 ≤ X) :
    (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2) ≤ 2 * X * Real.log X := by
  classical
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set n := ⌊X⌋₊ with hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0.le
  have hsub : (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hstep1 : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p ^ 2) ≤
      ∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log X * Real.log p := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hpX : (p : ℝ) ≤ X := le_trans (by exact_mod_cast hp.1.2) hnX
    have : Real.log p ≤ Real.log X := Real.log_le_log (by linarith) hpX
    nlinarith
  have hstep2 : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p) ≤
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
      simp only [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
  have hprim : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p) ≤ n * Real.log 4 := by
    have h1 : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p) =
        Real.log ((primorial n : ℕ) : ℝ) := by
      rw [primorial, Nat.cast_prod, Real.log_prod]
      intro p hp
      simp only [Finset.mem_filter] at hp
      exact_mod_cast hp.2.ne_zero
    rw [h1]
    have h4 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_four_pow n
    have hpos : (0 : ℝ) < ((primorial n : ℕ) : ℝ) := by exact_mod_cast primorial_pos n
    calc Real.log ((primorial n : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hpos h4
      _ = n * Real.log 4 := by rw [Real.log_pow]
  have hlog4 : Real.log 4 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 / 2 by norm_num)
    have h2 : Real.log 4 = Real.log (4/2) + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h3 := Real.log_two_lt_d9
    linarith
  rw [← Finset.mul_sum] at hstep1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ Real.log X * ∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p := hstep1
    _ ≤ Real.log X * (n * Real.log 4) :=
        mul_le_mul_of_nonneg_left (hstep2.trans hprim) hlogX
    _ ≤ Real.log X * (X * 2) := by
        apply mul_le_mul_of_nonneg_left _ hlogX
        exact mul_le_mul hnX hlog4 (Real.log_nonneg (by norm_num)) hX0.le
    _ = 2 * X * Real.log X := by ring

/-- `leaf_R1_trivial_bound` of `Feed1122LeafEvenMoment`, statement unchanged, from the
leaf `leaf_R1_le_sum_log_sq` and the proved Chebyshev bound. -/
theorem leaf_R1_trivial_bound_of_leaves (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖R1 P X m‖ ≤ 2 * X * Real.log X :=
  (leaf_R1_le_sum_log_sq P X m).trans (prime_log_sq_sum_le P X hX)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.prime_log_sq_sum_le
#print axioms LeanLab.ExceptionalSet.U1539.leaf_R1_trivial_bound_of_leaves
#print axioms LeanLab.ExceptionalSet.U1539.r1p_integral_normSq_Sp
#print axioms LeanLab.ExceptionalSet.U1539.leaf_R1_le_sum_log_sq
