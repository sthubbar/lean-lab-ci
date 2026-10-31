import LeanLab.ChirreHagen2025.Statements

/-!
Further statements from P0075, pages 4, 13 and 14.
These are CITED propositions, with no theorem asserting them.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Additional122

/-- CITED. P0075 Lemma 2.3, pages 4 and 5. -/
def lemma2_3 : Prop := RiemannHypothesis → ∀ T : ℝ, 4 * 10 ^ 13 ≤ T →
  (∫ t in (10 ^ 4 : ℝ)..T,
    ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2)
    ≤ 0.8056 * T

/-- CITED. P0075 Lemma A.1 part 1, pages 13 and 14. -/
def lemmaA1_part1 : Prop :=
  Summable (fun p : Nat.Primes => Real.log (p : ℝ) /
    (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) ∧
  (∑' p : Nat.Primes, Real.log (p : ℝ) /
    (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) < 1.7215

/-- CITED. P0075 Lemma A.1 part 2, pages 13 and 14. -/
def lemmaA1_part2 : Prop :=
  Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt (n + 1) ^ 2 /
    ((n : ℝ) + 1) ^ 2) ∧
  (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) < 0.8053

/-- CITED. P0075 Lemma A.1 part 3, pages 13 and 14. -/
def lemmaA1_part3 : Prop :=
  Summable (fun p : Nat.Primes => Real.log (p : ℝ) ^ 2 /
    ((p : ℝ) ^ 2 - (p : ℝ))) ∧
  (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) < 0.982

/-- CITED. P0075 Lemma A.2, page 14. -/
def lemmaA2 : Prop := RiemannHypothesis → ∀ x : ℝ, 10 ^ 13 ≤ x →
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ)) ≤
    Real.log x ^ 2 / 2 + 4.5222

/-- P0075 Lemma 2.3, page 4: its integrand is integrable on every positive compact interval. -/
theorem logDeriv_sq_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ =>
      ‖deriv riemannZeta (1 + t * Complex.I) / riemannZeta (1 + t * Complex.I)‖ ^ 2)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
  have hs : (1 : ℂ) + t * Complex.I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact ht0 hi
  have harg : ContinuousAt (fun x : ℝ => (1 : ℂ) + x * Complex.I) t := by fun_prop
  have hz : ContinuousAt (fun x : ℝ => riemannZeta (1 + x * Complex.I)) t :=
    ContinuousAt.comp (g := riemannZeta) (f := fun x : ℝ => (1 : ℂ) + x * Complex.I)
      (differentiableAt_riemannZeta hs).continuousAt harg
  have hd : ContinuousAt (fun x : ℝ => deriv riemannZeta (1 + x * Complex.I)) t :=
    ContinuousAt.comp (g := deriv riemannZeta) (f := fun x : ℝ => (1 : ℂ) + x * Complex.I)
      (analyticOn_riemannZeta.deriv.continuousOn.continuousAt
        (isOpen_compl_singleton.mem_nhds hs)) harg
  have hn : riemannZeta ((1 : ℂ) + t * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  exact ((hd.div hz hn).norm.pow 2).continuousWithinAt

/-- P0075 Lemma A.1 part 2, pages 13 and 14: convergence of the series, without its cited bound. -/
theorem mangoldt_sq_summable :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt (n + 1) ^ 2 /
      ((n : ℝ) + 1) ^ 2) := by
  have hseries : LSeriesSummable (LSeries.logMul (LSeries.logMul 1)) 2 :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simp only [LSeries.abscissaOfAbsConv_logMul, LSeries.abscissaOfAbsConv_one]
      change (1 : EReal) < ((2 : ℝ) : EReal)
      exact EReal.coe_lt_coe_iff.mpr (by norm_num))
  have hlog : Summable (fun n : ℕ => Real.log ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    have h := hseries.norm.comp_injective Nat.succ_injective
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [LSeries.norm_term_eq]
    have hln : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hclog : ‖Complex.log ((n : ℂ) + 1)‖ = Real.log ((n : ℝ) + 1) := by
      have hc : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; rfl
      rw [← hc, ← Complex.ofReal_log (by positivity), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hln]
    simp [LSeries.logMul, norm_mul, hclog, Real.rpow_two, pow_two]
  apply hlog.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    have h := ArithmeticFunction.vonMangoldt_le_log (n := n + 1)
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n + 1)
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast at h
    exact pow_le_pow_left₀ h0 h 2

end LeanLab.ChirreHagen2025.Additional122
