/- AI wrote this Lean code for CODEX task169.
Lemma 7 with display 6, journal pp. 1219 to 1222. Goldbach is open. -/
import LeanLab.BS2022GRH.Lemma6Input138
import LeanLab.BS2022GRH.PortedMertens
import LeanLab.BS2022GRH.ThetaMertens224
import LeanLab.BS2022GRH.ThetaInputs224
import LeanLab.BS2022GRH.LowerMertens224
import LeanLab.BS2022GRH.FiniteMertens224

namespace LeanLab.BS2022GRH.DecompC169c
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The common prime Mertens constant M in Lemma 6, p. 1219 display 3.
The convergent prime series is the standard Meissel and Mertens constant. -/
def mertensConstant : ℝ := eulerMascheroniConstant +
  ∑' p : {p : ℕ // p.Prime}, (log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))

/-- The qualitative limit uses the exact common constant of display 3. -/
theorem reciprocal_limit : Filter.Tendsto (fun x : ℝ =>
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x))
    Filter.atTop (nhds mertensConstant) := by
  exact PortedMertens.solution

/-- The integral-defined port constant equals the sealed prime series constant. -/
theorem ported_constant_eq : PortedMertens.Mertens.M = mertensConstant := by
  rw [PortedMertens.Mertens.M.eq, PortedMertens.Mertens.γ.eq_eulerMascheroni]
  unfold mertensConstant
  congr 1
  exact (PortedMertens.Mertens.tsum_primes_eq_tsum_ite
    (fun n : ℕ => log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))).symm

/-- The port gives an unconditional coarse bound with the same common constant. -/
theorem reciprocal_error_le_twelve (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x) - mertensConstant| ≤
      12 / log x := by
  have hfin : Nat.primesLE ⌊x⌋₊ = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    rw [Nat.primesLE_eq_filter_Icc_one]
    rfl
  have he : |(∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x) - mertensConstant| ≤
      (log 4 + 6 + PortedMertens.Mertens.E₁) / log x := by
    simpa only [hfin, PortedMertens.Mertens.E₂p, ported_constant_eq] using
      PortedMertens.Mertens.E₂p.abs_le hx
  have hc : log 4 + 6 + PortedMertens.Mertens.E₁ ≤ 12 := by
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
      norm_num
    rw [h4]
    linarith [PortedMertens.Mertens.E₁.le, log_two_lt_d9]
  exact he.trans (div_le_div_of_nonneg_right hc (le_of_lt (log_pos (by linarith))))

/-- The coarse 12 over log bound cannot provide the journal upper error. -/
theorem coarse_error_exceeds_journal (x : ℝ) (hx : 1 < x) :
    (2.28975e-9 : ℝ) / log x < 12 / log x := by
  exact (div_lt_div_iff_of_pos_right (log_pos hx)).mpr (by norm_num)

/-- Inclusive and strict reciprocal sums differ by at most the endpoint mass. -/
theorem reciprocal_endpoint_gap (x : ℝ) (hx : 2 ≤ x) :
    0 ≤ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) ∧
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) ≤ 1 / x := by
  by_cases hi : (⌊x⌋₊ : ℝ) = x
  · rw [← hi, Nat.floor_natCast, Nat.ceil_natCast]
    change 0 ≤ (∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌊x⌋₊, (1 : ℝ) / p) ∧
      (∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌊x⌋₊, (1 : ℝ) / p) ≤ 1 / (⌊x⌋₊ : ℝ)
    rw [Nat.primesBelow_succ]
    by_cases hp : (⌊x⌋₊).Prime
    · simp [hp, Nat.mem_primesBelow]
    · simp [hp]
  · have hceil : ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
      apply le_antisymm (Nat.ceil_le_floor_add_one x)
      have hf : ⌊x⌋₊ < ⌈x⌉₊ := by
        by_contra hh
        have heq : ⌊x⌋₊ = ⌈x⌉₊ := le_antisymm (Nat.floor_le_ceil x) (le_of_not_gt hh)
        apply hi
        have h1 := Nat.floor_le (by linarith : 0 ≤ x)
        have h2 := Nat.le_ceil x
        rw [← heq] at h2
        exact le_antisymm h1 h2
      omega
    rw [hceil]
    change 0 ≤ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ∧
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤ 1 / x
    simp only [sub_self, le_refl, true_and]
    positivity

/-- The endpoint mass vanishes at infinity. -/
theorem reciprocal_endpoint_gap_limit : Filter.Tendsto (fun x : ℝ =>
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p)) Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  apply squeeze_zero' _ _ hzero
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    exact (reciprocal_endpoint_gap x hx).1
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    exact (reciprocal_endpoint_gap x hx).2

/-- The strict endpoint convention has the same common Mertens limit. -/
theorem reciprocal_strict_limit : Filter.Tendsto (fun x : ℝ =>
    (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) - log (log x))
    Filter.atTop (nhds mertensConstant) := by
  have h := reciprocal_limit.sub reciprocal_endpoint_gap_limit
  simp only [sub_zero] at h
  convert h using 1
  funext x
  ring

/-- The strict endpoint has an unconditional coarse error bound. -/
theorem reciprocal_strict_error_le_thirteen (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) - log (log x) - mertensConstant| ≤
      13 / log x := by
  have hgap := reciprocal_endpoint_gap x hx
  have hcoarse := reciprocal_error_le_twelve x hx
  have habs := abs_add_le
    ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x) - mertensConstant)
    (-((∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p)))
  have heq : ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) - log (log x) - mertensConstant) -
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) -
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p)) =
      (∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p) - log (log x) - mertensConstant := by ring
  rw [← sub_eq_add_neg, heq, abs_neg, abs_of_nonneg hgap.1] at habs
  have hl : 0 < log x := log_pos (by linarith)
  have hlogle : log x ≤ x := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hsmall : 1 / x ≤ 1 / log x := one_div_le_one_div_of_le hl hlogle
  have halg : 12 / log x + 1 / log x = 13 / log x := by ring
  linarith

/-- The requested large lower bound holds unconditionally on this explicit far tail. -/
theorem reciprocal_lower_huge (x : ℝ)
    (hx : exp (13 / (1.107533e-7 : ℝ)) ≤ x) :
    log (log x) + mertensConstant - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  have hx2 : 2 ≤ x := by
    have he := add_one_le_exp (13 / (1.107533e-7 : ℝ))
    norm_num at he
    linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hL : 13 / (1.107533e-7 : ℝ) ≤ log x := by
    rw [← log_exp (13 / (1.107533e-7 : ℝ))]
    exact log_le_log (exp_pos _) hx
  have hsmall : (13 : ℝ) / log x ≤ 1.107533e-7 := by
    rw [div_le_iff₀ hl]
    nlinarith
  have herror := (reciprocal_strict_error_le_thirteen x hx2).trans hsmall
  have hlow := (abs_le.mp herror).1
  linarith

/-- Each correction term in the common constant is bounded by a square tail. -/
theorem mertens_correction_norm_le (p : ℕ) (hp : p.Prime) :
    ‖log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)‖ ≤ 2 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set t : ℝ := 1 / (p : ℝ) with ht
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have h := abs_log_sub_add_sum_range_le (x := t)
    (by rw [abs_of_nonneg ht0]; linarith) 1
  rw [abs_of_nonneg ht0] at h
  norm_num [Finset.sum_range_succ] at h
  have hr : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - t)]
    nlinarith [mul_nonneg (sq_nonneg t) (by linarith : 0 ≤ 1 - 2 * t)]
  calc
    _ = |t + log (1 - t)| := by rw [Real.norm_eq_abs]; dsimp [t]; congr 1; ring
    _ ≤ 2 * t ^ 2 := h.trans hr
    _ = 2 / (p : ℝ) ^ 2 := by dsimp [t]; ring

/-- The prime correction series defining the sealed constant is absolutely convergent. -/
theorem mertens_correction_summable : Summable (fun p : {p : ℕ // p.Prime} =>
    log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)) := by
  have hs : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
    have h := (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (2 : ℝ)
    simpa only [mul_one_div] using h
  apply (hs.subtype Nat.Prime).of_norm_bounded
  intro p
  exact mertens_correction_norm_le p.1 p.2

/-- LEAF. Small endpoint lower bound of Lemma 6, p. 1219 display 3.
Use Rosser and Schoenfeld Theorem 20 up to 10^8 and the paper computation to 10^12.
The finite computation and the treatment of the strict endpoint remain OPEN. -/
theorem reciprocal_lower_finite (x : ℝ) (hx : 3 ≤ x) (hx1 : x ≤ 1e12) :
    log (log x) + mertensConstant ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  rw [← ported_constant_eq]
  by_cases hx8 : x ≤ 1e8
  · exact FiniteMertens224.rosser_schoenfeld_small x hx hx8
  · exact FiniteMertens224.finite_from_integer_endpoints _
      FiniteMertens224.journal_computation (lt_of_not_ge hx8) hx1

/-- LEAF. Large endpoint lower bound of Lemma 6, p. 1219 display 3.
Use the explicit theta bound and the integral split at 10^19, pp. 1220 and 1221.
The two errors are 9.07982e-8 and 1.99551e-8. Their sum is 1.107533e-7. -/
theorem reciprocal_lower_infinite (x : ℝ) (hx : 1e12 < x) :
    log (log x) + mertensConstant - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  apply LowerMertens224.inclusive_to_strict_lower mertensConstant 1.107533e-7
    1e12 (by norm_num) _ hx
  intro y hy
  apply LowerMertens224.reciprocal_lower_inclusive mertensConstant reciprocal_limit hy
  · intro t ht
    exact ThetaInputs224.theta_table15_6e11 t (by linarith)
  · intro t ht
    apply ThetaInputs224.theta_table15_37
    calc
      exp 37 < exp (log (1e19 : ℝ)) := exp_lt_exp.mpr (by
        linarith [LowerMertens224.log_split_lower])
      _ = (1e19 : ℝ) := exp_log (by norm_num)
      _ ≤ t := ht
  · intro t ht ht1
    have h := ThetaInputs224.theta_buthe_1e19 t (by linarith) ht1
    nlinarith [sqrt_nonneg t]

/-- LEAF. Upper bound of Lemma 6, p. 1219 display 3.
Use Broadbent et al. Table 15 and the partial summation identity 4, p. 1220.
The sum includes a prime at x, as required for the upper estimate. -/
theorem reciprocal_upper (x : ℝ) (hx : exp 2753 < x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p) ≤
      log (log x) + mertensConstant + 2.28975e-9 / log x := by
  have hx2 : 2 ≤ x := by linarith [add_one_le_exp (2753 : ℝ)]
  have hL : 2753 < log x := by
    rw [← log_exp 2753]
    exact log_lt_log (exp_pos 2753) hx
  have hθ : ∀ t : ℝ, x ≤ t →
      |Chebyshev.theta t - t| ≤ (2.2885e-9 : ℝ) * t / log t := by
    intro t ht
    apply ThetaInputs224.theta_table15_2500
    exact (lt_trans (exp_lt_exp.mpr (by norm_num : (2500 : ℝ) < 2753)) hx).trans_le ht
  have hu := ThetaMertens224.reciprocal_upper_from_theta mertensConstant
    2.2885e-9 reciprocal_limit hx2 hθ
  have hr := div_le_div_of_nonneg_right (ThetaMertens224.upper_rounding hL.le)
    (le_of_lt (log_pos (by linarith : 1 < x)))
  have he : (2.2885e-9 : ℝ) / log x * (1 + 3 / (2 * log x)) ≤
      2.28975e-9 / log x := by
    simpa only [div_mul_eq_mul_div] using hr
  linarith

/-- Assemble the existing three-part Lemma6J with the same constant in every bound. -/
theorem lemma6J : Lemma6Input138.Lemma6J mertensConstant := by
  exact ⟨reciprocal_lower_finite, reciprocal_lower_infinite, reciprocal_upper⟩

/-- Exact existing Lemma7J with display 6.
Reuse all product, logarithm and square-tail proofs from task138. -/
theorem lemma7J : Lemma7J :=
  Lemma6Input138.lemma7J_of_lemma6 mertensConstant lemma6J

end
end LeanLab.BS2022GRH.DecompC169c

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_lower_finite
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_lower_infinite
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_upper
#print axioms LeanLab.BS2022GRH.DecompC169c.lemma6J
#print axioms LeanLab.BS2022GRH.DecompC169c.lemma7J

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_limit

#print axioms LeanLab.BS2022GRH.DecompC169c.ported_constant_eq

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_error_le_twelve
#print axioms LeanLab.BS2022GRH.DecompC169c.coarse_error_exceeds_journal

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_endpoint_gap
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_endpoint_gap_limit
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_strict_limit

#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_strict_error_le_thirteen
#print axioms LeanLab.BS2022GRH.DecompC169c.reciprocal_lower_huge

#print axioms LeanLab.BS2022GRH.DecompC169c.mertens_correction_norm_le
#print axioms LeanLab.BS2022GRH.DecompC169c.mertens_correction_summable
