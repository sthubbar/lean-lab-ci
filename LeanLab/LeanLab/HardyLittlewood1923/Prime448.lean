import LeanLab.HardyLittlewood1923.Inducing448
import Mathlib.NumberTheory.Chebyshev

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 9 and 10 Lemma 2 equation 2.21.
Mathlib supplies the proper prime power partial mass bound.
PNTPort supplies the bad prime power partial mass bound.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Prime448
open Real Finset
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Inducing448
/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. Keep von Mangoldt only at proper prime powers. -/
noncomputable def properWeight (m : ℕ) : ℝ :=
  if m.Prime then 0 else ArithmeticFunction.vonMangoldt m

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The proper prime power coefficient is nonnegative. -/
theorem properWeight_nonneg (m : ℕ) : 0 ≤ properWeight m := by
  unfold properWeight
  split_ifs
  · exact le_refl 0
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The proper prime power coefficient is bounded by von Mangoldt. -/
theorem properWeight_le (m : ℕ) : properWeight m ≤ ArithmeticFunction.vonMangoldt m := by
  unfold properWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_refl _

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The partial proper prime power mass equals Chebyshev psi minus theta. -/
theorem proper_partial_identity (M : ℕ) :
    (∑ m ∈ range (M + 1), properWeight m) = Chebyshev.psi M - Chebyshev.theta M := by
  have hzero : properWeight 0 = 0 := by simp [properWeight]
  rw [← sum_Icc_one_eq_range _ hzero M, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast, sum_filter, ← Icc_add_one_left_eq_Ioc, zero_add]
  apply sum_congr rfl
  intro m _
  by_cases hm : m.Prime <;> simp [properWeight, hm]

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The partial proper prime power mass is at most a fixed constant times square root M. -/
theorem proper_partial_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ,
    (∑ m ∈ range (M + 1), properWeight m) ≤ K * Real.sqrt M := by
  obtain ⟨C, hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C|, abs_nonneg _, fun M => ?_⟩
  rw [proper_partial_identity]
  exact (hc M).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. Positive radial damping makes the proper prime power mass summable. -/
theorem proper_mass_summable {n : ℕ} (hn : 0 < n) :
    Summable (fun m : ℕ => properWeight m * Real.exp (-(m : ℝ) / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : 0 < 1 / (n : ℝ))
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (properWeight_nonneg m) (Real.exp_pos _).le) _ hs
  intro m
  have hb : properWeight m ≤ (m : ℝ) := (properWeight_le m).trans
    (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg m)))
  simpa only [pow_one, show -(1 / (n : ℝ)) * (m : ℝ) = -(m : ℝ) / n by ring] using
    mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(m : ℝ) / n)).le

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. Each length n block has a linear times exponential envelope with square root n. -/
theorem proper_block {n : ℕ} (hn : 4 ≤ n) {K : ℝ} (hK : 0 ≤ K)
    (hpartial : ∀ M : ℕ, (∑ m ∈ range (M + 1), properWeight m) ≤ K * Real.sqrt M) (k : ℕ) :
    (∑ r ∈ range n, properWeight (k * n + r) * Real.exp (-(k * n + r : ℕ) / (n : ℝ))) ≤
      K * (((k : ℝ) + 1) * Real.exp (-(k : ℝ))) * Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let M := (k + 1) * n
  let T := (range n).image (fun r => k * n + r)
  have hsub : T ⊆ range (M + 1) := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
    apply mem_range.mpr
    dsimp [M]
    have := mem_range.mp hr
    nlinarith
  have hsum : (∑ r ∈ range n, properWeight (k * n + r)) = ∑ m ∈ T, properWeight m := by
    dsimp [T]
    rw [sum_image (by
      intro r hr s hs h
      change k * n + r = k * n + s at h
      omega)]
  have he (r : ℕ) : Real.exp (-(k * n + r : ℕ) / (n : ℝ)) ≤ Real.exp (-(k : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hnR]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hsqrt : Real.sqrt (M : ℝ) ≤ ((k : ℝ) + 1) * Real.sqrt n := by
    dsimp [M]
    push_cast
    rw [Real.sqrt_mul (by positivity : 0 ≤ (k : ℝ) + 1)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  calc
    _ ≤ ∑ r ∈ range n, properWeight (k * n + r) * Real.exp (-(k : ℝ)) :=
      sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (he r) (properWeight_nonneg _)
    _ = (∑ r ∈ range n, properWeight (k * n + r)) * Real.exp (-(k : ℝ)) := by rw [sum_mul]
    _ ≤ (∑ m ∈ range (M + 1), properWeight m) * Real.exp (-(k : ℝ)) := by
      rw [hsum]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => properWeight_nonneg m)
    _ ≤ (K * Real.sqrt M) * Real.exp (-(k : ℝ)) :=
      mul_le_mul_of_nonneg_right (hpartial M) (Real.exp_pos _).le
    _ ≤ (K * (((k : ℝ) + 1) * Real.sqrt n)) * Real.exp (-(k : ℝ)) := by gcongr
    _ = _ := by ring

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The full damped proper prime power mass is at most a fixed constant times square root n. -/
theorem proper_mass_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
    (∑' m : ℕ, properWeight m * Real.exp (-(m : ℝ) / n)) ≤ C * Real.sqrt n := by
  obtain ⟨K, hK, hpartial⟩ := proper_partial_bound
  let v : ℕ → ℝ := fun k => ((k : ℝ) + 1) * Real.exp (-(k : ℝ))
  have hs0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1)
  have hs1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have hvs : Summable v := by
    apply (hs1.add hs0).congr
    intro k
    dsimp [v]
    simp only [pow_one, pow_zero, neg_one_mul]
    ring
  have hv : 0 ≤ ∑' k, v k := tsum_nonneg (fun k => by dsimp [v]; positivity)
  refine ⟨K * ∑' k, v k, by positivity, fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  haveI : NeZero n := ⟨hnpos.ne'⟩
  let f : ℕ → ℝ := fun m => properWeight m * Real.exp (-(m : ℝ) / n)
  have hf : Summable f := proper_mass_summable hnpos
  have hp : Summable (fun z : ℕ × Fin n => f (z.1 * n + z.2)) :=
    hf.comp_injective (Nat.divModEquiv n).symm.injective
  have heq : (∑' m : ℕ, f m) = ∑' k : ℕ, ∑ r : Fin n, f (k * n + r) := by
    calc
      _ = ∑' z : ℕ × Fin n, f (z.1 * n + z.2) := ((Nat.divModEquiv n).symm.tsum_eq f).symm
      _ = _ := by rw [hp.tsum_prod]; simp only [tsum_fintype]
  have hb (k : ℕ) : (∑ r : Fin n, f (k * n + r)) ≤ K * v k * Real.sqrt n := by
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => f (k * n + r))]
    simpa only [f, v] using proper_block hn hK hpartial k
  have houter : Summable (fun k : ℕ => ∑ r : Fin n, f (k * n + r)) := by
    simpa only [tsum_fintype] using hp.prod
  change (∑' m : ℕ, f m) ≤ _
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, K * v k * Real.sqrt n :=
      houter.tsum_le_tsum hb ((hvs.mul_left K).mul_right (Real.sqrt n))
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]


/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The rational angular shift is exactly the standard additive character times the unshifted exponential. -/
theorem prime_phase {n q : ℕ} [NeZero q] (p m : ℕ) (θ : ℝ) :
    Complex.exp (-(m : ℂ) * localY n (2 * π * (p : ℝ) / q + θ)) =
      (ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) *
        Complex.exp (-(m : ℂ) * localY n θ) := by
  simp only [AddChar.mulShift_apply]
  rw [show (p : ZMod q) * (m : ZMod q) = ((p * m : ℕ) : ZMod q) by simp,
    ← Int.cast_natCast (p * m), ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  simp only [localY, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Int.cast_natCast, Int.cast_mul, Nat.cast_mul]
  ring

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The standard additive phase has norm one. -/
theorem phase_norm {q : ℕ} [NeZero q] (p m : ℕ) :
    ‖(ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q)‖ = 1 := by
  simp only [AddChar.mulShift_apply, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The unit restricted exponential von Mangoldt series is summable. -/
theorem unit_phase_summable {n q : ℕ} [NeZero q] (hn : 0 < n) (p : ℕ) (θ : ℝ) :
    Summable (fun m : ℕ => if IsUnit (m : ZMod q) then
      ((ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) *
        (ArithmeticFunction.vonMangoldt m : ℂ)) * Complex.exp (-(m : ℂ) * localY n θ) else 0) := by
  have hz : 0 < (localY n θ).re := by rw [localY_re]; positivity
  have hb : ∀ m : ℕ, ‖if IsUnit (m : ZMod q) then
      (ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ)
      else 0‖ ≤ ArithmeticFunction.vonMangoldt m := by
    intro m
    split_ifs
    · rw [norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    · simpa only [norm_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := m))
  simpa only [ite_mul, zero_mul] using Task52.summable_exponential hb hz

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The coefficient difference is bounded by the proper and bad prime power coefficients. -/
theorem prime_unit_coeff_bound (q m : ℕ) :
    ‖(if m.Prime then (Real.log m : ℂ) else 0) -
      (if m.Coprime q then (ArithmeticFunction.vonMangoldt m : ℂ) else 0)‖ ≤
        properWeight m + badWeight q m := by
  by_cases hp : m.Prime
  · have hv := ArithmeticFunction.vonMangoldt_apply_prime hp
    by_cases hc : m.Coprime q
    · simp only [properWeight, badWeight, if_pos hp, if_pos hc, hv, sub_self, norm_zero, zero_add, le_refl]
    · simp only [properWeight, badWeight, if_pos hp, if_neg hc, hv, sub_zero, zero_add,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg m), le_refl]
  · by_cases hc : m.Coprime q
    · simp only [properWeight, badWeight, if_neg hp, if_pos hc, zero_sub, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, add_zero, le_refl]
    · simp only [properWeight, badWeight, if_neg hp, if_neg hc, sub_self, norm_zero]
      exact add_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The actual prime to unit series difference is bounded by the two damped masses. -/
theorem prime_unit_series_bound {n q : ℕ} [NeZero q] (hn : 0 < n) (p : ℕ) (θ : ℝ) :
    ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) -
      Task52.unitWeightedSum (ZMod.stdAddChar.mulShift (p : ZMod q)) (localY n θ)‖ ≤
        (∑' m : ℕ, properWeight m * Real.exp (-(m : ℝ) / n)) +
        (∑' m : ℕ, badWeight q m * Real.exp (-(m : ℝ) / n)) := by
  classical
  have hz : 0 < (localY n (2 * π * (p : ℝ) / q + θ)).re := by rw [localY_re]; positivity
  have hsp := primeSeries_summable hz
  have hsu : Summable (fun m : ℕ => if m.Coprime q then
      ((ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) *
        (ArithmeticFunction.vonMangoldt m : ℂ)) * Complex.exp (-(m : ℂ) * localY n θ) else 0) := by
    simpa only [ZMod.isUnit_iff_coprime] using unit_phase_summable (q := q) hn p θ
  have hdiff := hsp.sub hsu
  have hsm := (proper_mass_summable hn).add (bad_mass_summable hn q)
  unfold primeSeries Task52.unitWeightedSum
  simp_rw [ZMod.isUnit_iff_coprime]
  rw [← hsp.tsum_sub hsu, ← (proper_mass_summable hn).tsum_add (bad_mass_summable hn q)]
  apply (norm_tsum_le_tsum_norm hdiff.norm).trans
  apply hdiff.norm.tsum_le_tsum _ hsm
  intro m
  have heq :
      (if m.Prime then (Real.log m : ℂ) *
        Complex.exp (-(m : ℂ) * localY n (2 * π * (p : ℝ) / q + θ)) else 0) -
      (if m.Coprime q then
        ((ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) *
          (ArithmeticFunction.vonMangoldt m : ℂ)) * Complex.exp (-(m : ℂ) * localY n θ) else 0) =
      ((if m.Prime then (Real.log m : ℂ) else 0) -
        (if m.Coprime q then (ArithmeticFunction.vonMangoldt m : ℂ) else 0)) *
      ((ZMod.stdAddChar.mulShift (p : ZMod q)) (m : ZMod q) *
        Complex.exp (-(m : ℂ) * localY n θ)) := by
    rw [prime_phase (n := n) (q := q) p m θ]
    split_ifs <;> ring
  rw [heq, norm_mul, norm_mul, phase_norm, one_mul, Complex.norm_exp]
  have hre : (-(m : ℂ) * localY n θ).re = -(m : ℝ) / n := by simp [localY]; ring
  rw [hre]
  calc
    _ ≤ (properWeight m + badWeight q m) * Real.exp (-(m : ℝ) / n) :=
      mul_le_mul_of_nonneg_right (prime_unit_coeff_bound q m) (Real.exp_pos _).le
    _ = _ := by ring

open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 pages 9 and 10 Lemma 2 equation 2.21. The exact original prime to unit correction has logarithmic exponent one with no OPEN input. -/
theorem prime_unit_correction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], ∀ p : ℕ, ∀ θ : ℝ,
        ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) -
          Task52.unitWeightedSum (ZMod.stdAddChar.mulShift (p : ZMod q)) (localY n θ)‖ ≤
            C * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ A := by
  obtain ⟨C, hC, hc⟩ := proper_mass_bound
  obtain ⟨D, hD, hd⟩ := bad_mass_bound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1, C / Real.log 2 + D, by positivity, fun n hn q _ p θ => ?_⟩
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq : Real.log 2 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ q + 1))
  have hs : 1 ≤ Real.log ((q : ℝ) + 1) / Real.log 2 := (one_le_div hlog2).mpr hlogq
  have hbase : C * Real.sqrt n ≤ C / Real.log 2 * Real.sqrt n * Real.log ((q : ℝ) + 1) := by
    calc
      _ ≤ (C * Real.sqrt n) * (Real.log ((q : ℝ) + 1) / Real.log 2) :=
        le_mul_of_one_le_right (by positivity) hs
      _ = _ := by ring
  rw [pow_one]
  calc
    _ ≤ C * Real.sqrt n + D * Real.sqrt n * Real.log ((q : ℝ) + 1) :=
      (prime_unit_series_bound (q := q) (by omega : 0 < n) p θ).trans
        (add_le_add (hc n hn) (hd n hn q hq))
    _ ≤ _ := by nlinarith only [hbase]

#print axioms proper_partial_identity
#print axioms proper_partial_bound
#print axioms proper_mass_summable
#print axioms proper_block
#print axioms proper_mass_bound
#print axioms prime_phase
#print axioms phase_norm
#print axioms unit_phase_summable
#print axioms prime_unit_coeff_bound
#print axioms prime_unit_series_bound
#print axioms prime_unit_correction
end LeanLab.HardyLittlewood1923.Prime448
