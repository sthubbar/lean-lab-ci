import LeanLab.HardyLittlewood1923.Decomp415c
import LeanLab.HardyLittlewood1923.APSums
import LeanLab.PNTPort.BV.Helpers
import Mathlib.Logic.Equiv.Fin.Basic

/-!
AI wrote this Lean code for CODEX task448.
P0004 page 20 equation 2.833 through the imprimitive Euler factors.
The partial bad prime power estimate is reused from PNTPort.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Inducing448
open Real Finset
open LeanLab.PNTPort.BV
/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The bad prime power coefficient keeps von Mangoldt exactly at integers not coprime to the level. -/
noncomputable def badWeight (q m : ℕ) : ℝ :=
  if m.Coprime q then 0 else ArithmeticFunction.vonMangoldt m

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The bad prime power coefficient is nonnegative. -/
theorem badWeight_nonneg (q m : ℕ) : 0 ≤ badWeight q m := by
  unfold badWeight
  split_ifs
  · exact le_refl 0
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The bad coefficient is at most von Mangoldt. -/
theorem badWeight_le (q m : ℕ) : badWeight q m ≤ ArithmeticFunction.vonMangoldt m := by
  unfold badWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_refl _

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The PNTPort logarithmic partial sum bound is at most a square root bound. -/
theorem bad_partial {M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q) :
    (∑ m ∈ range (M + 1), badWeight q m) ≤
      (2 / Real.log 2) * Real.log ((q : ℝ) + 1) * Real.sqrt M := by
  have hzero : badWeight q 0 = 0 := by simp [badWeight]
  have heq : (∑ m ∈ range (M + 1), badWeight q m) = psiBad M q := by
    rw [← sum_Icc_one_eq_range _ hzero M]
    unfold psiBad
    simp only [Nat.floor_natCast, sum_filter]
    apply sum_congr rfl
    intro m _
    by_cases hm : m.Coprime q <;> simp [badWeight, hm]
  rw [heq]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hlogq : 0 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hqq : Real.log q ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < q)) (by linarith)
  have hlog : Real.log (M : ℝ) ≤ 2 * Real.sqrt M := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg M) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith only [h]
  calc
    _ ≤ Real.log q / Real.log 2 * Real.log M := psiBad_le (by exact_mod_cast hM) hq
    _ ≤ Real.log ((q : ℝ) + 1) / Real.log 2 * Real.log M := by
      gcongr
    _ ≤ Real.log ((q : ℝ) + 1) / Real.log 2 * (2 * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The damped bad prime power series is absolutely summable. -/
theorem bad_mass_summable {n : ℕ} (hn : 0 < n) (q : ℕ) :
    Summable (fun m : ℕ => badWeight q m * Real.exp (-(m : ℝ) / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : 0 < 1 / (n : ℝ))
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (badWeight_nonneg q m) (Real.exp_pos _).le) _ hs
  intro m
  have hb : badWeight q m ≤ (m : ℝ) := (badWeight_le q m).trans
    (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg m)))
  simpa only [pow_one, show -(1 / (n : ℝ)) * (m : ℝ) = -(m : ℝ) / n by ring] using
    mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(m : ℝ) / n)).le

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. Every block of length n has a summable exponential envelope. -/
theorem bad_block {n q : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q) (k : ℕ) :
    (∑ r ∈ range n, badWeight q (k * n + r) * Real.exp (-(k * n + r : ℕ) / (n : ℝ))) ≤
      (2 / Real.log 2) * (((k : ℝ) + 1) * Real.exp (-(k : ℝ))) *
        Real.sqrt n * Real.log ((q : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  let M := (k + 1) * n
  let T := (range n).image (fun r => k * n + r)
  have hsub : T ⊆ range (M + 1) := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
    apply mem_range.mpr
    dsimp [M]
    have := mem_range.mp hr
    nlinarith
  have hsum : (∑ r ∈ range n, badWeight q (k * n + r)) = ∑ m ∈ T, badWeight q m := by
    dsimp [T]
    rw [sum_image (by
      intro r hr s hs h
      change k * n + r = k * n + s at h
      omega)]
  have hM : 1 ≤ M := by dsimp [M]; nlinarith
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
    _ ≤ ∑ r ∈ range n, badWeight q (k * n + r) * Real.exp (-(k : ℝ)) :=
      sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (he r) (badWeight_nonneg _ _)
    _ = (∑ r ∈ range n, badWeight q (k * n + r)) * Real.exp (-(k : ℝ)) := by rw [sum_mul]
    _ ≤ (∑ m ∈ range (M + 1), badWeight q m) * Real.exp (-(k : ℝ)) := by
      rw [hsum]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => badWeight_nonneg q m)
    _ ≤ ((2 / Real.log 2) * Real.log ((q : ℝ) + 1) * Real.sqrt M) * Real.exp (-(k : ℝ)) :=
      mul_le_mul_of_nonneg_right (bad_partial hM hq) (Real.exp_pos _).le
    _ ≤ ((2 / Real.log 2) * Real.log ((q : ℝ) + 1) *
        (((k : ℝ) + 1) * Real.sqrt n)) * Real.exp (-(k : ℝ)) := by gcongr
    _ = _ := by ring

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The smoothed bad prime power mass is bounded by square root n times log of q plus one. -/
theorem bad_mass_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ q : ℕ, 1 ≤ q →
    (∑' m : ℕ, badWeight q m * Real.exp (-(m : ℝ) / n)) ≤
      C * Real.sqrt n * Real.log ((q : ℝ) + 1) := by
  let v : ℕ → ℝ := fun k => ((k : ℝ) + 1) * Real.exp (-(k : ℝ))
  have hs0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1)
  have hs1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have hvs : Summable v := by
    apply (hs1.add hs0).congr
    intro k
    dsimp [v]
    simp only [pow_one, pow_zero, neg_one_mul]
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 ≤ ∑' k, v k := tsum_nonneg (fun k => by dsimp [v]; positivity)
  refine ⟨(2 / Real.log 2) * ∑' k, v k, by positivity, fun n hn q hq => ?_⟩
  have hnpos : 0 < n := by omega
  haveI : NeZero n := ⟨hnpos.ne'⟩
  let f : ℕ → ℝ := fun m => badWeight q m * Real.exp (-(m : ℝ) / n)
  have hf : Summable f := bad_mass_summable hnpos q
  have hp : Summable (fun z : ℕ × Fin n => f (z.1 * n + z.2)) :=
    hf.comp_injective (Nat.divModEquiv n).symm.injective
  have heq : (∑' m : ℕ, f m) = ∑' k : ℕ, ∑ r : Fin n, f (k * n + r) := by
    calc
      _ = ∑' z : ℕ × Fin n, f (z.1 * n + z.2) := ((Nat.divModEquiv n).symm.tsum_eq f).symm
      _ = _ := by rw [hp.tsum_prod]; simp only [tsum_fintype]
  have hb (k : ℕ) : (∑ r : Fin n, f (k * n + r)) ≤
      (2 / Real.log 2) * v k * Real.sqrt n * Real.log ((q : ℝ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => f (k * n + r))]
    simpa only [f, v] using bad_block hn hq k
  have houter : Summable (fun k : ℕ => ∑ r : Fin n, f (k * n + r)) := by
    simpa only [tsum_fintype] using hp.prod
  change (∑' m : ℕ, f m) ≤ _
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, (2 / Real.log 2) * v k * Real.sqrt n * Real.log ((q : ℝ) + 1) :=
      houter.tsum_le_tsum hb (((hvs.mul_left (2 / Real.log 2)).mul_right (Real.sqrt n)).mul_right _)
    _ = _ := by rw [tsum_mul_right, tsum_mul_right, tsum_mul_left]

open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp415c

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The difference of original and inducing character coefficients is supported on the bad prime powers. -/
theorem primitive_coeff_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖χ (m : ZMod q) * (ArithmeticFunction.vonMangoldt m : ℂ) -
      χ.primitiveCharacter (m : ZMod χ.conductor) * (ArithmeticFunction.vonMangoldt m : ℂ)‖ ≤
        badWeight q m := by
  by_cases hm : m.Coprime q
  · have hco : IsCoprime (m : ℤ) q := Nat.isCoprime_iff_coprime.mpr hm
    have hag := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hco
    push_cast at hag
    rw [hag, sub_self, norm_zero]
    exact badWeight_nonneg q m
  · have hnu : ¬ IsUnit (m : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hm
    rw [MulChar.map_nonunit χ hnu, zero_mul, zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [badWeight, if_neg hm]
    calc
      _ ≤ 1 * ArithmeticFunction.vonMangoldt m := mul_le_mul_of_nonneg_right
        (DirichletCharacter.norm_le_one _ _) ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := one_mul _

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. A character is principal exactly when its inducing primitive character is principal. -/
theorem primitive_one_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  constructor
  · intro h
    apply DirichletCharacter.eq_one_iff_conductor_eq_one.mpr
    have hp := χ.primitiveCharacter_isPrimitive
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. Absolute convergence bounds the weighted character difference by the bad prime power mass. -/
theorem weighted_difference_bound {n q : ℕ} [NeZero q] (hn : 0 < n)
    (χ : DirichletCharacter ℂ q) (θ : ℝ) :
    ‖Task52.weightedSum χ (localY n θ) - Task52.weightedSum χ.primitiveCharacter (localY n θ)‖ ≤
      ∑' m : ℕ, badWeight q m * Real.exp (-(m : ℝ) / n) := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hz : 0 < (localY n θ).re := by rw [localY_re]; positivity
  have ha := Task52.summable_weightedSum χ hz
  have hb := Task52.summable_weightedSum χ.primitiveCharacter hz
  have hdiff := ha.sub hb
  unfold Task52.weightedSum
  rw [← ha.tsum_sub hb]
  apply (norm_tsum_le_tsum_norm hdiff.norm).trans
  apply hdiff.norm.tsum_le_tsum _ (bad_mass_summable hn q)
  intro m
  rw [← sub_mul, norm_mul, Complex.norm_exp]
  have hre : (-(m : ℂ) * localY n θ).re = -(m : ℝ) / n := by simp [localY]; ring
  rw [hre]
  exact mul_le_mul_of_nonneg_right (primitive_coeff_bound χ m) (Real.exp_pos _).le

/-- P0004 page 20 equation 2.833 and the Euler product on page 10. The exact inducing correction target follows from the proved bad mass bound and cancellation of the common principal pole. -/
theorem inducing_character_correction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, ∀ θ : ℝ,
        ‖characterError n q χ θ -
          characterError n χ.conductor χ.primitiveCharacter θ‖ ≤
            C * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ A := by
  obtain ⟨C, hC, hc⟩ := bad_mass_bound
  refine ⟨1, C, hC, fun n hn q _ hq χ θ => ?_⟩
  have heq : characterError n q χ θ - characterError n χ.conductor χ.primitiveCharacter θ =
      Task52.weightedSum χ (localY n θ) - Task52.weightedSum χ.primitiveCharacter (localY n θ) := by
    unfold characterError
    rw [primitive_one_iff χ]
    ring
  rw [heq, pow_one]
  exact (weighted_difference_bound (by omega : 0 < n) χ θ).trans (hc n hn q hq)

#print axioms badWeight_nonneg
#print axioms badWeight_le
#print axioms bad_partial
#print axioms bad_mass_summable
#print axioms bad_block
#print axioms bad_mass_bound
#print axioms primitive_coeff_bound
#print axioms primitive_one_iff
#print axioms weighted_difference_bound
#print axioms inducing_character_correction
end LeanLab.HardyLittlewood1923.Inducing448
