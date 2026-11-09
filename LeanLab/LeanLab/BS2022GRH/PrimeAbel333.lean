/- AI wrote the Lean code for CODEX task333. Goldbach is open.
The prime count route in Schoenfeld Corollary 2 p. 340 display 6.21.
Source https://doi.org/10.1090/S0025-5718-1976-0457374-X. -/
import LeanLab.BS2022GRH.SchoenfeldEnvelope236
import LeanLab.BS2022GRH.DecompC169c

namespace LeanLab.BS2022GRH.PrimeAbel333
open Real Finset MeasureTheory intervalIntegral Filter Topology
noncomputable section

/-- The inclusive prime reciprocal sum in Schoenfeld p. 340. -/
def reciprocalSum (x : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p

/-- The prime count error in Schoenfeld p. 340. -/
def primeError (x : ℝ) : ℝ := PaperInputs148.primeCount x - liPV x

/-- The elementary majorant primitive in Schoenfeld p. 340. -/
def kernelPrimitive (x : ℝ) : ℝ := -(2 * log x + 4) / √x

/-- Local integrability of the prime count term in Abel summation, p. 340. -/
theorem prime_weight_integrable (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => PaperInputs148.primeCount t / t ^ 2) volume a b := by
  let c : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  have hsum (y : ℝ) : ∑ n ∈ Icc 0 ⌊y⌋₊, c n = PaperInputs148.primeCount y := by
    simp [c, PaperInputs148.primeCount, Nat.range_succ_eq_Icc_zero, ← sum_filter]
  have hcont : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.Icc a b) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have h := integrableOn_mul_sum_Icc c (m := 0) (by linarith : 0 ≤ a) hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  convert h using 1
  ext t
  rw [hsum]
  ring

/-- Finite reciprocal Abel summation against the prime count, p. 340. -/
theorem reciprocal_abel (x : ℝ) (hx : 2 ≤ x) :
    reciprocalSum x = PaperInputs148.primeCount x / x +
      ∫ t in (2 : ℝ)..x, PaperInputs148.primeCount t / t ^ 2 := by
  let c : ℕ → ℝ := fun n => if n.Prime then 1 else 0
  have hsum (y : ℝ) : ∑ n ∈ Icc 0 ⌊y⌋₊, c n = PaperInputs148.primeCount y := by
    simp [c, PaperInputs148.primeCount, Nat.range_succ_eq_Icc_zero, ← sum_filter]
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun y : ℝ => 1 / y) (-(1 / t ^ 2)) t := by
    simpa only [one_div] using (hasDerivAt_inv ht.ne')
  have hrecip : reciprocalSum x = ∑ n ∈ Icc 0 ⌊x⌋₊, (1 / (n : ℝ)) * c n := by
    unfold reciprocalSum
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [c, hp]
  rw [hrecip, sum_mul_eq_sub_integral_mul₁ c (f := fun t : ℝ => 1 / t)
    (by norm_num [c]) (by norm_num [c]), hsum, ← integral_of_le hx]
  · rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
    congr 1
    · ring
    · apply integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      dsimp only
      rw [(hd t (by linarith [ht.1])).deriv, hsum]
      ring
  · intro t ht
    exact (hd t (by linarith [ht.1])).differentiableAt
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr (f := fun t : ℝ => -(1 / t ^ 2))
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
    · intro t ht
      exact (hd t (by linarith [ht.1])).deriv

/-- The li part has an explicit primitive above two, Schoenfeld p. 340. -/
theorem li_primitive_derivative (t : ℝ) (ht : 2 < t) :
    HasDerivAt (fun y : ℝ => log (log y) - liPV y / y) (liPV t / t ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hL : log t ≠ 0 := (log_pos (by linarith : 1 < t)).ne'
  have h := ((hasDerivAt_log ht0).log hL).sub
    ((SliceMass236.liPV_hasDeriv t ht).div (hasDerivAt_id t) ht0)
  convert h using 1
  · ext y
    rfl
  · dsimp only [id_eq]
    field_simp
    <;> ring

/-- Local integrability of the li part of the Abel error, p. 340. -/
theorem li_weight_integrable (a b : ℝ) (ha : 2 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => liPV t / t ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht2 : 2 < t := ha.trans_le ht.1
  exact ContinuousAt.continuousWithinAt
    ((SliceMass236.liPV_hasDeriv t ht2).continuousAt.div
      (continuousAt_id.pow 2) (by positivity))

/-- The finite error identity before passing to the common Mertens limit.
Schoenfeld p. 340 proof of display 6.21. -/
theorem reciprocal_error_identity (x y : ℝ) (hx : 2 < x) (hxy : x ≤ y) :
    reciprocalSum x - log (log x) = reciprocalSum y - log (log y) +
      primeError x / x - primeError y / y - ∫ t in x..y, primeError t / t ^ 2 := by
  have hpx := reciprocal_abel x hx.le
  have hpy := reciprocal_abel y (hx.le.trans hxy)
  have hp := prime_weight_integrable x y (by linarith) hxy
  have hli := li_weight_integrable x y hx hxy
  have hadd := integral_add_adjacent_intervals
    (prime_weight_integrable 2 x (by norm_num) hx.le) hp
  have hI : (∫ t in x..y, liPV t / t ^ 2) =
      (log (log y) - liPV y / y) - (log (log x) - liPV x / x) := by
    apply integral_eq_sub_of_hasDerivAt _ hli
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    exact li_primitive_derivative t (hx.trans_le ht.1)
  have he : (∫ t in x..y, primeError t / t ^ 2) =
      (∫ t in x..y, PaperInputs148.primeCount t / t ^ 2) - ∫ t in x..y, liPV t / t ^ 2 := by
    rw [← integral_sub hp hli]
    apply integral_congr
    intro t ht
    dsimp [primeError]
    ring
  rw [he, hI]
  dsimp [primeError]
  simp only [sub_div]
  linarith

/-- Differentiate the explicit square root majorant primitive, p. 340. -/
theorem kernel_derivative (t : ℝ) (ht : 0 < t) :
    HasDerivAt kernelPrimitive (log t / (t * √t)) t := by
  have hs : √t ≠ 0 := (sqrt_pos.mpr ht).ne'
  have h := ((((hasDerivAt_log ht.ne').const_mul 2).add_const 4).neg).div
    (hasDerivAt_sqrt ht.ne') hs
  convert h using 1
  · rfl
  · dsimp
    field_simp
    rw [sq_sqrt ht.le]
    <;> ring

/-- Integrate the elementary majorant exactly on a finite interval, p. 340. -/
theorem kernel_integral (x y : ℝ) (hx : 1 < x) (hxy : x ≤ y) :
    (∫ t in x..y, log t / (t * √t)) =
      (2 * log x + 4) / √x - (2 * log y + 4) / √y := by
  have hi : IntervalIntegrable (fun t : ℝ => log t / (t * √t)) volume x y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have h := integral_eq_sub_of_hasDerivAt (a := x) (b := y) (f := kernelPrimitive)
    (fun t ht => kernel_derivative t (by
      rw [Set.uIcc_of_le hxy] at ht
      linarith [ht.1])) hi
  rw [h]
  dsimp [kernelPrimitive]
  ring

end
end LeanLab.BS2022GRH.PrimeAbel333

#print axioms LeanLab.BS2022GRH.PrimeAbel333.prime_weight_integrable
#print axioms LeanLab.BS2022GRH.PrimeAbel333.reciprocal_abel
#print axioms LeanLab.BS2022GRH.PrimeAbel333.li_primitive_derivative
#print axioms LeanLab.BS2022GRH.PrimeAbel333.li_weight_integrable
#print axioms LeanLab.BS2022GRH.PrimeAbel333.reciprocal_error_identity
#print axioms LeanLab.BS2022GRH.PrimeAbel333.kernel_derivative
#print axioms LeanLab.BS2022GRH.PrimeAbel333.kernel_integral
