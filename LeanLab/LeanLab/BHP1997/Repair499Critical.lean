/-
P0069 Baker Harman Pintz 1997, page 22, the nonprincipal critical line.
The cutoff form of partial summation separates the finite sum from its tail.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.DirichletZF.Growth
import LeanLab.BHP1997.TrivialC165

namespace LeanLab.BHP1997.Repair499Critical
open Classical Complex MeasureTheory Set Finset MeanValue132
open LeanLab.PNTPort.DirichletZF

/-- Page 22, finite partial summation at a positive integer cutoff. -/
theorem partialSum_abel499 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    partialSum N χ t = (N : ℂ) ^ (-Thm4.half t) * A χ N +
      Thm4.half t * ∫ u in Ioc (1 : ℝ) (N : ℝ),
        A χ u * (u : ℂ) ^ (-(Thm4.half t + 1)) := by
  let s := Thm4.half t
  have hs : s ≠ 0 := Complex.ne_zero_of_re_pos (by norm_num [s, Thm4.half])
  have hq1 : q ≠ 1 := by
    intro hq
    subst q
    exact hχ (Subsingleton.elim _ _)
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
  have hz : χ (0 : ZMod q) = 0 := χ.map_nonunit not_isUnit_zero
  have hA (u : ℝ) : (∑ k ∈ Icc 0 ⌊u⌋₊, χ (k : ZMod q)) = A χ u := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
    simp only [Nat.cast_zero, hz, zero_add, ← Finset.Icc_add_one_left_eq_Ioc]
    rfl
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun v : ℝ => (v : ℂ) ^ (-s))
        ((-s) * (u : ℂ) ^ (-s - 1)) u :=
    hasDerivAt_ofReal_cpow_const hu.ne' (neg_ne_zero.mpr hs)
  have hc : ContinuousOn (fun u : ℝ => (-s) * (u : ℂ) ^ (-s - 1)) (Icc 1 (N : ℝ)) := by
    refine continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.cpow_const ?_)
    intro u hu
    exact Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le zero_lt_one hu.1)
  have hi : IntegrableOn (deriv (fun v : ℝ => (v : ℂ) ^ (-s))) (Icc 1 (N : ℝ)) :=
    hc.integrableOn_Icc.congr_fun (fun u hu => (hd u (lt_of_lt_of_le zero_lt_one hu.1)).deriv.symm)
      measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul₀' (fun k : ℕ => χ (k : ZMod q)) (by simpa using hz) N
    (fun u hu => (hd u (lt_of_lt_of_le zero_lt_one hu.1)).differentiableAt) hi
  simp only [Complex.ofReal_natCast] at hab
  have hS : (∑ k ∈ Icc 0 N, (k : ℂ) ^ (-s) * χ (k : ZMod q)) = partialSum N χ t := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
    simp only [Nat.cast_zero, hz, mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc]
    simp only [partialSum, Nat.floor_natCast]
    apply sum_congr rfl
    intro k hk
    simp [Complex.cpow_neg, div_eq_mul_inv, mul_comm, s]
  rw [hS] at hab
  have hAN : (∑ k ∈ Icc 0 N, χ (k : ZMod q)) = A χ N := by
    simpa only [Nat.floor_natCast] using hA (N : ℝ)
  rw [hAN] at hab
  have hI : (∫ u in Ioc (1 : ℝ) (N : ℝ),
      deriv (fun v : ℝ => (v : ℂ) ^ (-s)) u * ∑ k ∈ Icc 0 ⌊u⌋₊, χ (k : ZMod q)) =
      (-s) * ∫ u in Ioc (1 : ℝ) (N : ℝ), A χ u * (u : ℂ) ^ (-(s + 1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [(hd u (lt_trans zero_lt_one hu.1)).deriv, hA]
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  rw [hI] at hab
  simpa only [s, neg_mul, sub_neg_eq_add] using hab
/-- Page 22, absolute integrability of the partial-summation tail. -/
theorem tail_integrable499 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t R : ℝ) (hR : 1 ≤ R) :
    IntegrableOn (fun u : ℝ => A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))) (Ioi R) := by
  have hc : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-(Thm4.half t + 1))) (Ioi R) := by
    refine Complex.continuous_ofReal.continuousOn.cpow_const ?_
    intro u hu
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [show R < u from hu])
  have hmajor : IntegrableOn (fun u : ℝ => (q : ℝ) * u ^ (-(3 / 2 : ℝ))) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith : 0 < R)).const_mul _
  refine hmajor.mono' ((measurable_A χ).aestronglyMeasurable.mul
    (hc.aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := by linarith [show R < u from hu]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  have he : (-(Thm4.half t + 1)).re = -(3 / 2 : ℝ) := by norm_num [Thm4.half]
  rw [he]
  exact mul_le_mul_of_nonneg_right (norm_A_le hχ u) (Real.rpow_nonneg hu0.le _)

/-- Page 22, the L-function is its finite polynomial minus its boundary term,
plus the tail from the integer cutoff to infinity. -/
theorem LFunction_cutoff499 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    χ.LFunction (Thm4.half t) = partialSum N χ t - A χ N / (N : ℂ) ^ (Thm4.half t) +
      Thm4.half t * ∫ u in Ioi (N : ℝ), A χ u * (u : ℂ) ^ (-(Thm4.half t + 1)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi := tail_integrable499 hχ t 1 (by norm_num)
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi hN'
  rw [intervalIntegral.integral_of_le hN'] at he
  rw [LFunction_eq_integral hχ (by norm_num [Thm4.half]), partialSum_abel499 hχ t hN]
  rw [← he]
  simp only [Complex.cpow_neg, div_eq_mul_inv]
  ring
/-- Page 22, the absolute tail after a real cutoff is at most twice
q divided by the square root of the cutoff. -/
theorem tail_norm_le499 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t R : ℝ) (hR : 1 ≤ R) :
    ‖∫ u in Ioi R, A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))‖ ≤
      2 * q / Real.sqrt R := by
  have hR0 : 0 < R := by linarith
  have hmajor : IntegrableOn (fun u : ℝ => (q : ℝ) * u ^ (-(3 / 2 : ℝ))) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hR0).const_mul _
  have hb : ‖∫ u in Ioi R, A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))‖ ≤
      ∫ u in Ioi R, (q : ℝ) * u ^ (-(3 / 2 : ℝ)) := by
    refine norm_integral_le_of_norm_le hmajor ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hR0.trans hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have he : (-(Thm4.half t + 1)).re = -(3 / 2 : ℝ) := by norm_num [Thm4.half]
    rw [he]
    exact mul_le_mul_of_nonneg_right (norm_A_le hχ u) (Real.rpow_nonneg hu0.le _)
  have hv : (∫ u in Ioi R, (q : ℝ) * u ^ (-(3 / 2 : ℝ))) = 2 * q / Real.sqrt R := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hR0]
    norm_num only [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_neg hR0.le, ← Real.sqrt_eq_rpow]
    ring
  exact hv ▸ hb
/-- Page 22, the nonprincipal critical-line bound from a balanced cutoff. -/
theorem nonprincipal_norm499 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) :
    ‖χ.LFunction (Thm4.half t)‖ ≤ 7 * Real.sqrt ((q : ℝ) * (|t| + 1)) := by
  let Q : ℝ := (q : ℝ) * (|t| + 1)
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg t]
  have hQ0 : 0 < Q := by linarith
  let N : ℕ := ⌈Q⌉₊
  have hQN : Q ≤ (N : ℝ) := Nat.le_ceil Q
  have hN : 1 ≤ N := by exact_mod_cast (le_trans hQ hQN)
  have hN0 : 0 < N := by omega
  have hNupper : (N : ℝ) ≤ Q + 1 := (Nat.ceil_lt_add_one hQ0.le).le
  let D := Real.sqrt (N : ℝ)
  let E := Real.sqrt Q
  have hD0 : 0 < D := Real.sqrt_pos.mpr (by exact_mod_cast hN0)
  have hE0 : 0 < E := Real.sqrt_pos.mpr hQ0
  have hED : Q ≤ E * D := by
    have hle : E ≤ D := Real.sqrt_le_sqrt hQN
    have hs : E * E = Q := Real.mul_self_sqrt hQ0.le
    nlinarith [mul_le_mul_of_nonneg_left hle hE0.le]
  have hDle : D ≤ 2 * E := by
    calc D ≤ Real.sqrt (4 * Q) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * E := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num [E]
  have hqQ : (q : ℝ) ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg t]
  have hBD : (q : ℝ) / D ≤ E := (div_le_iff₀ hD0).mpr (hqQ.trans hED)
  have hTD : 2 * q * (|t| + 1) / D ≤ 2 * E := by
    apply (div_le_iff₀ hD0).mpr
    dsimp [Q] at hED
    nlinarith
  have hs : ‖Thm4.half t‖ ≤ |t| + 1 := by
    have hn := norm_add_le (1 / 2 : ℂ) ((t : ℂ) * I)
    norm_num [norm_mul] at hn
    unfold Thm4.half
    linarith
  have hB : ‖A χ N / (N : ℂ) ^ (Thm4.half t)‖ ≤ q / D := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hN0,
      show (Thm4.half t).re = (1 / 2 : ℝ) by simp [Thm4.half], ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_right (norm_A_le hχ (N : ℝ)) hD0.le
  have hT : ‖Thm4.half t * ∫ u in Ioi (N : ℝ), A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))‖ ≤
      2 * q * (|t| + 1) / D := by
    rw [norm_mul]
    calc _ ≤ (|t| + 1) * (2 * q / D) :=
        mul_le_mul hs (tail_norm_le499 hχ t N (by exact_mod_cast hN)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hS := TrivialC165.partialSum_norm_le (N : ℝ) (Nat.cast_nonneg N) χ t
  rw [LFunction_cutoff499 hχ t hN]
  calc _ ≤ ‖partialSum N χ t - A χ N / (N : ℂ) ^ (Thm4.half t)‖ +
        ‖Thm4.half t * ∫ u in Ioi (N : ℝ), A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))‖ := norm_add_le _ _
    _ ≤ (‖partialSum N χ t‖ + ‖A χ N / (N : ℂ) ^ (Thm4.half t)‖) +
        ‖Thm4.half t * ∫ u in Ioi (N : ℝ), A χ u * (u : ℂ) ^ (-(Thm4.half t + 1))‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (2 * D + q / D) + 2 * q * (|t| + 1) / D := add_le_add (add_le_add hS hB) hT
    _ ≤ 7 * E := by linarith
end LeanLab.BHP1997.Repair499Critical
