/-
P0069 Baker Harman Pintz 1997, page 22, the principal critical line.
The zeta cutoff formula supplies the principal-character estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.StrongPNT.ZetaBounds
import LeanLab.BHP1997.Repair499Critical

namespace LeanLab.BHP1997.Repair499Principal
open Classical Complex MeasureTheory Set Finset MeanValue132
/-- Page 22, the elementary bound for each finite Euler factor. -/
theorem euler_factor_le499 {p : ℕ} (hp : p.Prime) (t : ℝ) :
    ‖1 - (p : ℂ) ^ (-Thm4.half t)‖ ≤
      (if p = 2 then (2 : ℝ) else 1) * Real.sqrt p := by
  have hr : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hr2 : (Real.sqrt (p : ℝ)) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have hb : ‖1 - (p : ℂ) ^ (-Thm4.half t)‖ ≤ 1 + 1 / Real.sqrt p := by
    calc _ ≤ 1 + ‖(p : ℂ) ^ (-Thm4.half t)‖ := by simpa using norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-Thm4.half t))
      _ = _ := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos]
        simp only [neg_re, show (Thm4.half t).re = (1 / 2 : ℝ) by simp [Thm4.half]]
        rw [Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow, one_div]
  refine hb.trans ?_
  rw [show (1 : ℝ) + 1 / Real.sqrt p = (Real.sqrt p + 1) / Real.sqrt p by field_simp]
  apply (div_le_iff₀ hr).mpr
  split_ifs with h
  · have hp2 : (p : ℝ) = 2 := by exact_mod_cast h
    nlinarith [sq_nonneg (Real.sqrt (p : ℝ) - 1)]
  · have hp3 : (3 : ℝ) ≤ p := by
      have : 3 ≤ p := by have := hp.two_le; omega
      exact_mod_cast this
    nlinarith [sq_nonneg (Real.sqrt (p : ℝ) - 1)]

/-- Page 22, the finite Euler product for a principal character is bounded
by twice the square root of its modulus on the critical line. -/
theorem euler_product_le499 (q : ℕ) (hq : 1 ≤ q) (t : ℝ) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-Thm4.half t))‖ ≤ 2 * Real.sqrt q := by
  let P : ℝ := ∏ p ∈ q.primeFactors, Real.sqrt p
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hPsq : P ^ 2 = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    dsimp [P]
    rw [← Finset.prod_pow]
    simp only [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_prod]
  have hPl : P ≤ Real.sqrt q := by
    apply (Real.le_sqrt hP0 (Nat.cast_nonneg q)).mpr
    rw [hPsq]
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) (Nat.prod_primeFactors_dvd q)
  have htwo : (∏ p ∈ q.primeFactors, if p = 2 then (2 : ℝ) else 1) ≤ 2 := by
    rw [Finset.prod_ite_eq']
    split_ifs <;> norm_num
  rw [norm_prod]
  calc _ ≤ ∏ p ∈ q.primeFactors, (if p = 2 then (2 : ℝ) else 1) * Real.sqrt p :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p hp => euler_factor_le499 (Nat.prime_of_mem_primeFactors hp) t)
    _ = (∏ p ∈ q.primeFactors, if p = 2 then (2 : ℝ) else 1) * P := by rw [Finset.prod_mul_distrib]
    _ ≤ 2 * P := mul_le_mul_of_nonneg_right htwo hP0
    _ ≤ 2 * Real.sqrt q := mul_le_mul_of_nonneg_left hPl (by norm_num)
/-- Page 22, a balanced Euler-Maclaurin cutoff bounds zeta on the critical line. -/
theorem zeta_norm499 (t : ℝ) :
    ‖riemannZeta (Thm4.half t)‖ ≤ 12 * Real.sqrt (|t| + 1) := by
  let T : ℝ := |t| + 1
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT0 : 0 < T := by linarith
  let N : ℕ := ⌈T⌉₊
  have hTN : T ≤ (N : ℝ) := Nat.le_ceil T
  have hN : 1 ≤ N := by exact_mod_cast (le_trans hT1 hTN)
  have hNp : 0 < N := by omega
  have hNu : (N : ℝ) ≤ T + 1 := (Nat.ceil_lt_add_one hT0.le).le
  let D := Real.sqrt (N : ℝ)
  let E := Real.sqrt T
  have hD0 : 0 < D := Real.sqrt_pos.mpr (by exact_mod_cast hNp)
  have hE0 : 0 < E := Real.sqrt_pos.mpr hT0
  have hED : T ≤ E * D := by
    have hle : E ≤ D := Real.sqrt_le_sqrt hTN
    have hs : E * E = T := Real.mul_self_sqrt hT0.le
    nlinarith [mul_le_mul_of_nonneg_left hle hE0.le]
  have hDle : D ≤ 2 * E := by
    calc D ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * E := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num [E]
  have hTD : 2 * T / D ≤ 2 * E := by
    apply (div_le_iff₀ hD0).mpr
    nlinarith
  let s := Thm4.half t
  have hsre : s.re = (1 / 2 : ℝ) := by simp [s, Thm4.half]
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; simp only [hsre, one_re] at this; norm_num at this
  have hsn : ‖s‖ ≤ T := by
    have hn := norm_add_le (1 / 2 : ℂ) ((t : ℂ) * I)
    norm_num [norm_mul] at hn
    dsimp [s, Thm4.half, T]
    linarith
  have hfinite : ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ ≤ 2 * D := by
    have he : (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) =
        partialSum N (1 : DirichletCharacter ℂ 1) t := by
      rw [Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
      simp only [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc]
      simp only [partialSum, Nat.floor_natCast]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Subsingleton.elim (k : ZMod 1) 1, map_one]
    rw [he]
    exact TrivialC165.partialSum_norm_le N (Nat.cast_nonneg N) 1 t
  have hden : (1 / 2 : ℝ) ≤ ‖1 - s‖ := by
    have hn := Complex.abs_re_le_norm (1 - s)
    simpa only [sub_re, one_re, hsre, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] using hn
  have hP1 : ‖(-(N : ℂ) ^ (1 - s)) / (1 - s)‖ ≤ 2 * D := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNp]
    simp only [sub_re, one_re, hsre, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    have hb := div_le_div_of_nonneg_left (Real.sqrt_nonneg (N : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) hden
    convert hb using 1 <;> ring
  have hP2 : ‖(-(N : ℂ) ^ (-s)) / 2‖ ≤ E := by
    rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNp]
    simp only [neg_re, hsre, norm_ofNat]
    rw [Real.rpow_neg (Nat.cast_nonneg N), ← Real.sqrt_eq_rpow]
    change D⁻¹ / 2 ≤ E
    rw [← one_div]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ hD0).mpr
    nlinarith
  have hI : ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ 2 / D := by
    have hb := ZetaBnd_aux1b N hN (σ := (1 / 2 : ℝ)) (t := t) (by norm_num)
    simpa [D, s, Thm4.half, Real.rpow_neg (Nat.cast_nonneg N), Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hb
  have htail : ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤ 2 * T / D := by
    rw [norm_mul]
    calc _ ≤ T * (2 / D) := mul_le_mul hsn hI (norm_nonneg _) hT0.le
      _ = _ := by ring
  rw [← Zeta0EqZeta hNp (by rw [hsre]; norm_num) hs1, riemannZeta0]
  refine (norm_add₄_le).trans ?_
  have hh := add_le_add (add_le_add (add_le_add hfinite hP1) hP2) htail
  exact hh.trans (by linarith)
/-- Page 22, a principal character has the same critical-line scale
as the finite Euler product times the zeta cutoff estimate. -/
theorem principal_norm499 {q : ℕ} [NeZero q] (hq : 1 ≤ q) (t : ℝ) :
    ‖(1 : DirichletCharacter ℂ q).LFunction (Thm4.half t)‖ ≤
      24 * Real.sqrt ((q : ℝ) * (|t| + 1)) := by
  have hs1 : Thm4.half t ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [Thm4.half] at this
  change ‖DirichletCharacter.LFunctionTrivChar q (Thm4.half t)‖ ≤ _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1, norm_mul]
  calc _ ≤ (2 * Real.sqrt q) * (12 * Real.sqrt (|t| + 1)) :=
      mul_le_mul (euler_product_le499 q hq t) (zeta_norm499 t) (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg q)]; ring
end LeanLab.BHP1997.Repair499Principal
