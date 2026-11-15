/-
P0093 pages 159 through 161. Comparison step of equation 6.1: on the arc of radius
one over q tau the principal square integral is replaced by the square integral of
the model series S one of equation 6.3, with the square root error term obtained by
the Cauchy Schwarz step of equation 5.3. Inputs: the mean square theorem
principal_arc_mean_square491, the principal mass principal_mass435 and the model
mass logFourier_mass491.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.PrincipalArcLeaf491
import LeanLab.Linnik1951.LogFourierMass491
import LeanLab.Linnik1951.SPLIT_mixed_bound491

namespace LeanLab.Linnik1951

open Finset MeasureTheory
open Filter
open scoped Topology

/-- Continuity of the model series S one of equation 6.3. -/
private lemma continuous_logFourier_arc491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m : ℕ => ‖logCoefficient520 N m‖)
    (fun m => by fun_prop) (logCoefficient_summable520 N hN).norm (fun m z => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Real algebra of the square root step. -/
private lemma sqrt_arc_le491 (N R C K L A B : ℝ) (hN : 0 < N) (hR : 0 < R) (hC : 0 < C)
    (hK : 0 < K) (hL : 1 ≤ L) (hA : A ≤ C * N / R * L ^ 13) (hB : B ≤ K * N) :
    Real.sqrt A * Real.sqrt B ≤ Real.sqrt (C * K) * N * L ^ 13 / Real.sqrt R := by
  have hL0 : 0 < L := by linarith
  have hX : 0 ≤ C * N / R * L ^ 13 := by positivity
  have h1 : Real.sqrt A * Real.sqrt B ≤
      Real.sqrt (C * N / R * L ^ 13) * Real.sqrt (K * N) :=
    mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  refine h1.trans ?_
  rw [← Real.sqrt_mul hX]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hR.le]
  rw [le_div_iff₀ hR]
  have hL13 : (1 : ℝ) ≤ L ^ 13 := one_le_pow₀ hL
  have e : C * N / R * L ^ 13 * (K * N) * R = C * K * N ^ 2 * L ^ 13 := by
    field_simp
  rw [e]
  have hp : 0 ≤ C * K * N ^ 2 * L ^ 13 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL13 hp]

/-- P0093 page 160 equation 6.1. On the arc the principal square integral is the square integral of the model series S one up to the square root error term, by the Cauchy Schwarz step of equation 5.3. The print keeps the contour integral here and passes to S one only at equation 6.3; this file passes to S one already on the arc. -/
theorem principal_arc_compare491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨C1, hC1, N1, hms⟩ := principal_arc_mean_square491 hG
  obtain ⟨P0, hP0, hmass⟩ := principal_mass435
  refine ⟨Real.sqrt (C1 * (2 * P0 + 4)), Real.sqrt_pos.mpr (by positivity),
    max 128 N1, ?_⟩
  intro N hN q hq hqQ n
  have hN128 : 128 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN3 : 3 ≤ N := by omega
  have hl : 1 ≤ Real.log N := by
    have hN3' : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3').le
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold principalIntegral491
  set R : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by
    have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN128.le
      have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn
        (by norm_num : (0 : ℝ) ≤ 1 / 7)
      have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
        rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rwa [he] at hh
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    dsimp [R]
    nlinarith
  set r : ℝ := 1 / R with hrdef
  have hr : 0 < r := by positivity
  have hrh : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR2
  have hrr : -r ≤ r := by linarith
  have : NeZero q := ⟨by omega⟩
  set Pf : ℝ → ℂ := characterPrime280 (1 : DirichletCharacter ℂ q) N with hPf
  set F : ℝ → ℂ := logFourier520 N with hF
  have hpc : Continuous Pf := continuous_character_prime357 (1 : DirichletCharacter ℂ q) N (by omega)
  have hfc : Continuous F := continuous_logFourier_arc491 N (by omega)
  have hec : Continuous (fun z : ℝ =>
      Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hdc : Continuous (fun z => Pf z - F z) := hpc.sub hfc
  have hsc : Continuous (fun z => Pf z + F z) := hpc.add hfc
  -- step 1: the difference is bounded by the integral of the product of norms
  have hstep1 : ‖(∫ z in -r..r, Pf z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
      ∫ z in -r..r, F z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in -r..r, ‖Pf z - F z‖ * ‖Pf z + F z‖ := by
    have hi1 : IntervalIntegrable (fun z : ℝ => Pf z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) volume (-r) r :=
      ((hpc.pow 2).mul hec).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun z : ℝ => F z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) volume (-r) r :=
      ((hfc.pow 2).mul hec).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1 hi2]
    refine (intervalIntegral.norm_integral_le_integral_norm hrr).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr (fun z _ => ?_)
    rw [show Pf z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) -
        F z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) =
        (Pf z - F z) * (Pf z + F z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) by ring,
      norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- step 2: Cauchy Schwarz
  have hdLp : MemLp (fun z => Pf z - F z) 2 (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mpr
      ((hdc.norm.pow 2).intervalIntegrable (-r) r).1
  have hsLp : MemLp (fun z => Pf z + F z) 2 (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hsc.aestronglyMeasurable).mpr
      ((hsc.norm.pow 2).intervalIntegrable (-r) r).1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc (-r) r))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (Filter.Eventually.of_forall (fun z => norm_nonneg (Pf z - F z)))
    (Filter.Eventually.of_forall (fun z => norm_nonneg (Pf z + F z)))
    (by norm_num; exact hdLp.norm) (by norm_num; exact hsLp.norm)
  norm_num only [Real.rpow_two] at hcs
  simp_rw [← Real.sqrt_eq_rpow] at hcs
  rw [← intervalIntegral.integral_of_le hrr, ← intervalIntegral.integral_of_le hrr,
    ← intervalIntegral.integral_of_le hrr] at hcs
  -- step 3: the two masses
  have hA : (∫ z in -r..r, ‖Pf z - F z‖ ^ 2) ≤ C1 * (N : ℝ) / R * Real.log N ^ 13 :=
    hms N hN1 q hq hqQ
  have hp : (∫ z in -r..r, ‖Pf z‖ ^ 2) ≤ P0 * ((N : ℝ) / Real.log N) :=
    hmass N q r hN3 hr.le hrh
  have hf : (∫ z in -r..r, ‖F z‖ ^ 2) ≤ 2 * (N : ℝ) :=
    logFourier_mass491 N (by omega) r hr.le hrh
  have hB : (∫ z in -r..r, ‖Pf z + F z‖ ^ 2) ≤ (2 * P0 + 4) * (N : ℝ) := by
    have hpi : IntervalIntegrable (fun z : ℝ => ‖Pf z‖ ^ 2) volume (-r) r :=
      (hpc.norm.pow 2).intervalIntegrable (-r) r
    have hfi : IntervalIntegrable (fun z : ℝ => ‖F z‖ ^ 2) volume (-r) r :=
      (hfc.norm.pow 2).intervalIntegrable (-r) r
    have hmono : (∫ z in -r..r, ‖Pf z + F z‖ ^ 2) ≤
        ∫ z in -r..r, (2 * ‖Pf z‖ ^ 2 + 2 * ‖F z‖ ^ 2) := by
      refine intervalIntegral.integral_mono_on hrr
        ((hsc.norm.pow 2).intervalIntegrable _ _)
        ((hpi.const_mul 2).add (hfi.const_mul 2)) (fun z _ => ?_)
      have h := norm_add_le (Pf z) (F z)
      have h0 := norm_nonneg (Pf z + F z)
      nlinarith [sq_nonneg (‖Pf z‖ - ‖F z‖)]
    rw [intervalIntegral.integral_add (hpi.const_mul 2) (hfi.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    have hdiv : (N : ℝ) / Real.log N ≤ N := div_le_self hNp.le hl
    have := mul_le_mul_of_nonneg_left hdiv hP0.le
    linarith
  have hfinal := sqrt_arc_le491 (N : ℝ) R C1 (2 * P0 + 4) (Real.log N) _ _ hNp hRp hC1
    (by positivity) hl hA hB
  exact hstep1.trans (hcs.trans hfinal)

end LeanLab.Linnik1951
