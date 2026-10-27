import LeanLab.GoldbachAverage.GSTheorem3Identity
import LeanLab.GoldbachAverage.LZTheorem1RH

/-!
P0051 arXiv 2110.14250v2, Theorem 3 eq. 21 page 4.
Cauchy Schwarz bounds the psi error by the nonnegative error majorant.
The kernel contributes one logarithm. No cited analytic input is used.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage
open Complex Finset MeasureTheory Set Filter
open LeanLab.LZCesaroShort LeanLab.PNTPort.Vinogradov

/-- Continuous functions belong to every Lp space on a finite real interval. -/
lemma continuous_memLp_Ioc (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (p : ENNReal) :
    MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x ⟨hx.1.le, hx.2⟩

/-- Weighted Cauchy Schwarz for a complex integral on the unit interval. -/
theorem norm_integral_mul_sq_le (f k : ℝ → ℂ) (hf : Continuous f) (hk : Continuous k) :
    ‖∫ x in (0 : ℝ)..1, f x * k x‖ ^ 2 ≤
      (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 * ‖k x‖) * (∫ x in (0 : ℝ)..1, ‖k x‖) := by
  set A : ℝ → ℝ := fun x => ‖f x‖ * Real.sqrt ‖k x‖ with hA
  set B : ℝ → ℝ := fun x => Real.sqrt ‖k x‖ with hB
  have hAc : Continuous A := hf.norm.mul hk.norm.sqrt
  have hBc : Continuous B := hk.norm.sqrt
  have hA0 : ∀ x, 0 ≤ A x := fun x => by dsimp [A]; positivity
  have hB0 : ∀ x, 0 ≤ B x := fun x => Real.sqrt_nonneg _
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Eventually.of_forall hA0) (Eventually.of_forall hB0)
    (continuous_memLp_Ioc A hAc 0 1 (ENNReal.ofReal 2))
    (continuous_memLp_Ioc B hBc 0 1 (ENNReal.ofReal 2))
  norm_num only [Real.rpow_two] at hh
  have hA2 : ∀ x, A x ^ 2 = ‖f x‖ ^ 2 * ‖k x‖ := by
    intro x
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hB2 : ∀ x, B x ^ 2 = ‖k x‖ := fun x => Real.sq_sqrt (norm_nonneg _)
  have hAB : ∀ x, A x * B x = ‖f x‖ * ‖k x‖ := by
    intro x
    dsimp [A, B]
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  simp_rw [hA2, hB2, hAB] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hcs : (∫ x in (0 : ℝ)..1, ‖f x‖ * ‖k x‖) ≤
      Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 * ‖k x‖) *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖k x‖) := by
    simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hh
  have hn : ‖∫ x in (0 : ℝ)..1, f x * k x‖ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ * ‖k x‖ := by
    simpa only [norm_mul] using
      (intervalIntegral.norm_integral_le_integral_norm (a := (0 : ℝ)) (b := 1)
        (f := fun x => f x * k x) (by norm_num))
  have he0 : 0 ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 * ‖k x‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by positivity)
  have hg0 : 0 ≤ ∫ x in (0 : ℝ)..1, ‖k x‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  have h := pow_le_pow_left₀ (norm_nonneg _) (hn.trans hcs) 2
  rwa [mul_pow, Real.sq_sqrt he0, Real.sq_sqrt hg0] at h

/-- The comparison kernel norm is periodic with period one. -/
lemma kernel_norm_periodic (N : ℕ) (rho : ℝ) :
    Function.Periodic (fun α => ‖IGenN N rho (-α)‖) 1 := by
  intro α
  apply congrArg norm
  unfold IGenN
  apply sum_congr rfl
  intro n _
  rw [show -(α + 1) * n = -α * n + ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring,
    eAdd_add_int]

/-- The integral of the kernel norm at the exponential radius. -/
def kernelMass (N : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖IGenN N (1 / Real.exp (-(1 / (N : ℝ)))) (-α)‖

/-- The comparison kernel has L1 mass at most 120 log N. -/
theorem kernel_mass_bound (N : ℕ) (hN2 : 2 ≤ N) : kernelMass N ≤ 120 * Real.log N := by
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set g : ℝ → ℝ := fun α => ‖IGenN N (1 / Real.exp (-(1 / (N : ℝ)))) (-α)‖ with hg
  have hgc : Continuous g := continuous_IGenN_norm N _
  set M := Nat.log 2 N + 1 with hM
  have hKM : (N : ℝ) ≤ 2 ^ M := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    exact_mod_cast this.le
  have hb := integral_G_le (H := N) (K := M) hN hKM
    (f := fun _ => (1 : ℝ)) continuous_const (fun _ => zero_le_one) hgc
    (c := 6) (by norm_num)
    (fun α hα => norm_IGenN_le hN (abs_le.mpr ⟨hα.1, hα.2⟩))
  have hlayer : ∀ k ∈ range (M + 1),
      6 * (2 * (N : ℝ) / 2 ^ k) * (∫ α in (-xi N k)..(xi N k), (1 : ℝ)) ≤ 24 := by
    intro k _
    have hxi := xi_le N k
    have hA : 2 * (N : ℝ) / 2 ^ k * xi N k ≤ 2 := by
      have hxN : xi N k * N ≤ 2 ^ k := (le_div_iff₀ hN0).mp hxi
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [intervalIntegral.integral_const, smul_eq_mul]
    nlinarith only [hA]
  have hs := sum_le_sum hlayer
  rw [sum_const, card_range, nsmul_eq_mul] at hs
  have hcount : (M : ℝ) + 1 ≤ 5 * Real.log N := by
    have h := natLog_le N hN
    have h23 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    have hL2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2r
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hdiv : Real.log N / Real.log 2 ≤ 2 * Real.log N := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [hM]
    push_cast
    linarith
  have hsym := (kernel_norm_periodic N (1 / Real.exp (-(1 / (N : ℝ))))).intervalIntegral_add_eq
    (-(1 / 2 : ℝ)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at hsym
  unfold kernelMass
  rw [← hsym]
  have hstep : (∫ α in (-(1 / 2 : ℝ))..(1 / 2), g α) ≤ (M + 1) * (24 : ℝ) := by
    have h := hb.trans hs
    simpa only [mul_one, Nat.cast_add, Nat.cast_one] using h
  push_cast at hstep
  exact hstep.trans (by nlinarith only [hcount])

/-- The nonnegative error majorant of P0051 eq. 18. -/
def Emajorant (N : ℕ) (r : ℝ) : ℝ := ∫ α in (0 : ℝ)..1, ‖FE N r α‖

lemma Emajorant_eq (N : ℕ) (r : ℝ) : Emajorant N r =
    ∫ α in (0 : ℝ)..1, ‖PsiGen r α - IGen r α‖ ^ 2 * ‖IGenN N (1 / r) (-α)‖ := by
  simp only [Emajorant, FE, norm_mul, norm_pow]

lemma Emajorant_nonneg (N : ℕ) (r : ℝ) : 0 ≤ Emajorant N r :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)

/-- The complex error is bounded by the paper's nonnegative majorant. -/
theorem norm_EGS_le_Emajorant (N : ℕ) (r : ℝ) : ‖EGS N r‖ ≤ Emajorant N r := by
  simpa only [EGS, Emajorant, FE] using
    (intervalIntegral.norm_integral_le_integral_norm (a := (0 : ℝ)) (b := 1)
      (f := FE N r) (by norm_num))

/-- The majorant can be integrated on the symmetric unit interval. -/
lemma Emajorant_eq_sym (N : ℕ) (r : ℝ) : Emajorant N r =
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖FE N r α‖ := by
  have hp : Function.Periodic (fun α => ‖FE N r α‖) 1 := by
    intro α
    exact congrArg norm (FE_periodic N r α)
  have hs := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at hs
  exact hs.symm

/-- Psi minus I is continuous at an admissible radius. -/
lemma continuous_psi_sub_I {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun α => PsiGen r α - IGen r α) := by
  have hc : ∀ n : ℕ, Continuous (fun α => tm r α n) := by
    intro n
    exact continuous_const.mul (continuous_eAdd_mul n)
  have ht := continuous_tsum hc (summable_geom_poly hr0.le hr1)
    (fun n α => norm_tm_le hr0.le α n)
  exact ht.congr (fun α => (psi_sub_I hr0.le hr1 α).symm)

/-- The error integrand is continuous at every admissible radius. -/
lemma continuous_FE (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : Continuous (FE N r) := by
  have hk : Continuous (fun α => IGenN N (1 / r) (-α)) := by unfold IGenN eAdd; fun_prop
  exact ((continuous_psi_sub_I hr0 hr1).pow 2).mul hk

/-- Theorem 3 eq. 21 in squared form, with an explicit constant. -/
theorem gs_theorem3_bound_sq (N : ℕ) (hN : 2 ≤ N) :
    (Chebyshev.psi N - N) ^ 2 ≤
      120 * Emajorant N (Real.exp (-(1 / (N : ℝ)))) * Real.log N := by
  set r := Real.exp (-(1 / (N : ℝ))) with hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := one_div_pos.mpr hN0
    linarith
  have hk : Continuous (fun α => IGenN N (1 / r) (-α)) := by unfold IGenN eAdd; fun_prop
  have hcs := norm_integral_mul_sq_le (fun α => PsiGen r α - IGen r α)
    (fun α => IGenN N (1 / r) (-α)) (continuous_psi_sub_I hr0 hr1) hk
  rw [← gs_theorem3_identity N hr0 hr1, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Emajorant_eq N r] at hcs
  have hm := kernel_mass_bound N hN
  have he0 := Emajorant_nonneg N r
  have hmul := mul_le_mul_of_nonneg_left hm he0
  have hmul' : Emajorant N r * kernelMass N ≤ 120 * Emajorant N r * Real.log N := by
    calc _ ≤ Emajorant N r * (120 * Real.log N) := hmul
      _ = _ := by ring
  change (Chebyshev.psi N - N) ^ 2 ≤ Emajorant N r * kernelMass N at hcs
  exact hcs.trans hmul'

/-- Theorem 3 eq. 21 with constant square root 120. -/
theorem gs_theorem3_bound (N : ℕ) (hN : 2 ≤ N) :
    |Chebyshev.psi N - N| ≤ Real.sqrt 120 *
      Real.sqrt (Emajorant N (Real.exp (-(1 / (N : ℝ)))) * Real.log N) := by
  have hsq := gs_theorem3_bound_sq N hN
  have he0 := Emajorant_nonneg N (Real.exp (-(1 / (N : ℝ))))
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have h : |Chebyshev.psi N - N| ≤
      Real.sqrt (120 * (Emajorant N (Real.exp (-(1 / (N : ℝ)))) * Real.log N)) := by
    apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
    rw [sq_abs]
    nlinarith only [hsq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 120)] at h
  exact h

end LeanLab.GoldbachAverage
