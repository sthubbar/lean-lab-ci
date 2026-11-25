import LeanLab.ChenDoubleSieve.Decomp348a
import LeanLab.LZPowersOfTwo.Burst8PNT

/-!
Wu 2004 pages 38 and 39, the passage from the sieve main terms with pi of N to the
main terms with N over log N in equations 10.2 and 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
The prime number theorem for `Nat.primeCounting` is derived here from the lab's
proved `theta_div_tendsto_one_p2`, which rests on the closed port `MediumPNT`,
together with Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO`.
A generic comparison then handles every main term whose remaining factor is
eventually bounded, and gives the Upsilon 0 comparison of Decomp348a directly,
since f is continuous at the limit level 6.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S148
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The prime number theorem, pi of x times log x over x tends to one, real form.
From theta of x over x tends to one and pi of x minus theta of x over log x being
big O of x over log x squared. -/
theorem primeCounting_log_div_tendsto_real :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x / x) atTop (𝓝 1) := by
  have hO := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have h1 : (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / log x) *
      (log x / x)) =O[atTop] (fun x : ℝ => x / log x ^ 2 * (log x / x)) :=
    hO.mul (Asymptotics.isBigO_refl _ _)
  have h2 : (fun x : ℝ => x / log x ^ 2 * (log x / x)) =ᶠ[atTop] fun x => (log x)⁻¹ := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl := log_pos hx
    have hx0 : x ≠ 0 := by positivity
    field_simp
  have h4 : Tendsto (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ) -
      Chebyshev.theta x / log x) * (log x / x)) atTop (𝓝 0) :=
    (h1.trans_eventuallyEq h2).trans_tendsto tendsto_log_atTop.inv_tendsto_atTop
  have h5 := h4.add LeanLab.LZPowersOfTwo.Burst8P2.theta_div_tendsto_one_p2
  rw [zero_add] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl := log_pos hx
  have hx0 : (0 : ℝ) < x := by linarith
  field_simp
  ring

/-- The prime number theorem for `Nat.primeCounting` along the naturals, the
statement of the LEAF `primeCounting_pnt` in Feed1122_S120_main4_compare. -/
theorem primeCounting_pnt_proved :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) * log N / N) atTop (𝓝 1) := by
  refine (primeCounting_log_div_tendsto_real.comp tendsto_natCast_atTop_atTop).congr ?_
  intro N
  simp [Nat.floor_natCast]

/-- The algebraic identity behind each comparison: the difference of the two main
terms is the prime number theorem error times the normalised density times the
remaining factor times Theta of N. -/
theorem compare_identity' (S : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) / log N * lowerDensity N * S - (Nat.primeCounting N : ℝ) * lowerDensity N * S
      = (1 - (Nat.primeCounting N : ℝ) * log N / N) * scaledDensity N * S * Θ N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']

/-- Wu 2004 pages 38 and 39, the replacement of pi of N by N over log N in a sieve
main term whose remaining factor is eventually bounded: the difference is at most
eta Theta N on large even N, with the bound on the factor needed only on large
even N. From the prime number theorem above and the proved
`scaledDensity_tendsto` of Decomp348a. -/
theorem compare_of_bounded (S : ℕ → ℝ) (C : ℝ) (hS : ∀ᶠ N : ℕ in evenAtTop, |S N| ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |(N : ℝ) / log N * lowerDensity N * S N
        - (Nat.primeCounting N : ℝ) * lowerDensity N * S N| ≤ η * Θ N := by
  intro η hη
  set L : ℝ := 2 / (kappa1 * exp eulerMascheroniConstant)
  set K : ℝ := |L| + 1 with hK
  have hKpos : 0 < K := by positivity
  set C' : ℝ := |C| + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  have hεpos : 0 < η / (K * C') := by positivity
  have hsd : ∀ᶠ N in evenAtTop, |scaledDensity N| ≤ K := by
    have hlt : ∀ᶠ N in evenAtTop, scaledDensity N ∈ Metric.ball L 1 :=
      scaledDensity_tendsto (Metric.ball_mem_nhds L one_pos)
    filter_upwards [hlt] with N hN
    rw [Metric.mem_ball, Real.dist_eq] at hN
    have := abs_sub_abs_le_abs_sub (scaledDensity N) L
    linarith
  have hpnt : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) * log N / N ∈ Metric.ball (1 : ℝ) (η / (K * C')) :=
    primeCounting_pnt_proved (Metric.ball_mem_nhds 1 hεpos)
  have hle : evenAtTop ≤ atTop := inf_le_left
  have hall : ∀ᶠ N in evenAtTop, Even N ∧ 2 ≤ N ∧ |scaledDensity N| ≤ K ∧
      (Nat.primeCounting N : ℝ) * log N / N ∈ Metric.ball (1 : ℝ) (η / (K * C')) ∧
      |S N| ≤ C := by
    have hev : ∀ᶠ N in evenAtTop, Even N := mem_inf_of_right (mem_principal_self _)
    filter_upwards [hev, hle (eventually_ge_atTop 2), hsd, hle hpnt, hS]
      with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hall' := (eventually_inf_principal.1 hall)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hall'
  refine ⟨N0, fun N hE hN => ?_⟩
  obtain ⟨-, h2, h3, h4, h5⟩ := hN0 N hN hE
  rw [compare_identity' _ h2]
  rw [Metric.mem_ball, Real.dist_eq] at h4
  have hΘ := Θ_nonneg N
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hΘ]
  have e1 : |1 - (Nat.primeCounting N : ℝ) * log N / N| ≤ η / (K * C') := by
    rw [abs_sub_comm]; exact h4.le
  have e3 : |S N| ≤ C' := by
    have := le_abs_self C; linarith
  have hprod : |1 - (Nat.primeCounting N : ℝ) * log N / N| * |scaledDensity N| * |S N| ≤
      η / (K * C') * K * C' := by
    apply mul_le_mul (mul_le_mul e1 h3 (abs_nonneg _) hεpos.le) e3 (abs_nonneg _)
    positivity
  have heq : η / (K * C') * K * C' = η := by field_simp
  rw [heq] at hprod
  exact mul_le_mul_of_nonneg_right hprod hΘ

/-- Wu 2004 page 38: the sifting function f at the residual level of divisor one
stays bounded, since the level tends to 6 by `lowerLevel_one_tendsto` and f is
continuous on the positive reals by the linear sieve specification of Lemma 2.2. -/
theorem f_lowerLevel_one_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, |f (lowerLevel B N 1)| ≤ |f 6| + 1 := by
  have hf : ContinuousOn f (Ioi 0) := by
    unfold IsLinearSieve at h; exact h.2.1
  have hc : ContinuousAt f 6 := hf.continuousAt (Ioi_mem_nhds (by norm_num))
  have ht := hc.tendsto.comp (lowerLevel_one_tendsto B)
  have := ht (Metric.ball_mem_nhds (f 6) one_pos)
  filter_upwards [this] with N hN
  simp only [Set.mem_preimage, Function.comp_apply, Metric.mem_ball, Real.dist_eq] at hN
  have := abs_sub_abs_le_abs_sub (f (lowerLevel B N 1)) (f 6)
  linarith

/-- Wu 2004 page 38, the statement of the LEAF `main0_compare` in
Feed1122_Decomp348a_main0_lower: replacing pi of N by N over log N in the
Upsilon 0 main term costs at most eta Theta N for large even N. -/
theorem main0_compare_proved (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |(N : ℝ) / log N *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - (Nat.primeCounting N : ℝ) *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))| ≤ η * Θ N := by
  intro η hη B _
  exact compare_of_bounded (fun N => f (lowerLevel B N 1)) _
    ((inf_le_left : evenAtTop ≤ atTop) (f_lowerLevel_one_bounded F f h B)) η hη

end LeanLab.ChenDoubleSieve.Feed1122.S148
