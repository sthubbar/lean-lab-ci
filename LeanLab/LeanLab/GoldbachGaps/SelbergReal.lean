/-
P0030 Goldston 1990 pages 285 and 286, displays 2 and 4.
The integer window RH estimate extends to real windows by monotonicity of theta.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.GoldbachGaps.Decomp1520
import LeanLab.GoldbachGaps.Goldston1990Cor1Full

namespace LeanLab.GoldbachGaps.Decomp1520
open Real Chebyshev Finset Filter MeasureTheory

/-- A real window is controlled by its two neighboring integer lengths. -/
theorem jg_real_le_nat_windows {N w : ℝ} {M K : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (hKw : (K : ℝ) ≤ w) (hwK : w ≤ (K : ℝ) + 1) :
    JgL N w ≤ 2 * JgL M K + 2 * JgL M ((K : ℝ) + 1) + 2 * M := by
  have hpt : ∀ x : ℝ, (θ (x + w) - θ x - w) ^ 2 ≤
      2 * (θ (x + K) - θ x - K) ^ 2 +
      2 * (θ (x + ((K : ℝ) + 1)) - θ x - ((K : ℝ) + 1)) ^ 2 + 2 := by
    intro x
    have hlo : θ (x + K) ≤ θ (x + w) := theta_mono (by linarith)
    have hhi : θ (x + w) ≤ θ (x + ((K : ℝ) + 1)) := theta_mono (by linarith)
    by_cases hz : 0 ≤ θ (x + w) - θ x - w
    · have he : θ (x + w) - θ x - w ≤
          (θ (x + ((K : ℝ) + 1)) - θ x - ((K : ℝ) + 1)) + 1 := by linarith
      have hs := mul_self_le_mul_self hz he
      nlinarith [sq_nonneg (θ (x + ((K : ℝ) + 1)) - θ x - ((K : ℝ) + 1) - 1),
        sq_nonneg (θ (x + K) - θ x - K)]
    · have hz' : 0 ≤ -(θ (x + w) - θ x - w) := by linarith
      have he : -(θ (x + w) - θ x - w) ≤ -(θ (x + K) - θ x - K) + 1 := by linarith
      have hs := mul_self_le_mul_self hz' he
      nlinarith [sq_nonneg (θ (x + K) - θ x - K + 1),
        sq_nonneg (θ (x + ((K : ℝ) + 1)) - θ x - ((K : ℝ) + 1))]
  have hsum := intervalIntegral.integral_mono_on hN (jg_integrand_integrable w 1 N)
    ((((jg_integrand_integrable K 1 N).const_mul 2).add
      ((jg_integrand_integrable ((K : ℝ) + 1) 1 N).const_mul 2)).add intervalIntegrable_const)
    (fun x _ => hpt x)
  have hk : JgL N K ≤ JgL M K := by
    exact intervalIntegral.integral_mono_interval le_rfl hN hNM
      (Eventually.of_forall fun _ => sq_nonneg _) (jg_integrand_integrable K 1 M)
  have hk1 : JgL N ((K : ℝ) + 1) ≤ JgL M ((K : ℝ) + 1) := by
    exact intervalIntegral.integral_mono_interval le_rfl hN hNM
      (Eventually.of_forall fun _ => sq_nonneg _) (jg_integrand_integrable ((K : ℝ) + 1) 1 M)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hsum
  · simp only [smul_eq_mul] at hsum
    change JgL N w ≤ 2 * JgL N K + 2 * JgL N ((K : ℝ) + 1) + (N - 1) * 2 at hsum
    linarith
  all_goals first
    | exact ((jg_integrand_integrable K 1 N).const_mul 2).add
        ((jg_integrand_integrable ((K : ℝ) + 1) 1 N).const_mul 2)
    | exact (jg_integrand_integrable K 1 N).const_mul 2
    | exact (jg_integrand_integrable ((K : ℝ) + 1) 1 N).const_mul 2
    | exact intervalIntegrable_const

/-- Selberg display 4 on the sealed real range, conditional on RH only. -/
theorem selbergJ_of_rh (hRH : RiemannHypothesis) : ∃ A N₁ : ℝ, SelbergJ A N₁ := by
  obtain ⟨C, hC, hJ⟩ := LeanLab.GoldbachGaps.Goldston1990.jg_pointwise hRH
  refine ⟨10000 * (C + 1), Real.exp 1, ?_⟩
  intro N w hN hw hwN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact hN
  have hN1 : 1 ≤ N := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  set K : ℕ := ⌊w⌋₊ with hKdef
  set M : ℕ := ⌈4 * N⌉₊ with hMdef
  have hKlo : (K : ℝ) ≤ w := Nat.floor_le (by linarith)
  have hKhi : w < (K : ℝ) + 1 := Nat.lt_floor_add_one w
  have hK1 : 1 ≤ K := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hw)
  have hMlo : 4 * N ≤ M := Nat.le_ceil (4 * N)
  have hMhi : (M : ℝ) ≤ 5 * N := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 4 * N by positivity)
    dsimp [M]
    linarith
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hNM : N ≤ M := by linarith
  have hlogM : 1 ≤ Real.log M := hlog.trans (Real.log_le_log hNpos hNM)
  have hlogM3 : Real.log M ≤ 3 * Real.log N := by
    have h5 : Real.log 5 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      norm_num at *
      linarith
    calc
      Real.log M ≤ Real.log (5 * N) := Real.log_le_log (by positivity) hMhi
      _ = Real.log 5 + Real.log N := Real.log_mul (by norm_num) hNpos.ne'
      _ ≤ 3 * Real.log N := by linarith
  have hKs : K * K ≤ M := by
    have : (K : ℝ) * K ≤ M := by nlinarith
    exact_mod_cast this
  have hK1s : (K + 1) * (K + 1) ≤ M := by
    have hk : (K : ℝ) + 1 ≤ w + 1 := by linarith
    have hk' : (K : ℝ) + 1 ≤ 2 * w := by linarith
    have : ((K : ℝ) + 1) ^ 2 ≤ (2 * w) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hk' 2
    have : ((K : ℝ) + 1) * ((K : ℝ) + 1) ≤ M := by nlinarith
    exact_mod_cast this
  have hnat : ∀ k : ℕ, 1 ≤ k → k * k ≤ M →
      JgL M k ≤ 30 * C * k * M * Real.log M ^ 2 := by
    intro k hk hks
    have hb := hJ M k hk hks hlogM
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have he : 30 * C * (Real.log M ^ 2 / k) * ((k : ℝ) ^ 2 * M) =
        30 * C * k * M * Real.log M ^ 2 := by field_simp
    rw [he] at hb
    exact hb
  have hb := jg_real_le_nat_windows hN1 hNM hKlo hKhi.le
  have hb0 := hnat K hK1 hKs
  have hb1 := hnat (K + 1) (by omega) hK1s
  push_cast at hb1
  have hlogMsq : Real.log M ^ 2 ≤ 9 * Real.log N ^ 2 := by nlinarith
  have hML : (M : ℝ) * Real.log M ^ 2 ≤ 45 * N * Real.log N ^ 2 := by
    calc
      _ ≤ (5 * N) * (9 * Real.log N ^ 2) :=
        mul_le_mul hMhi hlogMsq (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hKL : 30 * C * (2 * (K : ℝ) + 1) ≤ 90 * C * w := by
    have : 2 * (K : ℝ) + 1 ≤ 3 * w := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hC]
  have hprod : 30 * C * (2 * (K : ℝ) + 1) * ((M : ℝ) * Real.log M ^ 2) ≤
      (90 * C * w) * (45 * N * Real.log N ^ 2) :=
    mul_le_mul hKL hML (by positivity) (by positivity)
  have hrest : (M : ℝ) ≤ 5 * w * N * Real.log N ^ 2 := by
    have hl2 : 1 ≤ Real.log N ^ 2 := by nlinarith
    calc
      (M : ℝ) ≤ 5 * N := hMhi
      _ ≤ 5 * w * N * Real.log N ^ 2 := by
        have : 1 ≤ w * Real.log N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hl2 (by linarith : 0 ≤ w)]
        nlinarith [mul_le_mul_of_nonneg_left this hNpos.le]
  have h0 : 0 ≤ w * N * Real.log N ^ 2 := by positivity
  nlinarith [mul_nonneg hC h0]

/-- The introduction interval conclusion via the real Selberg bound, conditional on RH only. -/
theorem goldbach_interval_of_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
      ∃ n : ℕ, Even n ∧ IsGoldbachSum n ∧ N ≤ n ∧ (n : ℝ) ≤ N + C * Real.log N ^ 2 := by
  obtain ⟨A, N₁, hS⟩ := selbergJ_of_rh hRH
  exact goldbach_interval_of_selbergJ hS

end LeanLab.GoldbachGaps.Decomp1520
