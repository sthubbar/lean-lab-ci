import LeanLab.LZCesaroShort.Sec5Envelope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/1606.00869v2 pages 10 and 11, Section 5.
The zero term estimate is CONDITIONAL ON the explicit Vinogradov Korobov PNT input.
The free lower case n in the printed final logarithm is read as N, as in the task61 decision.
-/

namespace LeanLab.LZCesaroShort

open Filter Finset
open scoped Chebyshev

/-- A comparison for the decay exponent on a factor two interval in logarithmic coordinates.
This is an auxiliary estimate for the page 11 PNT argument. -/
lemma korobov_rate_doubling {x y : ℝ} (hx : 4 ≤ x) (hlo : x / 2 ≤ y) (hhi : y ≤ 2 * x) :
    x ^ (3 / 5 : ℝ) * (Real.log x) ^ (-(1 / 5 : ℝ)) ≤
      4 * (y ^ (3 / 5 : ℝ) * (Real.log y) ^ (-(1 / 5 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hpow2 : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (2 : ℝ) ^ a ≤ 2 := by
    intro a _ ha
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha
  have ha : x ^ (3 / 5 : ℝ) ≤ 2 * y ^ (3 / 5 : ℝ) := by
    calc
      _ ≤ (2 * y) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow hx0.le (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ (3 / 5 : ℝ) * y ^ (3 / 5 : ℝ) :=
        Real.mul_rpow (by norm_num) hy0.le
      _ ≤ 2 * y ^ (3 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right (hpow2 _ (by norm_num) (by norm_num)) (by positivity)
  have hlog : Real.log y ≤ 2 * Real.log x := by
    have h1 := Real.log_le_log hy0 hhi
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ x)
    linarith
  have hb' : (Real.log y) ^ (1 / 5 : ℝ) ≤ 2 * (Real.log x) ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ (2 * Real.log x) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hly.le hlog (by norm_num)
      _ = (2 : ℝ) ^ (1 / 5 : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) :=
        Real.mul_rpow (by norm_num) hlx.le
      _ ≤ 2 * (Real.log x) ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right (hpow2 _ (by norm_num) (by norm_num)) (by positivity)
  have hb : (Real.log x) ^ (-(1 / 5 : ℝ)) ≤ 2 * (Real.log y) ^ (-(1 / 5 : ℝ)) := by
    rw [Real.rpow_neg hlx.le, Real.rpow_neg hly.le]
    have hxp : 0 < (Real.log x) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hlx _
    have hyp : 0 < (Real.log y) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hly _
    apply (mul_le_mul_iff_right₀ hyp).mp
    field_simp
    simpa [mul_comm] using hb'
  have h := mul_le_mul ha hb (by positivity) (by positivity)
  nlinarith

/-- The pointwise Vinogradov Korobov PNT error is uniform up to twice N after reducing c.
The cited PNT estimate remains an explicit hypothesis. -/
theorem psi_uniform_korobov_of_pointwise
    (hPNT : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |ψ (n : ℝ) - n| ≤ K * n * Real.exp
        (-c * (Real.log n) ^ (3 / 5 : ℝ) * (Real.log (Real.log n)) ^ (-(1 / 5 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, n ≤ 2 * N →
        |ψ (n : ℝ) - n| ≤ C * N * Real.exp
          (-c * (Real.log N) ^ (3 / 5 : ℝ) * (Real.log (Real.log N)) ^ (-(1 / 5 : ℝ))) := by
  obtain ⟨c, hc, K, n₀, hp⟩ := hPNT
  have htlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (2 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp htlog
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp (htlog.eventually_ge_atTop 4)
  obtain ⟨Npow, hNpow⟩ := eventually_atTop.mp (htpow.eventually_ge_atTop c)
  let C₀ : ℝ := Real.log 4 + 5
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨c / 4, by positivity, C₀ + 2 * |K|, by positivity,
    max (max Nlog Npow) (max (n₀ ^ 2) 4), fun N hN n hn => ?_⟩
  have hNlog' : Nlog ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNpow' : Npow ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNn₀ : n₀ ^ 2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : 4 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2N : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn
  let L := Real.log (N : ℝ)
  let F := L ^ (3 / 5 : ℝ) * (Real.log L) ^ (-(1 / 5 : ℝ))
  have hL4 : 4 ≤ L := hNlog N hNlog'
  have hL0 : 0 < L := by linarith
  have hlogL1 : 1 ≤ Real.log L := by
    apply (Real.le_log_iff_exp_le hL0).mpr
    have := Real.exp_one_lt_d9
    linarith
  have hFle : F ≤ L ^ (3 / 5 : ℝ) := by
    have h1 : (Real.log L) ^ (-(1 / 5 : ℝ)) ≤ 1 := by
      calc
        _ ≤ (Real.log L) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogL1 (by norm_num)
        _ = 1 := Real.rpow_zero _
    dsimp [F]
    exact mul_le_of_le_one_right (by positivity) h1
  have hcL : c ≤ L ^ (2 / 5 : ℝ) := hNpow N hNpow'
  have hpowid : L ^ (3 / 5 : ℝ) * L ^ (2 / 5 : ℝ) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hcF : c / 4 * F ≤ L / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hFle (by positivity : (0 : ℝ) ≤ c / 4)
    have h2 := mul_le_mul_of_nonneg_right hcL (by positivity : (0 : ℝ) ≤ L ^ (3 / 5 : ℝ))
    nlinarith
  have hsmall : Real.sqrt (N : ℝ) ≤ N * Real.exp (-(c / 4) * F) := by
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    calc
      _ = Real.exp (Real.log N / 2) := by
        rw [← Real.log_sqrt hN0.le, Real.exp_log hsN]
      _ ≤ Real.exp (Real.log N - c / 4 * F) :=
        Real.exp_le_exp.mpr (by change L / 2 ≤ L - c / 4 * F; linarith)
      _ = N * Real.exp (-(c / 4) * F) := by
        rw [show Real.log (N : ℝ) - c / 4 * F = Real.log N + (-(c / 4) * F) by ring,
          Real.exp_add, Real.exp_log hN0]
  have hNe : 0 ≤ (N : ℝ) * Real.exp (-(c / 4) * F) := by positivity
  change |ψ (n : ℝ) - n| ≤ (C₀ + 2 * |K|) * N * Real.exp
    (-(c / 4) * L ^ (3 / 5 : ℝ) * (Real.log L) ^ (-(1 / 5 : ℝ)))
  rw [mul_assoc (-(c / 4))]
  change |ψ (n : ℝ) - n| ≤ (C₀ + 2 * |K|) * N * Real.exp (-(c / 4) * F)
  rcases le_or_gt (n : ℝ) (Real.sqrt (N : ℝ)) with hns | hns
  · have hpsi := Chebyshev.psi_le_const_mul_self hn0
    have hpsi0 := Chebyshev.psi_nonneg (n : ℝ)
    have hlin : |ψ (n : ℝ) - n| ≤ C₀ * n := by
      rw [abs_le]
      dsimp [C₀]
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      constructor <;> nlinarith
    calc
      _ ≤ C₀ * n := hlin
      _ ≤ C₀ * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_left hns hC₀
      _ ≤ C₀ * (N * Real.exp (-(c / 4) * F)) := mul_le_mul_of_nonneg_left hsmall hC₀
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg K) hNe]
  · have hn₀r : (n₀ : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have hsq : (n₀ : ℝ) ^ 2 ≤ N := by exact_mod_cast hNn₀
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (Nat.cast_nonneg n₀)] at h
    have hn₀ : n₀ ≤ n := by exact_mod_cast (hn₀r.trans hns.le)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.sqrt_pos.mpr hN0) hns.le
    have hlo : L / 2 ≤ Real.log (n : ℝ) := by
      have h := Real.log_le_log (Real.sqrt_pos.mpr hN0) hns.le
      rwa [Real.log_sqrt hN0.le] at h
    have hhi : Real.log (n : ℝ) ≤ 2 * L := by
      have h := Real.log_le_log hnpos hn2N
      rw [Real.log_mul (by norm_num) hN0.ne'] at h
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      change Real.log (n : ℝ) ≤ 2 * Real.log N
      dsimp [L] at hL4
      linarith
    have hcomp := korobov_rate_doubling hL4 hlo hhi
    have hexp : Real.exp (-c * (Real.log n) ^ (3 / 5 : ℝ)
        * (Real.log (Real.log n)) ^ (-(1 / 5 : ℝ))) ≤ Real.exp (-(c / 4) * F) := by
      apply Real.exp_le_exp.mpr
      dsimp [F] at *
      nlinarith [mul_le_mul_of_nonneg_left hcomp hc.le]
    have hb := hp n hn₀
    calc
      _ ≤ |K| * n * Real.exp (-c * (Real.log n) ^ (3 / 5 : ℝ)
          * (Real.log (Real.log n)) ^ (-(1 / 5 : ℝ))) :=
        hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self K) hn0) (Real.exp_pos _).le)
      _ ≤ |K| * (2 * N) * Real.exp (-(c / 4) * F) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn2N (abs_nonneg K)) hexp
          (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hC₀ hNe]

/-- The normalized page 11 zero term rate, conditional on its cited pointwise PNT input. -/
theorem sec5_korobov_of_pointwise
    (hPNT : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |ψ (n : ℝ) - n| ≤ K * n * Real.exp
        (-c * (Real.log n) ^ (3 / 5 : ℝ) * (Real.log (Real.log n)) ^ (-(1 / 5 : ℝ)))) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N →
      ‖ZH N H / (H : ℂ)‖ ≤ K * (H * N * Real.exp
        (-c * (Real.log N) ^ (3 / 5 : ℝ) * (Real.log (Real.log N)) ^ (-(1 / 5 : ℝ))) + N) := by
  obtain ⟨c, hc, C, hC, Np, hp⟩ := psi_uniform_korobov_of_pointwise hPNT
  obtain ⟨Nz, K, hK, hz⟩ := zero_term_bound_of_psi_window
  refine ⟨c, hc, C + K, max Np Nz, fun N H hN hH hHN => ?_⟩
  have hpN := hp N (le_trans (le_max_left _ _) hN)
  have hwin : ∀ n ∈ Icc (N - H) (N + H), |ψ (n : ℝ) - n| ≤ C * N * Real.exp
      (-c * (Real.log N) ^ (3 / 5 : ℝ) * (Real.log (Real.log N)) ^ (-(1 / 5 : ℝ))) := by
    intro n hn
    exact hpN n (by have := (mem_Icc.mp hn).2; omega)
  have hb := hz N H (le_trans (le_max_right _ _) hN) hH hHN _ (by positivity) hwin
  have hA : 0 ≤ (H : ℝ) * N * Real.exp
      (-c * (Real.log N) ^ (3 / 5 : ℝ) * (Real.log (Real.log N)) ^ (-(1 / 5 : ℝ))) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show C ≤ C + K by linarith) hA
  have h2 := mul_le_mul_of_nonneg_right (show K ≤ C + K by linarith) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

end LeanLab.LZCesaroShort
