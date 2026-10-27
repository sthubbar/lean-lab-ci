import LeanLab.GoldbachAverage.InghamTheta
import LeanLab.GoldbachAverage.BSPOmega

/-!
The missing integer transfer in P0050, arXiv 0806.3295v3 pages 4 and 5.
Large Goldbach counts are an explicit hypothesis. This file does not assert that input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.OmegaTransfer82
open Complex Finset Filter
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.LZCesaroShort

/-- The integrated explicit formula and Goldbach use the same zero sum.
Source: P0051 eq. 42 page 8 and P0050 page 4. -/
theorem Wf_eq_Z1 (x : ℝ) : Wf x = Z1 x := by
  rw [Wf, Z1, zeroSum]
  have e : (∑' ρ : Zall, wterm x ρ.1) =
      ∑' ρ : NontrivialZero, wterm x ρ.1 := by
    rw [Zall_eq]
    rfl
  rw [e]
  rfl

/-- Under RH a unit step of the zero sum is O of square root x times log squared x.
Source: the integer transfer mentioned on P0050 page 4. -/
theorem Z1_unit_step (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 6 ≤ N → ‖Z1 N - Z1 (N - 1 : ℕ)‖ ≤
      C * (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log N + 1) ^ 2 := by
  obtain ⟨D1, D2, hD1, hD2, hb⟩ := dW_bound hRH
  refine ⟨2 * D1 + 8 * D2, by positivity, fun N hN => ?_⟩
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hstep := hb N hNr (N - 1) N (by linarith) (by linarith) (by linarith)
  rw [Wf_eq_Z1, Wf_eq_Z1] at hstep
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast]
  have hp : (2 * (N : ℝ)) ^ ((1 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hN0.le]
    have htwo : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  have he : (2 * (N : ℝ)) ^ ((3 : ℝ) / 2) =
      (2 * N) * (2 * N) ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring, Real.rpow_add (by positivity), Real.rpow_one]
  rw [he] at hstep
  have hf : (2 * (N : ℝ)) * (2 * N) ^ ((1 : ℝ) / 2) *
      (2 * D2 * (Real.log N + 1) / N) =
      4 * D2 * (Real.log N + 1) * (2 * N) ^ ((1 : ℝ) / 2) := by
    field_simp
    ring
  rw [hf, show (N : ℝ) - ((N : ℝ) - 1) = 1 by ring, one_mul] at hstep
  have h1 := mul_le_mul_of_nonneg_right hp (show 0 ≤ D1 * (Real.log N + 1) ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * D2 * (Real.log N + 1) by positivity)
  have h3 : Real.log N + 1 ≤ (Real.log N + 1) ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3
    (show 0 ≤ 8 * D2 * (N : ℝ) ^ ((1 : ℝ) / 2) by positivity)
  nlinarith

/-- The Goldbach summand is controlled by two adjacent errors and a zero sum difference.
Source: P0050 page 4, the discrete version of the jump argument. -/
theorem G_le_adjacent_errors (N : ℕ) :
    G (N + 1) ≤ E (N + 1) + E N + (N : ℝ) + 1 / 2 +
      2 * ‖Z1 (N + 1 : ℕ) - Z1 N‖ := by
  set A : ℕ → ℂ := fun n =>
    ((∑ j ∈ range (n + 1), G j : ℝ) : ℂ) - (n : ℂ) ^ 2 / 2 + 2 * Z1 n
  have he : (G (N + 1) : ℂ) = A (N + 1) - A N + ((N : ℂ) + 1 / 2) -
      2 * (Z1 (N + 1 : ℕ) - Z1 N) := by
    dsimp [A]
    rw [sum_range_succ]
    push_cast
    ring
  have hn : ‖(G (N + 1) : ℂ)‖ = G (N + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G_nonneg _)]
  have h := norm_sub_le (A (N + 1) - A N + ((N : ℂ) + 1 / 2))
    (2 * (Z1 (N + 1 : ℕ) - Z1 N))
  have h1 := norm_add_le (A (N + 1) - A N) ((N : ℂ) + 1 / 2)
  have h2 := norm_sub_le (A (N + 1)) (A N)
  rw [← he, hn, norm_mul, Complex.norm_two] at h
  have hmain : ‖(N : ℂ) + 1 / 2‖ = (N : ℝ) + 1 / 2 := by
    have hcast : (N : ℂ) + 1 / 2 = ((N : ℝ) + 1 / 2 : ℝ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hmain] at h1
  change G (N + 1) ≤ ‖A (N + 1)‖ + ‖A N‖ + (N : ℝ) + 1 / 2 + _
  linarith

/-- Under RH the zero sum changes by at most N across a unit step, eventually.
Source: P0050 page 4, the integer transfer mentioned after the real jump argument. -/
theorem Z1_unit_step_eventually (hRH : RiemannHypothesis) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖Z1 N - Z1 (N - 1 : ℕ)‖ ≤ (N : ℝ) := by
  obtain ⟨C, hC, hb⟩ := Z1_unit_step hRH
  obtain ⟨N₀, hN₀⟩ := GSCor2.eventually_le_rpow (4 * C) (1 / 2) 1 2
    (by norm_num) 1 (by norm_num)
  refine ⟨max N₀ 6, fun N hN => ?_⟩
  have hN6 : 6 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN6
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < N)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := hb N hN6
  have h2 : (Real.log N + 1) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2) by positivity)
  have h4 := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.rpow_one, one_mul] at h4
  nlinarith

/-- Large integer Goldbach counts imply the integer omega statement under RH.
Source: P0050 pages 4 and 5. The large count input is stated as a hypothesis.
This theorem does not prove the Gallagher large sieve density input. -/
theorem bsp_omega_of_large_values (hRH : RiemannHypothesis)
    (hlarge : ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      c * N * Real.log (Real.log N) ≤ G N) : ¬ ErrSmallO := by
  intro hsmall
  obtain ⟨c, hc, hlarge⟩ := hlarge
  obtain ⟨N₁, h₁⟩ := hsmall (c / 8) (by positivity)
  obtain ⟨N₂, h₂⟩ := Z1_unit_step_eventually hRH
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₃, h₃⟩ := eventually_atTop.mp (hll.eventually_ge_atTop (12 / c))
  obtain ⟨N, hN, hGN⟩ := hlarge (max (max (N₁ + 1) N₂) (max N₃ 6))
  have hN1 : N₁ + 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN6 : 6 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hloglog : Real.log (Real.log (N - 1 : ℕ)) ≤ Real.log (Real.log N) := by
    have hNm : (1 : ℝ) < (N - 1 : ℕ) := by
      rw [hcast]
      have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN6
      linarith
    apply Real.log_le_log (Real.log_pos hNm)
    apply Real.log_le_log (by linarith)
    rw [hcast]
    linarith
  have hllN := h₃ N hN3
  have hll0 : 0 < Real.log (Real.log N) := lt_of_lt_of_le (by positivity) hllN
  have hE1 := h₁ N (by omega)
  have hE0 := h₁ (N - 1) (by omega)
  have hE0' : E (N - 1) ≤ c / 8 * N * Real.log (Real.log N) := by
    refine hE0.trans ?_
    calc c / 8 * (N - 1 : ℕ) * Real.log (Real.log (N - 1 : ℕ))
        ≤ c / 8 * (N - 1 : ℕ) * Real.log (Real.log N) := by gcongr
      _ ≤ c / 8 * N * Real.log (Real.log N) := by gcongr; omega
  have hG := G_le_adjacent_errors (N - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at hG
  have hzero := h₂ N hN2
  have hlinear : 3 * (N : ℝ) ≤ c / 4 * N * Real.log (Real.log N) := by
    have hcll : 12 ≤ c * Real.log (Real.log N) := by
      rw [div_le_iff₀ hc] at hllN
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hcll hN0.le
    nlinarith
  rw [hcast] at hG hzero
  have hcn : 0 < c * (N : ℝ) * Real.log (Real.log N) := by positivity
  nlinarith

end LeanLab.GoldbachAverage.OmegaTransfer82
