/-
AI wrote the Lean code. CODEX task139, 2026-10-27.
Source: https://arxiv.org/pdf/2012.06322, printed pages 5, 8 and 9.
These are checks of the displayed estimates. Paper conclusions remain QUESTIONS.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.Audit139

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139

noncomputable section

/-- Page 5, S2 display. Balancing its two terms gives the reconstructed exponent. -/
theorem tail_balance139 (γ n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    tailBudget γ n y (n ^ (-γ / 3) * y ^ ((2 : ℝ) / 3)) =
      2 * (n ^ (1 - 2 * γ / 3) * y ^ ((1 : ℝ) / 3)) := by
  let H : ℝ := n ^ (-γ / 3) * y ^ ((2 : ℝ) / 3)
  have hH : 0 < H := by dsimp [H]; positivity
  have h₁ : H ^ ((1 : ℝ) / 2) * n ^ (1 - γ / 2) =
      n ^ (1 - 2 * γ / 3) * y ^ ((1 : ℝ) / 3) := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    dsimp [H]
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow]
    ring
  have h₂ : H⁻¹ * y * n ^ (1 - γ) =
      n ^ (1 - 2 * γ / 3) * y ^ ((1 : ℝ) / 3) := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    dsimp [H]
    simp (disch := positivity) only [Real.log_mul, Real.log_inv, Real.log_rpow]
    ring
  change H ^ ((1 : ℝ) / 2) * n ^ (1 - γ / 2) + H⁻¹ * y * n ^ (1 - γ) = _
  rw [h₁, h₂]
  ring

/-- Page 8, QUESTION Q139a. The printed S2 term exceeds every constant multiple of
the claimed target along admissible windows at gamma 89/90 and epsilon 1/100. -/
theorem printed_tail_not_dominated139 (C N : ℝ) :
    ∃ m : ℕ, N ≤ (m : ℝ) ∧
      (m : ℝ) ^ songExponent (89 / 90) < (m : ℝ) / 3 ∧
      C * ((m : ℝ) ^ ((21 : ℝ) / 31 - 14 * (89 / 90) / 31 + 1 / 100) *
        ((m : ℝ) / 3) ^ ((23 : ℝ) / 31)) <
      (m : ℝ) ^ (1 - ((89 : ℝ) / 90) / 3) * ((m : ℝ) / 3) ^ ((1 : ℝ) / 3) := by
  let δ : ℝ := (1 - ((89 : ℝ) / 90) / 3) + 1 / 3 -
    ((21 : ℝ) / 31 - 14 * (89 / 90) / 31 + 1 / 100) - 23 / 31
  let k : ℝ := (3 : ℝ) ^ ((23 : ℝ) / 31 - 1 / 3)
  have hδ : 0 < δ := by norm_num [δ]
  have hk : 0 < k := by dsimp [k]; positivity
  have hθ : 0 < 1 - songExponent (89 / 90) := by
    rw [songExponent_89_90]
    norm_num
  have hgood : ∀ᶠ m : ℕ in Filter.atTop,
      N ≤ (m : ℝ) ∧ 1 ≤ (m : ℝ) ∧
      3 < (m : ℝ) ^ (1 - songExponent (89 / 90)) ∧ max C 0 / k < (m : ℝ) ^ δ := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop N,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ),
      ((_root_.tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 3,
      ((_root_.tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
        (max C 0 / k)] with m hN hn hW hD
    exact ⟨hN, hn, hW, hD⟩
  obtain ⟨m, hN, hn, hW, hD⟩ := hgood.exists
  let n : ℝ := m
  change N ≤ n at hN
  change 1 ≤ n at hn
  change 3 < n ^ (1 - songExponent (89 / 90)) at hW
  change max C 0 / k < n ^ δ at hD
  have hn0 : 0 < n := by linarith
  have hwin : n ^ songExponent (89 / 90) < n / 3 := by
    have he : n ^ songExponent (89 / 90) * n ^ (1 - songExponent (89 / 90)) = n := by
      rw [← Real.rpow_add hn0,
        show songExponent (89 / 90) + (1 - songExponent (89 / 90)) = 1 by ring,
        Real.rpow_one]
    have hp := Real.rpow_pos_of_pos hn0 (songExponent (89 / 90))
    nlinarith [mul_lt_mul_of_pos_left hW hp]
  have hratio : C < n ^ δ * k := (le_max_left C 0).trans_lt ((div_lt_iff₀ hk).mp hD)
  have he : n ^ (1 - ((89 : ℝ) / 90) / 3) * (n / 3) ^ ((1 : ℝ) / 3) =
      (n ^ δ * k) * (n ^ ((21 : ℝ) / 31 - 14 * (89 / 90) / 31 + 1 / 100) *
        (n / 3) ^ ((23 : ℝ) / 31)) := by
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    dsimp [δ, k]
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div]
    ring
  refine ⟨m, hN, hwin, ?_⟩
  rw [he]
  exact mul_lt_mul_of_pos_right hratio (by positivity)

/-- Page 9, Section 4. Combining the displayed powers at the exact window leaves epsilon. -/
theorem threshold_exponent_loss139 (γ ε : ℝ) :
    (21 / 31 - 14 * γ / 31 + ε) + (1 - γ) -
      (8 / 31) * songExponent γ = ε := by
  unfold songExponent
  ring

/-- Page 9, Section 4. A positive power loss cannot supply an inverse fourth log bound. -/
theorem positive_power_not_log_saving139 (ε : ℝ) (hε : 0 < ε) (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C / Real.log (n : ℝ) ^ 4 < (n : ℝ) ^ ε := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ε) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ n : ℕ in Filter.atTop,
      N ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧ max C 0 < (n : ℝ) ^ ε := by
    filter_upwards [Filter.eventually_ge_atTop N, hlog.eventually_ge_atTop 1,
      hpow.eventually_gt_atTop (max C 0)] with n hN hL hP
    exact ⟨hN, hL, hP⟩
  obtain ⟨n, hN, hL, hP⟩ := hgood.exists
  have hden : 1 ≤ Real.log (n : ℝ) ^ 4 := one_le_pow₀ hL
  have hdiv : C / Real.log (n : ℝ) ^ 4 ≤ max C 0 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (n : ℝ) ^ 4)).mpr
    have hm : 0 ≤ max C 0 := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hden hm
    nlinarith [le_max_left C 0]
  exact ⟨n, hN, hdiv.trans_lt hP⟩


/-- Page 9, QUESTION Q139c. Separate epsilon bounds do not imply a uniform logarithmic saving. -/
theorem all_epsilon_bounds_not_log_saving139 :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 : ℝ) ≤ C * (n : ℝ) ^ ε) ∧
    ¬ (∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (1 : ℝ) ≤ C / Real.log (n : ℝ) ^ 4) := by
  constructor
  · intro ε hε
    refine ⟨1, 1, fun n hn => ?_⟩
    simpa only [one_mul] using Real.one_le_rpow (by exact_mod_cast hn) hε.le
  · rintro ⟨C, N, h⟩
    have hlim : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hgood : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n ∧ max 1 (C + 1) < Real.log (n : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop N, hlim.eventually_gt_atTop (max 1 (C + 1))]
        with n hn hL
      exact ⟨hn, hL⟩
    obtain ⟨n, hn, hL⟩ := hgood.exists
    have hL1 : 1 < Real.log (n : ℝ) := (le_max_left _ _).trans_lt hL
    have hLC : C + 1 < Real.log (n : ℝ) := (le_max_right _ _).trans_lt hL
    have hs2 : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
    have hs4 : Real.log (n : ℝ) ^ 2 ≤ Real.log (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (Real.log (n : ℝ) ^ 2 - 1)]
    have hd : 0 < Real.log (n : ℝ) ^ 4 := by positivity
    have hb := (le_div_iff₀ hd).mp (h n hn)
    nlinarith

/-- Page 9, QUESTION Q139c. A positive additional window margin removes the epsilon power loss. -/
theorem threshold_exponent_margin139 (γ δ : ℝ) (hδ : 0 < δ) :
    (21 / 31 - 14 * γ / 31 + 4 * δ / 31) + (1 - γ) -
      (8 / 31) * (songExponent γ + δ) < 0 := by
  unfold songExponent
  linarith

end

end LeanLab.Song2020.Audit139

#print axioms LeanLab.Song2020.Audit139.tail_balance139
#print axioms LeanLab.Song2020.Audit139.printed_tail_not_dominated139
#print axioms LeanLab.Song2020.Audit139.threshold_exponent_loss139
#print axioms LeanLab.Song2020.Audit139.positive_power_not_log_saving139

#print axioms LeanLab.Song2020.Audit139.all_epsilon_bounds_not_log_saving139

#print axioms LeanLab.Song2020.Audit139.threshold_exponent_margin139
