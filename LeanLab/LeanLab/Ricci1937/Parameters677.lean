import LeanLab.Ricci1937.BetaBar
import LeanLab.Ricci1937.Section2

/-!
Ricci 1937, auxiliary parameter checks for the fifth pair.
The schedule is new auxiliary data for the formulas on pages 78, 81, 89 and 90.
No sieve count or prime block construction is asserted.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Real Finset

noncomputable section

/-- Auxiliary continuation of the page 89 and 90 profile convention at masses 0.8698, 0.6043, 0.5719 and 0.4885.
The transition is bounded using omega 4.79. -/
def decomp677TauUpper : ℝ :=
  exp (-0.8698) + exp (-1.4741) + exp (-2.046) + exp (-2.5345) +
    exp (-3.023) + exp (-3.5115) + exp (-4) + exp (-4.4885) +
    exp (-4.8835) / (1 - exp (-0.24425))

/-- The auxiliary profile leaves a strict margin below one. -/
lemma decomp677_tau_upper : decomp677TauUpper < 0.9999 := by
  have h0 : exp (-0.8698 : ℝ) ≤ 1 / (2386433 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h1 : exp (-1.4741 : ℝ) ≤ 1 / (4367103 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h2 : exp (-2.046 : ℝ) ≤ 1 / (7736878 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h3 : exp (-2.5345 : ℝ) ≤ 1 / (12609942 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h4 : exp (-3.023 : ℝ) ≤ 1 / (20551282 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h5 : exp (-3.5115 : ℝ) ≤ 1 / (33488512 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h6 : exp (-4 : ℝ) ≤ 1 / (54548180 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h7 : exp (-4.4885 : ℝ) ≤ 1 / (88778239 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h8 : exp (-4.8835 : ℝ) ≤ 1 / (131490122 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have h9 : exp (-0.24425 : ℝ) ≤ 1 / (1276663 / 1000000 : ℝ) :=
    ricci_exp_neg_upper (by norm_num)
      (ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial]))
  have ht : exp (-4.8835 : ℝ) / (1 - exp (-0.24425)) ≤
      (1 / (131490122 / 1000000 : ℝ)) / (1 - 1 / (1276663 / 1000000 : ℝ)) :=
    div_le_div₀ (by positivity) h8 (by norm_num) (by linarith)
  unfold decomp677TauUpper
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ht ⊢
  linarith

/-- The transition ratio one over 121 is below exp of negative 4.79. -/
lemma decomp677_transition_ratio : (1 / 121 : ℝ) < exp (-4.79) := by
  have hsmall : exp (0.79 : ℝ) ≤ 2.204 := ricci_exp_upper_small (by norm_num)
    (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have hone : exp (1 : ℝ) ≤ 2.719 := by linarith [exp_one_lt_d9]
  have hfour : exp (4 : ℝ) ≤ 2.719 ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le hone 4
  have hsplit : exp (4.79 : ℝ) = exp 4 * exp 0.79 := by rw [← exp_add]; norm_num
  have hbound := mul_le_mul hfour hsmall (exp_pos _).le (by positivity)
  have h121 : exp (4.79 : ℝ) < 121 := by rw [hsplit]; nlinarith
  rw [exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (exp_pos _) h121

/-- The auxiliary scalar budget meets both strict cutoffs for two and 366. -/
theorem decomp677_candidate_scalar_budget :
    ∃ δ κ : ℝ, 1 / (3 : ℝ) < δ ∧
      1 / (367 : ℝ) < δ * (1 / 121) ∧ 0 < κ ∧
      δ * (1 + 2 * decomp677TauUpper) ≤ 1 - κ := by
  refine ⟨0.33335, 0.00001, by norm_num, by norm_num, by norm_num, ?_⟩
  have ht := decomp677_tau_upper
  linarith

/-- Page 78 beta bar tail for the auxiliary schedule, using twenty finite terms. -/
lemma decomp677_beta_tail {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.389) :
    (∑' k : ℕ, ricciBetaBarTerm q (4 + k)) < 0.01487 := by
  have hq413 : q ≤ 0.413 := by linarith
  have hsum := ricciBetaBar_summable hq0 hq413
  have hhead : (∑ k ∈ range 20, ricciBetaBarTerm q (4 + k)) ≤
      ∑ k ∈ range 20, ricciBetaBarTerm (0.389 : ℝ) (4 + k) := by
    apply sum_le_sum
    intro k hk
    have hk20 : k < 20 := mem_range.mp hk
    unfold ricciBetaBarTerm
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq _)
    interval_cases k <;> norm_num [Nat.factorial]
  have htail : Summable (fun k : ℕ => ricciBetaBarTerm q (24 + k)) := by
    have hs : Summable (fun k : ℕ => ricciBetaBarTerm q (4 + (20 + k))) :=
      hsum.comp_injective (fun i j h => by omega)
    simpa only [← Nat.add_assoc] using hs
  have hdom : Summable (fun k : ℕ => ricciBetaMajorant q 24 * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hmajor : Summable (fun k : ℕ => ricciBetaMajorant q (24 + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold ricciBetaMajorant; positivity)
      (ricciBetaMajorant_shift_le (by norm_num) hq0 hq413)
  have htaille := htail.tsum_le_tsum
    (fun k => ricciBetaBar_le_majorant (by omega : 4 ≤ 24 + k) hq0) hmajor
  have htailbound := ricciBetaMajorant_tail_le (B := 24) (by norm_num) hq0 hq413
  have h24 : ricciBetaMajorant q 24 ≤ ricciBetaMajorant (0.389 : ℝ) 24 := by
    unfold ricciBetaMajorant
    gcongr
  have h24div := div_le_div_of_nonneg_right h24 (by norm_num : (0 : ℝ) ≤ 1 - 0.86)
  have hnum : (∑ k ∈ range 20, ricciBetaBarTerm (0.389 : ℝ) (4 + k)) +
      ricciBetaMajorant (0.389 : ℝ) 24 / (1 - 0.86) < 0.01487 := by
    norm_num [sum_range_succ, ricciBetaBarTerm, ricciBetaMajorant, Nat.factorial]
  have hsplit : (∑' k : ℕ, ricciBetaBarTerm q (4 + k)) =
      (∑ k ∈ range 20, ricciBetaBarTerm q (4 + k)) +
        ∑' k : ℕ, ricciBetaBarTerm q (24 + k) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hsum.sum_add_tsum_nat_add 20).symm
  rw [hsplit]
  linarith

/-- The auxiliary schedule lies inside the certified beta parameter interval. -/
lemma decomp677_beta_parameter :
    0 ≤ (0.4885 : ℝ) ^ 2 * exp 0.4885 ∧
      (0.4885 : ℝ) ^ 2 * exp 0.4885 ≤ 0.389 := by
  have he : exp (0.4885 : ℝ) ≤ 1.62987 := ricci_exp_upper_small (by norm_num)
    (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  constructor
  · positivity
  · nlinarith

/-- The page 81 lower coefficient bracket is positive at the auxiliary schedule.
This is a scalar estimate and supplies no actual decreasing sieve blocks. -/
theorem decomp677_lower_coefficient_positive :
    0 < (Ebar3 (8698 / 10000) (6043 / 10000) (5719 / 10000) : ℝ) -
      ((0.8698 : ℝ) * 0.6043 ^ 2 * 0.5719 ^ 2 /
        (0.4885 ^ 5 * exp (3 * 0.4885))) *
        (∑' k : ℕ, ricciBetaBarTerm (0.4885 ^ 2 * exp 0.4885) (4 + k)) := by
  have htail := decomp677_beta_tail decomp677_beta_parameter.1 decomp677_beta_parameter.2
  have hexp : (4.329 : ℝ) ≤ exp (3 * 0.4885) := ricci_exp_lower (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have hfac : (0.8698 : ℝ) * 0.6043 ^ 2 * 0.5719 ^ 2 /
      (0.4885 ^ 5 * exp (3 * 0.4885)) ≤
      (0.8698 : ℝ) * 0.6043 ^ 2 * 0.5719 ^ 2 / (0.4885 ^ 5 * 4.329) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hmul := mul_lt_mul_of_pos_left htail
    (by positivity : 0 < (0.8698 : ℝ) * 0.6043 ^ 2 * 0.5719 ^ 2 /
      (0.4885 ^ 5 * exp (3 * 0.4885)))
  have hbound := mul_le_mul_of_nonneg_right hfac (by norm_num : (0 : ℝ) ≤ 0.01487)
  norm_num [Ebar3] at *
  linarith

/-- Page 78 condition 1.5 holds for the auxiliary tail mass. -/
lemma decomp677_theta_admissible :
    exp (0.4885 : ℝ) * (0.4885 * exp 1 / 2) ^ 2 < 1 ∧ 1 < exp (0.4885 : ℝ) :=
  ricci_theta_admissible (by norm_num) (by norm_num)

end
end LeanLab.Ricci1937
