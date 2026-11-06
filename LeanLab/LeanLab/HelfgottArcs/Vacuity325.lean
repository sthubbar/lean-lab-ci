/-
Concrete joint hypothesis instances for CODEX task325.
These examples do not assume the three open analytic estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.TypeIPartial325
import LeanLab.HelfgottArcs.Mobius325
import LeanLab.HelfgottArcs.Approximation325
import LeanLab.HelfgottArcs.Vacuity119

namespace LeanLab.HelfgottArcs
open Finset Set
open Decomp119

example := partial_summation_bound325 (fun _ => (1 : ℝ)) (fun _ => (1 : ℂ)) 8 8
  (by intro k hk; simpa using (show (k : ℝ) ≤ 8 by exact_mod_cast hk))
example := unimodal_variation_bound325 (fun _ => (1 : ℝ)) 8 0 (by norm_num)
  (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
example := unimodal_partial_sum_bound325 (fun _ => (1 : ℝ)) (fun _ => (1 : ℂ))
  8 0 (by norm_num) 8 (by norm_num)
  (by intro k hk; simpa using (show (k : ℝ) ≤ 8 by exact_mod_cast hk))
  (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
example := weighted_phase_variation325 (fun _ => (1 : ℝ)) (1 / 4) 3 8 (by norm_num [round])
example := unimodal_phase_bound325 (fun _ => (1 : ℝ)) (1 / 4) 3 8 0
  (by norm_num [round]) (by norm_num) (by intros; norm_num)
  (by intros; norm_num) (by intros; norm_num)
example := eta2_monotone_left325 (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
example := eta2_antitone_right325 (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) (by norm_num)
example := eta2_between325 (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num)
example := sampled_weight_phase_bound325 (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) monotone_const
  1 (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
  (1 / 4) 3 8 (by norm_num [round])
example := eta2_sampled_phase_bound325 (fun _ => (1 / 2 : ℝ)) monotone_const
  (1 / 4) 3 8 (by norm_num [round])
example := eta2rho_monotone_left325 (ρ := 4) le_rfl (a := 1 / 4) (b := 1 / 2)
  (by norm_num) (by norm_num) (by norm_num)
example := eta2rho_antitone_right325 (ρ := 4) le_rfl (a := 1 / 2) (b := 1)
  (by norm_num) (by norm_num) (by norm_num)
example := eta2rho_between325 (ρ := 4) le_rfl (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num)
example := eta2rho_sampled_phase_bound325 (ρ := 4) le_rfl
  (fun _ => (1 / 2 : ℝ)) monotone_const (1 / 4) 3 8 (by norm_num [round])
example := odd_phase_norm325 (fun _ => (1 : ℝ)) (1 / 8) 8
example := odd_eta2_phase_bound325 (1 / 8) (1 / 8) (by norm_num) 8 (by norm_num [round])
example := odd_log_eta2_phase_bound325 16 1 (1 / 8) (by norm_num) (by norm_num) 8
  (by norm_num [round])
example := eta2_sampled_length_bound325 (fun _ => (1 / 2 : ℝ)) 0 3 8
example := minor_odd_eta2_block325 2.16e20 (1 / 4000000) 1 2000000 0
  Vacuity119.main_parameters.1 {0, 1} 0
  (by intro n hn; simp only [Finset.mem_insert, Finset.mem_singleton] at hn; rcases hn with rfl | rfl <;> norm_num)
  (by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    have hh : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = (6e6 : ℝ) ^ (2 : ℕ) := by
      calc
        _ = ((2.16e20 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 1
          norm_num
        _ = _ := by rw [MinorQAMGM.x0_cbrt]
    rcases hn with rfl | rfl <;> norm_num [hh]) 8

open Mobius325
example := coprimeMu_multiplicative 6
example := coprimeMu_zeta_prime_pow 6 5 2 (by norm_num)
example := coprimeMu_zeta_values 6 10
example := coprimeMu_abs 6 5
example := coprimeMu_zeta_zero_of_coprime 6 5 (by norm_num) (by norm_num)
example := coprimeMu_complement_bound 6 5 (by norm_num)
example := coprimeMu_floor_sum 6 10
example := reciprocal_floor_identity (fun n => (n : ℝ)) 10
example := coprime_mobius_reciprocal_bound 6 10
example := granville_ramare_10_2 10 6
example := first_approximation_endpoint325
example := reset_disjunction_counterexample325

example := parameter_product325 16 (by norm_num)
example := parameter_product_exceeds_short_range325 16 (by norm_num)
example := first_denominator_exceeds_reset325

end LeanLab.HelfgottArcs
