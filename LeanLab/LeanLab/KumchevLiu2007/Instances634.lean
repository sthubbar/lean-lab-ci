/-
Concrete instances for all sixteen new Task634 statements.
Sources and plain math twins are in STATEMENTS.md.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.InitialRange634
import LeanLab.KumchevLiu2007.Gallagher634
import LeanLab.KumchevLiu2007.Endpoint634
import LeanLab.KumchevLiu2007.KernelBounds634
import LeanLab.KumchevLiu2007.LargeEpsilon634
import LeanLab.KumchevLiu2007.CharacterBounds634
import LeanLab.KumchevLiu2007.Decomp542a
import LeanLab.KumchevLiu2007.Decomp557c

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
example : LeanLab.BHP1997.Gallagher605.frequencyWindow ({0} : Finset ℕ)
    (fun _ => (1 : ℂ)) (fun _ => (0 : ℝ)) 1 =ᵐ[volume]
      fun t => ∑ _m ∈ ({0} : Finset ℕ).filter
        (fun _ => t < (0 : ℝ) ∧ 0 ≤ t + 1), (1 : ℂ) := by
  exact Task634.frequencyWindow_ae_strict _ _ _ _
example : (∫ t : ℝ, ‖LeanLab.BHP1997.Gallagher605.frequencyWindow
    ({0} : Finset ℕ) (fun _ => (1 : ℂ)) (fun _ => (0 : ℝ)) 1 t‖ ^ 2) =
      ∫ t in (-1 : ℝ)..0, ‖∑ _m ∈ ({0} : Finset ℕ).filter
        (fun _ => t < (0 : ℝ) ∧ 0 ≤ t + 1), (1 : ℂ)‖ ^ 2 := by
  simpa using Task634.frequencyWindow_energy_interval ({0} : Finset ℕ)
    (fun _ => (1 : ℂ)) (fun _ => (0 : ℝ)) 1 0 0 (by norm_num) le_rfl
    (by intro m hm; exact ⟨le_rfl, le_rfl⟩)
example : (∫ β in (-(1 / (2 : ℝ)))..(1 / 2),
    ‖Task556d.roughSum 16 1 β‖ ^ 2) ≤ (π / 2) ^ 2 *
      ((∫ t in (3 : ℝ)..4, ‖Task556a.roughShortSum 16 1 1 0 t‖ ^ 2) +
        ∫ t in (4 : ℝ)..16, ‖Task556a.roughShortSum 16 1 1 0 t‖ ^ 2) := by
  have h := Task634.roughSum_gallagher 16 1 1 0 (by norm_num)
  norm_num only [zero_add, mul_one] at h
  exact h

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
example : ∃ H M : ℝ,
    (2 : ℝ) ^ (7 / 18 + 1 / 10 : ℝ) ≤ H ∧
      H ≤ (2 : ℝ) ^ (1 - 1 / 10 : ℝ) ∧ 0 ≤ M ∧
        ∀ β ∈ Set.Icc (0 : ℝ) 1,
          Task556d.kernelMass (Task556a.windowY 2 (1 / 10)) H (Real.log 2 ^ (1 : ℝ)) β ≤ M := by
  let H : ℝ := (2 : ℝ) ^ (1 - 1 / 10 : ℝ)
  let Y : ℝ := Task556a.windowY 2 (1 / 10)
  have hH : 0 < H := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨H, H * ((Task556a.squareWindow Y).card : ℝ) ^ 2, ?_, le_rfl,
    mul_nonneg hH.le (sq_nonneg _), ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · intro β _
    exact (Task634.kernelMass_trivial_bounds Y (Real.log 2 ^ (1 : ℝ)) H β hH).2
#check Task634.singleton_endpoint_energy 1 (by norm_num)

open LeanLab.KumchevLiu2007
example : Task129.windowPairs 4 16 3 = ∅ :=
  Task634.windowPairs_empty_below 4 16 (by norm_num) 3 (by norm_num)
example : Task129.err53 4 (17 / 6) 1 3 = 0 := by
  apply Task634.err53_vanish_below
  · exact Real.rpow_nonneg (by norm_num) _
  · norm_num [Task129.windowY, show (7 / 12 + (17 / 6 : ℝ) / 2 : ℝ) = 2 by norm_num,
      Real.rpow_two]
#check Task634.eventually_large_window 1 (by norm_num)
#check Task634.eq53_very_large_eps 1 1 1 (by norm_num)

open LeanLab.KumchevLiu2007
example : Task557a.primitiveMax 2 (1 : DirichletCharacter ℂ 1) ≤ Chebyshev.psi 2 :=
  Task634.primitiveMax_le_psi 2 _
#check Task634.maximal_character_mean_trivial 2 (by norm_num) 1 (by norm_num)

open LeanLab.KumchevLiu2007
#check Task634.maximal_character_mean_log_range (Real.exp 2)
  (by have h := Real.add_one_le_exp (2 : ℝ); linarith)
  1 (by norm_num) (by norm_num)

#print axioms LeanLab.KumchevLiu2007.Task634.frequencyWindow_ae_strict
#print axioms LeanLab.KumchevLiu2007.Task634.frequencyWindow_energy_interval
#print axioms LeanLab.KumchevLiu2007.Task634.roughSum_gallagher
#print axioms LeanLab.KumchevLiu2007.Task634.singleton_endpoint_energy
#print axioms LeanLab.KumchevLiu2007.Task634.kernelMass_trivial_bounds
#print axioms LeanLab.KumchevLiu2007.Task634.windowPairs_empty_below
#print axioms LeanLab.KumchevLiu2007.Task634.err53_vanish_below
#print axioms LeanLab.KumchevLiu2007.Task634.eventually_large_window
#print axioms LeanLab.KumchevLiu2007.Task634.eq53_very_large_eps
#print axioms LeanLab.KumchevLiu2007.Task634.primitiveMax_le_psi
#print axioms LeanLab.KumchevLiu2007.Task634.maximal_character_mean_trivial
#print axioms LeanLab.KumchevLiu2007.Task634.maximal_character_mean_log_range
#print axioms LeanLab.KumchevLiu2007.Eq33RouteB.gallagher_roughSum
#print axioms LeanLab.KumchevLiu2007.Task556d.minor_mean_square_of_kernel
#print axioms LeanLab.KumchevLiu2007.Task542a.maximal_bombieri_vinogradov
#print axioms LeanLab.KumchevLiu2007.Task557b.maximal_psi_bv
#print axioms LeanLab.KumchevLiu2007.Task542a.weighted_maximal_bombieri_vinogradov
#print axioms LeanLab.KumchevLiu2007.Task542a.prime_window_weighted_bv
#print axioms LeanLab.KumchevLiu2007.Task542a.bv_remainder_from_maximal
#print axioms LeanLab.KumchevLiu2007.Task557c.maximal_bombieri_vinogradov
#print axioms LeanLab.KumchevLiu2007.Eq33RouteB.A23_initial_range
#print axioms LeanLab.KumchevLiu2007.Eq33RouteB.kernel_mass_of_A23_route
#print axioms LeanLab.KumchevLiu2007.Task556d.kernel_mass_of_A23
#print axioms LeanLab.KumchevLiu2007.Task556d.minor_arc_transference_from_kernel

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
#check Task634.roughShortSum_initial_norm_le 16 1 4 0 3 (by norm_num) (by norm_num) (by norm_num)
#check Task634.initial_energy_prefix_bound 16 1 4 0 (by norm_num) (by norm_num)
#check Task634.initial_energy_small 16 1 4 0 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : (2 : ℕ) ∈ (Task556a.squareWindow 16).filter
    (fun m : ℕ => (3 : ℝ) < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ 3 + 4) := by
  norm_num [Task556a.squareWindow]
example : (∫ t in (Task556a.windowY (Real.exp 1800) (1 / 18) / 4 - Real.exp 800)..
    (Task556a.windowY (Real.exp 1800) (1 / 18) / 4),
      ‖Task556a.roughShortSum (Task556a.windowY (Real.exp 1800) (1 / 18))
        (Real.log (Real.exp 1800) ^ (1 : ℝ)) (Real.exp 800) 0 t‖ ^ 2) ≤
          4 * (Real.exp 800) ^ 2 / Real.log (Real.exp 1800) ^ (1 + 2 : ℝ) := by
  have hX : 2 ≤ Real.exp 1800 := by
    have h := Real.add_one_le_exp (1800 : ℝ)
    linarith
  have hY : Task556a.windowY (Real.exp 1800) (1 / 18) = Real.exp 1100 := by
    unfold Task556a.windowY
    rw [← Real.exp_mul]
    norm_num
  have hH : (Real.exp 1800) ^ (7 / 18 + 1 / 18 : ℝ) ≤ Real.exp 800 := by
    rw [← Real.exp_mul]
    norm_num
  have hpoly := Real.pow_div_factorial_le_exp 300 (by norm_num) 5
  have hp : (1800 : ℝ) ^ (3 : ℝ) ≤ Real.exp 300 := by
    norm_num at hpoly ⊢
    linarith
  have hsmall : Real.exp 800 * Real.log (Real.exp 1800) ^ (1 + 2 : ℝ) ≤
      Task556a.windowY (Real.exp 1800) (1 / 18) := by
    rw [hY, Real.log_exp]
    rw [show (1 + 2 : ℝ) = 3 by norm_num]
    calc
      _ ≤ Real.exp 800 * Real.exp 300 := mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = Real.exp 1100 := by rw [← Real.exp_add]; norm_num
  exact Task634.A23_initial_range_small 1 1 (1 / 18) (Real.exp 1800) (Real.exp 800) 0
    hX (by norm_num) hH hsmall
#print axioms LeanLab.KumchevLiu2007.Task634.roughShortSum_initial_norm_le
#print axioms LeanLab.KumchevLiu2007.Task634.initial_energy_prefix_bound
#print axioms LeanLab.KumchevLiu2007.Task634.initial_energy_small
#print axioms LeanLab.KumchevLiu2007.Task634.A23_initial_range_small
