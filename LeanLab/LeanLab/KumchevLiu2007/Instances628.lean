/-
Concrete nonvacuity checks for the repaired Decomp516a route.
These examples check domains and finite energy witnesses.
They do not supply either analytic cancellation leaf or the unwritten residue.
Sources are P0088 pages 2, 7, 8, 15 and 16.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.LargeEpsilon628
import LeanLab.KumchevLiu2007.KernelBounds634

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

-- Nonempty translated blocks with an actual proved uniform kernel majorant.
example : (∑ n ∈ intervalNumbers 33 2, ‖minorCoefficient 32 16 2 1 n‖ ^ 2) ≤
    4 * 16 * (2 * ((squareWindow 16).card : ℝ) ^ 2) := by
  apply minor_mean_square_shifted (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  intro β _
  exact (Task634.kernelMass_trivial_bounds 16 1 2 β (by norm_num)).2

-- Both energy implications have a proved, nonempty finite model.
example : (∀ β ∈ Set.Icc (0 : ℝ) 1,
    kernelMass 16 16 1 β ≤ 16 * π ^ 2 * 4096 * 16 / Real.log 16 ^ (0 : ℝ)) ∧
    (∑ n ∈ intervalNumbers 17 16, ‖minorCoefficient 16 16 16 1 n‖ ^ 2) ≤
      64 * π ^ 2 * 4096 * 16 * 16 / Real.log 16 ^ (0 : ℝ) := by
  have hcard : ((squareWindow 16).card : ℝ) = 2 := by
    norm_num [squareWindow, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]
  have hshort : ∀ α t : ℝ, ‖roughShortSum 16 1 16 α t‖ ≤ 2 := by
    intro α t
    unfold roughShortSum
    calc
      _ ≤ ∑ _m ∈ (squareWindow 16).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + 16), (1 : ℝ) := by
        apply norm_sum_le_of_le
        intro m _
        rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
        exact roughWeight_norm_le_one _ _
      _ = (((squareWindow 16).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + 16)).card : ℝ) := by simp
      _ ≤ ((squareWindow 16).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le (squareWindow 16)
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + 16)
      _ = 2 := hcard
  have hint : ∀ α a b : ℝ, a ≤ b →
      (∫ t in a..b, ‖roughShortSum 16 1 16 α t‖ ^ 2) ≤ (b - a) * 4 := by
    intro α a b hab
    have hi : IntervalIntegrable (fun t => ‖roughShortSum 16 1 16 α t‖ ^ 2)
        volume a b := Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow 16)
          (fun m => roughWeight ((16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ)) m *
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) 16 a b
    calc
      _ ≤ ∫ _t in a..b, (4 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
        intro t _
        nlinarith [hshort α t, norm_nonneg (roughShortSum 16 1 16 α t)]
      _ = _ := by simp
  have he : ∀ α : ℝ, α ∉ majorArcs 16 1 →
      ((∫ t in (16 / 4 - 16 : ℝ)..(16 / 4), ‖roughShortSum 16 1 16 α t‖ ^ 2) +
        ∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 16 α t‖ ^ 2) ≤
          4096 * 16 ^ 2 / Real.log 16 ^ ((0 : ℝ) + 2) := by
    intro α _
    have h1 := hint α (16 / 4 - 16) (16 / 4) (by norm_num)
    have h2 := hint α (16 / 4) 16 (by norm_num)
    have hE : ((∫ t in (16 / 4 - 16 : ℝ)..(16 / 4), ‖roughShortSum 16 1 16 α t‖ ^ 2) +
        ∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 16 α t‖ ^ 2) ≤ 112 := by
      linarith
    refine hE.trans ?_
    have hL : 0 < Real.log 16 := Real.log_pos (by norm_num)
    have hlog : Real.log 16 ≤ 16 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)]
    have hsq : Real.log 16 ^ (2 : ℕ) ≤ 256 := by
      have h := (sq_le_sq₀ hL.le (by norm_num : (0 : ℝ) ≤ 16)).mpr hlog
      norm_num at h ⊢
      exact h
    norm_num only [zero_add, Real.rpow_two]
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith
  exact ⟨kernel_mass_of_complete_energy (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) he,
    minor_block_of_complete_energy (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) he⟩

-- The preceding energy witness has a nonempty minor frequency domain.
example : (1 / 2 : ℝ) ∉ majorArcs 16 1 := by
  rintro ⟨q, hq1, hqP, a, _hcop, hclose⟩
  have hq2 : q ≤ 1 := by exact_mod_cast hqP
  have hq : q = 1 := by omega
  subst q
  norm_num at hclose
  obtain ⟨hl, hu⟩ := abs_le.mp hclose
  have ha0 : (0 : ℤ) < a := by
    exact_mod_cast (show (0 : ℝ) < (a : ℝ) by linarith)
  have ha1 : a < (1 : ℤ) := by
    exact_mod_cast (show (a : ℝ) < 1 by linarith)
  omega

-- A fixed numeric application gives arbitrarily large admissible blocks.
example : ∃ X H : ℝ, 3 ≤ X ∧ 100 ≤ X ∧ 2 ≤ H ∧
    X ^ (7 / 18 + (1 / 10 : ℝ)) * (Real.log X ^ (1 : ℝ)) ^ (-4 : ℤ) ≤ H ∧
    H ≤ windowY X (1 / 10) * (Real.log X ^ (1 : ℝ)) ^ (-4 : ℤ) := by
  exact block_range_nonempty 1 (1 / 10) 100 (by norm_num) (by norm_num)

example : (1 / 10 : ℝ) ≤ 7 / 18 ∧ 1 ≤ windowY 16 (1 / 10) ∧
    windowY 16 (1 / 10) ≤ 16 ∧ windowY 16 (1 / 10) ≤ 16 := by
  apply block_window_parameters (B := 0) (H := windowY 16 (1 / 10))
    (by norm_num) (by norm_num) (by norm_num)
  · simp only [Real.rpow_zero, one_zpow, mul_one]
    unfold windowY
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · simp

-- The initial Gallagher integral has a positive A and an exact block endpoint.
example (α : ℝ) :
    (∫ t in (256 / 4 - 16 : ℝ)..(256 / 4),
      ‖roughShortSum 256 (Real.log (Real.exp 2) ^ (1 : ℝ)) 16 α t‖ ^ 2) ≤
        4 * 16 ^ 2 / Real.log (Real.exp 2) ^ ((2 : ℝ) + 2) := by
  apply block_initial_energy (B := 1) (A := 2)
  · have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  · norm_num
  · norm_num
  · norm_num
  · norm_num [Real.log_exp]

example : ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
    X ^ (7 / 18 + (1 / 10 : ℝ)) * (Real.log X ^ (1 : ℝ)) ^ (-4 : ℤ) ≤ H →
      2 ≤ H := block_length_eventually 1 (1 / 10) (by norm_num)

example : ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
    X ^ (7 / 18 + (1 / 10 : ℝ)) * (Real.log X ^ (1 : ℝ)) ^ (-4 : ℤ) ≤ H →
      Real.sqrt (windowY X (1 / 10)) ≤ H :=
  block_root_eventually 1 (1 / 10) (by norm_num)

-- The new low H leaf has an active numeric domain, not a contradictory premise.
example : 11 / 36 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 5 / 6 ∧
    (64 : ℝ) ^ (1 - (1 / 2 : ℝ)) < 16 ∧ (16 : ℝ) ≤ 64 ∧
    (16 : ℝ) ≤ windowY 64 (1 / 2) ∧ (16 : ℝ) < 64 ^ (7 / 18 + (1 / 2 : ℝ)) := by
  have h64 : (64 : ℝ) = 2 ^ (6 : ℝ) := by norm_num
  have h16 : (16 : ℝ) = 64 ^ (2 / 3 : ℝ) := by
    rw [h64, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, h16]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  · rw [h16]
    unfold windowY
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · rw [h16]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

example : (11 / 36 : ℝ) < 1 / 2 := by
  apply low_H_epsilon (X := 64) (H := 16) (by norm_num)
  · norm_num
  · have h16 : (16 : ℝ) = 64 ^ (2 / 3 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h16]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

example : windowPairs 16 100 24 = ∅ :=
  block_windowPairs_empty_below 16 100 (by norm_num) 24 (by norm_num)

example : err53 1 1 1 0 = 0 := by
  apply block_err53_vanish_below
  · norm_num [windowY]
  · norm_num [windowY]

example : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ∧ 2 * X < windowY X 1 / 4 :=
  block_eventually_large_window 1 (by norm_num)

example : ∀ᶠ X : ℝ in Filter.atTop, ∀ H : ℝ, 0 ≤ H → H ≤ X →
    cntIoc (fun n => InH2 n ∧
      Real.sqrt (windowY X 1) * Real.log X ^ (-(1 : ℝ)) < err53 X 1 1 n) X H = 0 :=
  block_eq53_very_large_eps 1 1 1 (by norm_num)

example : cntIoc (fun n => InH2 n ∧
    Real.sqrt (windowY 64 (1 / 2)) * Real.log 64 ^ (-(1 : ℝ)) <
      err53 64 (1 / 2) 1 n) 64 64 ≤
    cntIoc (fun n => InH2 n ∧
    Real.sqrt (windowY 64 (1 / 2)) * Real.log 64 ^ (-(1 : ℝ)) <
      err53 64 (1 / 2) 1 n) 64 (windowY 64 (1 / 2)) :=
  exception_count_le_window 1 1 (1 / 2) 64 64 (by norm_num)

end LeanLab.KumchevLiu2007.Task628
