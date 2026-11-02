/-
Task219 hypothesis instances for the page 21 ports and their application.
These checks use nonempty sums and nonzero phases where the hypotheses permit them.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp90

namespace LeanLab.BakerHarmanPintz1997.Vacuity219
open Finset PortedVanDerCorput LogPhase219 DerivativeTest219 LogarithmicTest219
open Progression219 Parameter219 LowFrequency219 Decomp90

example : ‖∑ n ∈ Ioc (0 : ℕ) 4, eK ((n : ℝ) / 2)‖ ≤ 4 := by
  have hb := kusmin_landau (f := fun n : ℕ => (n : ℝ) / 2) (a := 0) (b := 4)
    (δ := 1 / 4) (m := 0) (by norm_num) (by norm_num)
    (by intro n hn hn'; push_cast; linarith)
    (by intro n hn hn'; push_cast; linarith)
    (by intro n hn hn'; push_cast; linarith)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Ioc (0 : ℕ) 4, eK ((n : ℝ) ^ 2 / 2)‖ ≤ 40 := by
  have hb := vdC_second_derivative (f := fun n : ℕ => (n : ℝ) ^ 2 / 2)
    (a := 0) (b := 4) (lam := 1) (c := 1) (by omega) (by norm_num) (by norm_num)
    (by intro n hn hn'; push_cast; nlinarith)
    (by intro n hn hn'; push_cast; nlinarith)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Icc (-1 : ℤ) 1, eK ((n : ℝ) / 2)‖ ≤ 4 := by
  have hb := kusmin_landau_int (fun n : ℤ => (n : ℝ) / 2) (-1) 1 (by omega)
    (δ := 1 / 4) (m := 0) (by norm_num) (by norm_num)
    (by intro n hn; push_cast; linarith)
    (by intro n hn; push_cast; linarith)
    (by intro n hn; push_cast; linarith)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Icc (-2 : ℤ) 2, eK ((n : ℝ) ^ 2 / 2)‖ ≤ 48 := by
  have hb := second_derivative_int (fun n : ℤ => (n : ℝ) ^ 2 / 2) (-2) 2 (by omega)
    (lam := 1) (c := 1) (by norm_num) (by norm_num)
    (by intro n hn; push_cast; nlinarith)
    (by intro n hn; push_cast; nlinarith)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Icc (0 : ℤ) 0, eK (0 : ℝ)‖ ≤ 4 := by
  have hb := iterated_interval_vdc 0 (fun _ => 0) 0 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      intro hs hlen hhs
      have hh : hs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hs
      simp [backwardDifferences, eK])
  norm_num at hb ⊢ <;> exact hb

example : ∃ y : ℝ, 1 ≤ y ∧ y ≤ 4 ∧
    backwardDifferences [1, 2] (fun z => -Real.log z) 1 = 2 / y ^ 2 := by
  have hb := log_backwardDifferences_meanValue [1, 2] (by simp) (k := 1) (by simp) (x := 1) (by norm_num)
  norm_num at hb ⊢ <;> exact hb

example : (1 / 8 : ℝ) ≤ backwardDifferences [1, 2] (fun z => -Real.log z) 1 ∧
    backwardDifferences [1, 2] (fun z => -Real.log z) 1 ≤ 2 := by
  have hb := log_backwardDifferences_bounds [1, 2] (by simp) (k := 1) (by simp)
    (N := 1) (M := 4) (x := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Icc (0 : ℤ) 0,
    eK ((1 / 65536 : ℝ) * (-Real.log ((1 : ℝ) * n + 1)))‖ ≤ 4 * 65536 * 1 := by
  apply logarithmic_iterated_bound 0 0 0 1 (a := 1) (t := 1 / 65536) (r := 1)
    (N := 1) (M := 3) (U := 65536) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro hs hlen hhs
  have hh : hs = [] := List.eq_nil_of_length_eq_zero hlen
  subst hs
  norm_num [logDifferenceScale]

example : (∑ n ∈ (Ioc 1 5).filter (fun n : ℕ => (n : ZMod 2) = 1), (n : ℂ)) = 8 := by
  have hs : (Ioc 1 5).filter (fun n : ℕ => (n : ZMod 2) = 1) = ({3, 5} : Finset ℕ) := by decide
  rw [hs]
  norm_num

example : ‖∑ n ∈ Icc (100 : ℤ) 200, eK ((25 : ℝ) * (-Real.log ((1 : ℝ) * n + 0)))‖ ≤ 16 := by
  have hb := logarithmic_first_derivative 100 200 (a := 1) (T := 25) (r := 0) (N := 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb ⊢ <;> exact hb

example : ‖∑ n ∈ Ioc (100 : ℕ) 200, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) *
    (n : ℂ) ^ (-(half 25))‖ ≤ 8 * Real.pi * (100 : ℝ) ^ (1 / 2 : ℝ) / 25 := by
  have hb := character_sum_small_frequency (N := 100) (N1 := 200) (t := 25) (q := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num <;> nlinarith [Real.pi_gt_three]) (1 : DirichletCharacter ℂ 1)
  norm_num at hb ⊢ <;> exact hb

example : ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
    ‖∑ n ∈ (Ioc 2 4).filter (fun n : ℕ => (n : ZMod 1) = 0),
      (n : ℂ) ^ (-(16 : ℂ) * Complex.I)‖ ≤ C * (2 : ℝ) ^ (1 - 2 * η) := by
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlog : 1 ≤ L 16 := by
    unfold L
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  obtain ⟨η, hη, h⟩ := titchmarsh_branch (1 / 4) (by norm_num)
  obtain ⟨C, hC, h⟩ := h 1 (by norm_num)
  refine ⟨η, C, hη, hC, ?_⟩
  have hh := h 16 (by norm_num) 2 (by norm_num [h16]) (by norm_num) 1
    (by simpa using hlog) 16 (by norm_num) (by
      have hp : (1 : ℝ) ≤ (16 : ℝ) ^ ((1 / 4 : ℝ) / 4) := by
        apply Real.one_le_rpow <;> norm_num
      have hroot : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
        rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 16), hroot]
      nlinarith) 0 4 (by norm_num) (by norm_num)
  norm_num at hh ⊢ <;> exact hh

example : ((Ioc 2 4).filter (fun n : ℕ => (n : ZMod 1) = 0)).card = 2 := by decide

example : ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
    ‖∑ n ∈ Ioc (4 : ℕ) 8, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) *
      (n : ℂ) ^ (-(half 0))‖ ≤ C * ((4 : ℝ) ^ (1 / 2 - η) + (4 : ℝ) ^ (1 / 2 : ℝ)) := by
  have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlog : 1 ≤ L 16 := by
    unfold L
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  obtain ⟨η, hη, h⟩ := fgm_branch (1 / 4) (by norm_num)
  obtain ⟨C, hC, h⟩ := h 1 (by norm_num)
  refine ⟨η, C, hη, hC, ?_⟩
  have hh := h 16 (by norm_num) 4 8 (by norm_num [h16]) (by norm_num)
    (by norm_num) (by norm_num) 1 (by simpa using hlog) (1 : DirichletCharacter ℂ 1)
    0 (by norm_num) (by norm_num)
  norm_num at hh ⊢ <;> exact hh

example : (Ioc (4 : ℕ) 8 : Finset ℕ).card = 4 := by decide

/-- A positive differencing order has consistent hypotheses on a nonempty interval. -/
example : ∃ N : ℕ, 2 ≤ N ∧
    ‖∑ n ∈ Icc (N : ℤ) (2 * (N : ℤ)),
      eK (((N : ℝ) ^ (5 / 2 : ℝ)) * (-Real.log (n : ℝ)))‖ ≤
        16 * (N : ℝ) ^ (1 - (1 / 64 : ℝ) / 2) := by
  obtain ⟨X, hX, hbound⟩ := logarithmic_fixed_order 1
    (δ := 1 / 64) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max X 2)
  have hN2 : (2 : ℝ) ≤ N := (le_max_right X 2).trans hN.le
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hscale : (N : ℝ) ^ (5 / 2 : ℝ) * (1 / (N : ℝ)) ^ (1 + 2) =
      (N : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num
  refine ⟨N, by exact_mod_cast hN2, ?_⟩
  have hb := hbound N ((le_max_left X 2).trans hN.le) 1
    ((N : ℝ) ^ (5 / 2 : ℝ)) 0 (by norm_num) hN1 (by positivity)
    (by rw [hscale]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
    (by rw [hscale]) (N : ℤ) (2 * (N : ℤ))
    (by norm_num) (by norm_num)
  norm_num at hb ⊢ <;> exact hb

example : Lemma6 := lemma6_decomposed

#print axioms titchmarsh_branch
#print axioms fgm_branch
#print axioms lemma6_decomposed
end LeanLab.BakerHarmanPintz1997.Vacuity219
