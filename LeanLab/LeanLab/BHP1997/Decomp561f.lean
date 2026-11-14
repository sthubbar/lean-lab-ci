/-
P0069 page 10 display 2.16, unrestricted window normalization diagnostic.
This does not refute the paper local energy estimate under its other inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.Gallagher.Basic
import Mathlib.Tactic
namespace LeanLab.BHP1997.Decomp561f
open Finset Complex MeasureTheory
open LeanLab.PNTPort.Gallagher

/-- P0069 page 10 display 2.16, auxiliary normalization diagnostic.
Interior windows of length two cancel for the alternating coefficients. -/
theorem alternating_window_interior561 (N m : ℕ) (hm : 0 < m) (hmN : m < N) :
    win (fun n => (-1 : ℂ) ^ n) N 2 m = 0 := by
  have he : ((range N).filter (fun n => n ≤ m ∧ m < n + 2)) = {m - 1, m} := by
    ext n
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    omega
  rw [win, he, sum_pair (by omega : m - 1 ≠ m)]
  have hs : m = m - 1 + 1 := by omega
  nth_rw 2 [hs]
  rw [pow_succ]
  ring

/-- P0069 page 10 display 2.16, auxiliary normalization diagnostic.
The first boundary window equals one. -/
theorem alternating_window_first561 (N : ℕ) (hN : 0 < N) :
    win (fun n => (-1 : ℂ) ^ n) N 2 0 = 1 := by
  have he : ((range N).filter (fun n => n ≤ 0 ∧ 0 < n + 2)) = {0} := by
    ext n
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  rw [win, he]
  simp

/-- P0069 page 10 display 2.16, auxiliary normalization diagnostic.
The last boundary window contains the final coefficient. -/
theorem alternating_window_last561 (N : ℕ) (hN : 0 < N) :
    win (fun n => (-1 : ℂ) ^ n) N 2 N = (-1 : ℂ) ^ (N - 1) := by
  have he : ((range N).filter (fun n => n ≤ N ∧ N < n + 2)) = {N - 1} := by
    ext n
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  rw [win, he]
  simp

/-- P0069 page 10 display 2.16, auxiliary normalization diagnostic.
Every later window is zero. -/
theorem alternating_window_after561 (N m : ℕ) (hm : N < m) :
    win (fun n => (-1 : ℂ) ^ n) N 2 m = 0 := by
  have he : ((range N).filter (fun n => n ≤ m ∧ m < n + 2)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    simp only [mem_filter, mem_range] at hn
    omega
  rw [win, he]
  simp


/-- P0069 page 10 display 2.16, the alternating two point windows have
constant total energy, independent of the polynomial support length. -/
theorem alternating_window_energy561 (N : ℕ) (hN : 0 < N) :
    (∑ m ∈ range (N + 2), ‖win (fun n => (-1 : ℂ) ^ n) N 2 m‖ ^ 2) = 2 := by
  have hp (m : ℕ) : ‖win (fun n => (-1 : ℂ) ^ n) N 2 m‖ ^ 2 =
      (if m = 0 then (1 : ℝ) else 0) + (if m = N then (1 : ℝ) else 0) := by
    by_cases hm0 : m = 0
    · subst m
      rw [alternating_window_first561 N hN]
      norm_num [hN.ne]
    by_cases hmN : m < N
    · rw [alternating_window_interior561 N m (Nat.pos_of_ne_zero hm0) hmN]
      simp [hm0, ne_of_lt hmN]
    by_cases he : m = N
    · subst m
      rw [alternating_window_last561 N hN]
      simp [ne_of_gt hN, norm_pow]
    · rw [alternating_window_after561 N m (by omega)]
      simp [hm0, he]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  norm_num

/-- P0069 page 10 display 2.16, the full frequency band for the alternating
polynomial has energy equal to its support length by the existing finite Parseval. -/
theorem alternating_polynomial_energy561 (N : ℕ) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2),
      ‖∑ n ∈ range N, (-1 : ℂ) ^ n * LeanLab.PNTPort.LargeSieve.e (n * t)‖ ^ 2) = (N : ℝ) := by
  rw [LeanLab.PNTPort.Gallagher.parseval]
  simp [norm_pow]

/-- P0069 page 10 display 2.16, source normalization QUESTION.
No universal bound uses both the full band of radius one half and unmodulated
windows of length two, even for the single family of alternating coefficients.
This negates an unrestricted reading of that auxiliary inequality, not the
paper theorem with its other analytic hypotheses. -/
theorem full_band_window_bound_false561 :
    ¬ ∃ C : ℝ, ∀ N : ℕ,
      (∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        ‖∑ n ∈ range N, (-1 : ℂ) ^ n * LeanLab.PNTPort.LargeSieve.e (n * t)‖ ^ 2) ≤
        C * (∑ m ∈ range (N + 2), ‖win (fun n => (-1 : ℂ) ^ n) N 2 m‖ ^ 2) := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (2 * C))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN1)
  have hNC : 2 * C < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hh := hC N
  rw [alternating_polynomial_energy561, alternating_window_energy561 N hN0] at hh
  linarith

end LeanLab.BHP1997.Decomp561f
