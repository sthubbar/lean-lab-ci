import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
Deepening of the HARD leaf `sawtooth_sum_bound` of Feed1122VoronoiDivisorSumAsymptotic.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
In the classical proof the sawtooth sum over m up to root x splits at x to one third:
the head is bounded trivially by its length, and only the tail needs van der Corput.
The head bound and the splitting are proved here; the tail is the remaining HARD leaf.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122SawtoothSumBound

open Finset

/-- LEAF: Voronoi tail sawtooth bound in the classical proof of the Voronoi formula cited on
Halupczok page 337. The sum over m with floor of x to one third below m and m at most root x of
fract of x over m minus one half is O of x to one third times log x, by the van der Corput
second derivative test on dyadic blocks.
Class HARD: a genuine exponential sum estimate. -/
theorem tail_sawtooth_bound :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |∑ m ∈ (Icc 1 ⌊Real.sqrt x⌋₊).filter (fun m => ⌊x ^ (1 / 3 : ℝ)⌋₊ < m),
          (Int.fract (x / m) - 1 / 2)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x := by
  sorry

/-- The sawtooth has absolute value at most one half. -/
theorem abs_sawtooth_le (t : ℝ) : |Int.fract t - 1 / 2| ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Trivial head bound: the sawtooth sum over m at most x to one third and at most root x
has absolute value at most one half of x to one third. -/
theorem head_sawtooth_bound (x : ℝ) (hx : 0 ≤ x) :
    |∑ m ∈ (Icc 1 ⌊Real.sqrt x⌋₊).filter (fun m => ¬ ⌊x ^ (1 / 3 : ℝ)⌋₊ < m),
        (Int.fract (x / m) - 1 / 2)| ≤ x ^ (1 / 3 : ℝ) / 2 := by
  set a := ⌊x ^ (1 / 3 : ℝ)⌋₊
  set H := (Icc 1 ⌊Real.sqrt x⌋₊).filter (fun m => ¬ a < m)
  have hsub : H ⊆ Icc 1 a := by
    intro m hm
    simp only [H, mem_filter, mem_Icc, not_lt] at hm
    exact mem_Icc.mpr ⟨hm.1.1, hm.2⟩
  have hcard : (H.card : ℝ) ≤ a := by
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans (by omega)
  have ha : (a : ℝ) ≤ x ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  calc
    _ ≤ ∑ m ∈ H, |Int.fract (x / m) - 1 / 2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ H, (1 / 2 : ℝ) := sum_le_sum fun m _ => abs_sawtooth_le _
    _ = H.card * (1 / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ x ^ (1 / 3 : ℝ) / 2 := by nlinarith

/-- The sawtooth bound over m up to root x, assembled from the tail leaf and the
proved head bound. Statement identical to `sawtooth_sum_bound`. -/
theorem sawtooth_sum_bound_of_leaves :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨C, X0, hC, hT⟩ := tail_sawtooth_bound
  refine ⟨C + 1, max X0 3, by positivity, fun x hx => ?_⟩
  have hx3 : (3 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans hx3)
  have hp : 0 ≤ x ^ (1 / 3 : ℝ) := by positivity
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 ⌊Real.sqrt x⌋₊)
    (fun m => ⌊x ^ (1 / 3 : ℝ)⌋₊ < m) (fun m : ℕ => Int.fract (x / m) - 1 / 2)
  rw [← hsplit]
  have hT' := hT x ((le_max_left _ _).trans hx)
  have hH := head_sawtooth_bound x hx0
  have hpl : x ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) * Real.log x := le_mul_of_one_le_right hp hlog
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ C * x ^ (1 / 3 : ℝ) * Real.log x + x ^ (1 / 3 : ℝ) / 2 := add_le_add hT' hH
    _ ≤ (C + 1) * x ^ (1 / 3 : ℝ) * Real.log x := by nlinarith

end LeanLab.Halupczok2012.Feed1122SawtoothSumBound

#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBound.abs_sawtooth_le
#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBound.head_sawtooth_bound
#print axioms LeanLab.Halupczok2012.Feed1122SawtoothSumBound.sawtooth_sum_bound_of_leaves
