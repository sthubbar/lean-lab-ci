import LeanLab.LanguascoPerelli1996.Window422

/-!
P0071 pages 355 through 358, audit of the elementary window estimate.
Finite Cauchy Schwarz loses one power of the window length.
The resulting bound does not supply the OPEN analytic leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Coarse422
open Real

/-- Derived finite Cauchy Schwarz test for the Gallagher route to display 23.
A single window has at most L coefficients. -/
theorem window_sq_le (c : ℕ → ℂ) (N L m : ℕ) :
    ‖LeanLab.PNTPort.Gallagher.win c N L m‖ ^ 2 ≤
      (L : ℝ) * ∑ n ∈ (Finset.range N).filter (fun n => n ≤ m ∧ m < n + L), ‖c n‖ ^ 2 := by
  let s := (Finset.range N).filter (fun n => n ≤ m ∧ m < n + L)
  have hsub : s ⊆ Finset.Ico (m + 1 - L) (m + 1) := by
    intro n hn
    simp only [s, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
    omega
  have hcard : (s.card : ℝ) ≤ L := by
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hh
    exact_mod_cast hh.trans (by omega : m + 1 - (m + 1 - L) ≤ L)
  calc
    _ ≤ (∑ n ∈ s, ‖c n‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖c n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (L : ℝ) * ∑ n ∈ s, ‖c n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Derived finite counting test for display 23.
Every coefficient occurs in exactly L of the integer windows. -/
theorem coefficient_window_count (c : ℕ → ℂ) (N L : ℕ) :
    (∑ m ∈ Finset.range (N + L),
      ∑ n ∈ (Finset.range N).filter (fun n => n ≤ m ∧ m < n + L), ‖c n‖ ^ 2) =
        (L : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_filter]
  have hs : (Finset.range (N + L)).filter (fun m => n ≤ m ∧ m < n + L) =
      Finset.Ico n (n + L) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
    omega
  rw [hs]
  simp

/-- Derived coarse window bound for page 358 display 23.
Without an analytic cancellation input the finite Cauchy Schwarz route
gives L squared times the coefficient energy, rather than L times it. -/
theorem all_windows_coarse (c : ℕ → ℂ) (N L : ℕ) :
    (∑ m ∈ Finset.range (N + L), ‖LeanLab.PNTPort.Gallagher.win c N L m‖ ^ 2) ≤
      (L : ℝ) ^ 2 * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  calc
    _ ≤ ∑ m ∈ Finset.range (N + L), (L : ℝ) *
        ∑ n ∈ (Finset.range N).filter (fun n => n ≤ m ∧ m < n + L), ‖c n‖ ^ 2 :=
      Finset.sum_le_sum (fun m _ => window_sq_le c N L m)
    _ = (L : ℝ) * ((L : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2) := by
      rw [← Finset.mul_sum, coefficient_window_count]
    _ = _ := by ring

end LeanLab.LanguascoPerelli1996.Coarse422

#print axioms LeanLab.LanguascoPerelli1996.Coarse422.window_sq_le
#print axioms LeanLab.LanguascoPerelli1996.Coarse422.coefficient_window_count
#print axioms LeanLab.LanguascoPerelli1996.Coarse422.all_windows_coarse
