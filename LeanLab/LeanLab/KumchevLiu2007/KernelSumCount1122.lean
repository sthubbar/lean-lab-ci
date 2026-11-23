/-
ROUTE BURST burst-20261122, session S81. Card form of the square counting input of the LEAF
outer_square_bound of KernelSumSplit1122, P0088 Kumchev and Liu 2007, page 7, the display
before 27: at most H/(2s) + 1 integers m at least s have m^2 in a window of length H.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelSumF2Bound1122

namespace LeanLab.KumchevLiu2007.KernelSumCount1122

/-- PROVED. If every m in S has s at most m and m^2 in [A, A + H), with s > 0 and H at least 0,
then S has at most H/(2s) + 1 elements. -/
theorem card_squares_window (s A H : ℝ) (hs : 0 < s) (hH : 0 ≤ H) (S : Finset ℕ)
    (hS : ∀ m ∈ S, s ≤ m ∧ A ≤ (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 < A + H) :
    (S.card : ℝ) ≤ H / (2 * s) + 1 := by
  have hq : 0 ≤ H / (2 * s) := div_nonneg hH (by linarith)
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; simp only [Finset.card_empty, Nat.cast_zero]; linarith
  set m0 := S.min' hne
  have hm0 := hS m0 (S.min'_mem hne)
  have hsub : S ⊆ Finset.Icc m0 (m0 + ⌊H / (2 * s)⌋₊) := by
    intro m hm
    have hle : m0 ≤ m := S.min'_le m hm
    have hg := KernelSumF2Bound1122.square_gap_window s A H m0 m hm0.1 hle hm0.2.1 (hS m hm).2.2
    rw [Finset.mem_Icc]
    refine ⟨hle, ?_⟩
    have h1 : ((m : ℝ) - m0) ≤ H / (2 * s) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have h2 : m - m0 ≤ ⌊H / (2 * s)⌋₊ := Nat.le_floor (by rw [Nat.cast_sub hle]; exact h1)
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc, show m0 + ⌊H / (2 * s)⌋₊ + 1 - m0 = ⌊H / (2 * s)⌋₊ + 1 by omega] at hc
  have hf := Nat.floor_le hq
  have hc' : (S.card : ℝ) ≤ ((⌊H / (2 * s)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  linarith

end LeanLab.KumchevLiu2007.KernelSumCount1122

#print axioms LeanLab.KumchevLiu2007.KernelSumCount1122.card_squares_window
