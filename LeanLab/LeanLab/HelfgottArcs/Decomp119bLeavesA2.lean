/-
P0013 pages 74 and 75, the compact range of Lemma A.2, split along the paper's own proof:
interpolation bound A.4, second derivative bound from A.5, and the sampled grid with step 0.001.
AI wrote the Lean code for burst-20261122 S92. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FourierDecay

namespace LeanLab.HelfgottArcs.Decomp119bLeavesA2
open MeasureTheory Set Real

/-- LEAF: P0013 page 74 display A.4, maximum of a C2 function on an interval from its endpoints.
Class MEDIUM. P0013 display A.4, applied on page 75 to 4g plus fhat. Linear interpolation plus
the Taylor remainder bound, valued in the complex numbers. -/
theorem interp_A4 (g : ℝ → ℂ) (M a b : ℝ) (hab : a ≤ b) (hg : ContDiff ℝ 2 g)
    (hM : ∀ v ∈ Icc a b, ‖deriv (deriv g) v‖ ≤ M) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖g t‖ ≤ max ‖g a‖ ‖g b‖ + (b - a) ^ 2 / 8 * M := by
  sorry

/-- LEAF: P0013 page 75, smoothness of the multiplier 4g plus fhat, the Fourier transform of a
compactly supported bounded weight. Class MEDIUM. P0013 page 75, needed to apply display A.4. -/
theorem a2_contDiff :
    ContDiff ℝ 2 (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t) := by
  sorry

/-- LEAF: P0013 page 75, the bound by 48 pi squared on the second derivative of 4g plus fhat,
from display A.5 and the bound 12 pi squared for fhat second derivative. Class HARD. P0013
page 75 after display A.8. -/
theorem a2_second_deriv (v : ℝ) :
    ‖deriv (deriv (fun t : ℝ => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t)) v‖ ≤
      48 * π ^ 2 := by
  sorry

/-- LEAF: P0013 page 75, the Simpson rule grid check at t equal to k over 1000, largest value
31.52065 with error at most 0.000045. Class HARD. P0013 page 75, numerical certificate; the
floating point reproduction is gen/task81_lemma_a2.py, not a proof. -/
theorem a2_grid_certificate (k : ℕ) (hk : k ≤ 655000) :
    ‖(-2 * π * Complex.I * ((k / 1000 : ℝ) : ℂ)) ^ 2 * fhat eta2 (k / 1000 : ℝ)‖ ≤ 31.520695 := by
  sorry

/-- Interpolation step on one grid cell, assembled from A.4 and the second derivative bound. -/
theorem a2_cell (k : ℕ) (hk : k + 1 ≤ 655000) (δ : ℝ) (h0 : (k / 1000 : ℝ) ≤ δ)
    (h1 : δ ≤ (k / 1000 : ℝ) + 1 / 1000) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  set F : ℝ → ℂ := fun t => (-2 * π * Complex.I * (t : ℂ)) ^ 2 * fhat eta2 t with hF
  have hi := interp_A4 F (48 * π ^ 2) (k / 1000) ((k / 1000 : ℝ) + 1 / 1000)
    (by linarith) a2_contDiff (fun v _ => a2_second_deriv v) δ ⟨h0, h1⟩
  have ga := a2_grid_certificate k (by omega)
  have gb := a2_grid_certificate (k + 1) hk
  have hcast : (((k + 1 : ℕ) : ℝ) / 1000) = (k / 1000 : ℝ) + 1 / 1000 := by
    push_cast; ring
  rw [hcast] at gb
  have hmax : max ‖F (k / 1000)‖ ‖F ((k / 1000 : ℝ) + 1 / 1000)‖ ≤ 31.520695 :=
    max_le ga gb
  have hp : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
  have herr : ((k / 1000 : ℝ) + 1 / 1000 - k / 1000) ^ 2 / 8 * (48 * π ^ 2) ≤ 0.000237 := by
    ring_nf
    nlinarith
  change ‖F δ‖ ≤ 31.521
  linarith

/-- The parent `a2_compact` statement from the leaves, with the low branch handled by the parent. -/
theorem a2_compact_mid (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 655) :
    ‖(-2 * π * Complex.I * (δ : ℂ)) ^ 2 * fhat eta2 δ‖ ≤ 31.521 := by
  rcases eq_or_lt_of_le h1 with h | h
  · exact norm_second_fourier_eta2_le_of_large (by rw [h]; norm_num)
  · set k : ℕ := ⌊1000 * δ⌋₊ with hk
    have hfl : (k : ℝ) ≤ 1000 * δ := Nat.floor_le (by positivity)
    have hlt : 1000 * δ < k + 1 := Nat.lt_floor_add_one _
    have hk1 : k < 655000 := by
      have : (k : ℝ) < 655000 := by linarith
      exact_mod_cast this
    exact a2_cell k (by omega) δ (by rw [div_le_iff₀ (by norm_num)]; linarith)
      (by
        have : (k : ℝ) / 1000 + 1 / 1000 = (k + 1) / 1000 := by ring
        rw [this, le_div_iff₀ (by norm_num)]; linarith)

end LeanLab.HelfgottArcs.Decomp119bLeavesA2
