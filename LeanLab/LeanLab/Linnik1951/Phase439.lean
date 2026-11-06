/-
P0093 pages 162 and 163 equations 7.8 through 7.11.
Elementary phase deficit estimates for the finite weighted rotation argument.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.EntropyBridge412

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 163 equation 7.10. A phase away from the nearest
integer has a quadratic cosine deficit. Mathlib supplies the cosine bound
on the interval from negative pi through pi and the nearest integer bound. -/
theorem phase_distance_deficit439 (x : ℝ) :
    8 * |x - (round x : ℤ)| ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have hround := abs_sub_round x
  have hpi := Real.pi_pos
  have hy : |2 * Real.pi * (x - (round x : ℤ))| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  have hc := Real.cos_le_one_sub_mul_cos_sq hy
  have heq : 2 * Real.pi * (x - (round x : ℤ)) =
      2 * Real.pi * x - (round x : ℤ) * (2 * Real.pi) := by ring
  rw [heq, Real.cos_sub_int_mul_two_pi] at hc
  have hsq : 2 / Real.pi ^ 2 * (2 * Real.pi * (x - (round x : ℤ))) ^ 2 =
      8 * |x - (round x : ℤ)| ^ 2 := by
    rw [sq_abs]
    field_simp
    ring
  rw [← heq, hsq] at hc
  linarith

/-- P0093 page 163 consecutive phase comparison before equation 7.11.
For unit phases, the distance from z to one is controlled by the two
rotated deficits at z and z squared. This avoids choosing a good pair. -/
theorem unit_square_deficit439 (w z : ℂ) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    1 - z.re ≤ 2 * ((1 - (w * z).re) + (1 - (w * z ^ 2).re)) := by
  have ha : ‖w * z‖ = 1 := by rw [norm_mul, hw, hz, one_mul]
  have hb : ‖w * z ^ 2‖ = 1 := by rw [norm_mul, norm_pow, hw, hz]; norm_num
  have heq : ‖w * z ^ 2 - w * z‖ = ‖z - 1‖ := by
    rw [show w * z ^ 2 - w * z = w * z * (z - 1) by ring,
      norm_mul, ha, one_mul]
  have htri : ‖w * z ^ 2 - w * z‖ ≤ ‖w * z ^ 2 - 1‖ + ‖w * z - 1‖ := by
    rw [show w * z ^ 2 - w * z = (w * z ^ 2 - 1) - (w * z - 1) by ring]
    exact norm_sub_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [heq] at hsq
  have hA := LeanLab.Linnik.Gallagher1975Lemma1.norm_sub_one_sq ha
  have hB := LeanLab.Linnik.Gallagher1975Lemma1.norm_sub_one_sq hb
  have hZ := LeanLab.Linnik.Gallagher1975Lemma1.norm_sub_one_sq hz
  nlinarith [sq_nonneg (‖w * z ^ 2 - 1‖ - ‖w * z - 1‖)]

/-- P0093 page 163 passage to equation 7.11. Summing the consecutive
phase comparison controls all unrotated deficits. The last phase costs
at most two and each rotated deficit occurs at most twice. -/
theorem consecutive_phase_deficit_sum439 (M : ℕ) (w : ℂ) (hw : ‖w‖ = 1)
    (z : ℕ → ℂ) (hz : ∀ m, ‖z m‖ = 1) (hstep : ∀ m, z (m + 1) = z m ^ 2) :
    ∑ m ∈ range M, (1 - (z m).re) ≤
      4 * (∑ m ∈ range M, (1 - (w * z m).re)) + 2 := by
  have hD (m : ℕ) : 0 ≤ 1 - (w * z m).re := by
    have hh := Complex.re_le_norm (w * z m)
    rw [norm_mul, hw, hz, one_mul] at hh
    linarith
  cases M with
  | zero => simp
  | succ M =>
    have hpair (m : ℕ) : 1 - (z m).re ≤
        2 * ((1 - (w * z m).re) + (1 - (w * z (m + 1)).re)) := by
      rw [hstep]
      exact unit_square_deficit439 w (z m) hw (hz m)
    have hsum := Finset.sum_le_sum (s := range M) (fun m hm => hpair m)
    simp_rw [mul_add] at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hprefix : (∑ m ∈ range M, (1 - (w * z m).re)) ≤
        ∑ m ∈ range (M + 1), (1 - (w * z m).re) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun m hm hnot => hD m)
    have hshift : (∑ m ∈ range M, (1 - (w * z (m + 1)).re)) ≤
        ∑ m ∈ range (M + 1), (1 - (w * z m).re) := by
      rw [Finset.sum_range_succ']
      linarith [hD 0]
    have hlast : 1 - (z M).re ≤ 2 := by
      have hh := Complex.abs_re_le_norm (z M)
      rw [hz] at hh
      linarith [(abs_le.mp hh).1]
    rw [Finset.sum_range_succ]
    nlinarith

end LeanLab.Linnik1951
