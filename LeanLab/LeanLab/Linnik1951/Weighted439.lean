/-
P0093 page 162 equations 7.8 and 7.9.
The finite weighted rotation deficit before binary phase concentration.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Phase439

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 162 equations 7.8 and 7.9. A large weighted sum of unit
phases gives a unit rotation with small total unweighted deficit, when
every retained weight lies between a fixed positive c and one. -/
theorem weighted_rotation_deficit439 (M : ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η)
    (ha : ∀ m ∈ range M, c ≤ a m) (ha1 : ∀ m ∈ range M, a m ≤ 1)
    (hz : ∀ m, ‖z m‖ = 1)
    (hlarge : (1 - η) * (∑ m ∈ range M, a m) <
      ‖∑ m ∈ range M, (a m : ℂ) * z m‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      (∑ m ∈ range M, (1 - (w * z m).re)) ≤ η * (M : ℝ) / c := by
  obtain ⟨w, hw, hrot⟩ := LeanLab.Linnik.Gallagher1975Lemma1.exists_rot
    (∑ m ∈ range M, (a m : ℂ) * z m)
  refine ⟨w, hw, ?_⟩
  have hD (m : ℕ) : 0 ≤ 1 - (w * z m).re := by
    have hh := Complex.re_le_norm (w * z m)
    rw [norm_mul, hw, hz, one_mul] at hh
    linarith
  have htotal : (∑ m ∈ range M, a m) ≤ (M : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum ha1
  have hidentity : (∑ m ∈ range M, a m * (1 - (w * z m).re)) =
      (∑ m ∈ range M, a m) - ‖∑ m ∈ range M, (a m : ℂ) * z m‖ := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [← hrot, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show w * ((a m : ℂ) * z m) = (a m : ℂ) * (w * z m) by ring]
    simp
  have hlower : c * (∑ m ∈ range M, (1 - (w * z m).re)) ≤
      ∑ m ∈ range M, a m * (1 - (w * z m).re) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_right (ha m hm) (hD m))
  have hupper : (∑ m ∈ range M, a m * (1 - (w * z m).re)) ≤ η * (M : ℝ) := by
    rw [hidentity]
    calc
      _ ≤ η * (∑ m ∈ range M, a m) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left htotal hη
  apply (le_div_iff₀ hc).mpr
  nlinarith

end LeanLab.Linnik1951
