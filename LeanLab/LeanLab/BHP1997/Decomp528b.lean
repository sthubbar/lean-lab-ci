/-
P0069, pages 24 to 27. CODEX task528.
Finite partial summation for the explicit smooth endpoint taper.
This algebra does not assert the analytic mean value 4.1.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp528a

namespace LeanLab.BHP1997.Decomp528b
open Classical Decomp528a
open scoped BigOperators

/-- Pages 24 to 27, auxiliary Abel bound for arbitrary finite real weights.
A uniform prefix norm bounds the weighted sum by endpoint plus variation. -/
theorem weighted_sum_norm_le (w : ℕ → ℝ) (g : ℕ → ℂ) (n : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (hg : ∀ j ≤ n, ‖∑ i ∈ Finset.range j, g i‖ ≤ K) :
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * g i‖ ≤
      (|w (n - 1)| + ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) * K := by
  have he : (∑ i ∈ Finset.range n, (w i : ℂ) * g i) =
      w (n - 1) • (∑ i ∈ Finset.range n, g i) -
      ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), g j) := by
    simpa only [Complex.real_smul] using Finset.sum_range_by_parts w g n
  rw [he]
  calc
    _ ≤ ‖w (n - 1) • (∑ i ∈ Finset.range n, g i)‖ +
        ‖∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) • (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sub_le _ _
    _ ≤ |w (n - 1)| * K + ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| * K := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg n le_rfl) (abs_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg (i + 1) (by have := Finset.mem_range.mp hi; omega)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Pages 24 to 27, auxiliary variation estimate for an increasing factor
and a decreasing factor taking values between zero and one. -/
theorem product_variation_le_two (u v : ℕ → ℝ) (hu : Monotone u) (hv : Antitone v)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, |u (i + 1) * v (i + 1) - u i * v i|) ≤ 2 := by
  have hstep (i : ℕ) : |u (i + 1) * v (i + 1) - u i * v i| ≤
      (u (i + 1) - u i) + (v i - v (i + 1)) := by
    have hu' := hu (Nat.le_succ i)
    have hv' := hv (Nat.le_succ i)
    have h1 := mul_le_of_le_one_right (sub_nonneg.mpr hu') (hv1 (i + 1))
    have h2 := mul_le_of_le_one_left (sub_nonneg.mpr hv') (hu1 i)
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hu') (hv0 (i + 1)),
      mul_nonneg (hu0 i) (sub_nonneg.mpr hv')]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ((u (i + 1) - u i) + (v i - v (i + 1))) :=
      Finset.sum_le_sum (fun i hi => hstep i)
    _ = (u n - u 0) + (v 0 - v n) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub, Finset.sum_range_sub']
    _ ≤ 2 := by linarith [hu1 n, hu0 0, hv1 0, hv0 n]

/-- Pages 24 to 27, the smooth endpoint taper has discrete variation at most two. -/
theorem taper_variation_le_two {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑ i ∈ Finset.range n, |taper x (i + 1) - taper x i|) ≤ 2 := by
  let u : ℕ → ℝ := fun i => Real.smoothTransition (4 * ((i : ℝ) / x) - 2)
  let v : ℕ → ℝ := fun i => Real.smoothTransition (4 - 2 * ((i : ℝ) / x))
  have hu : Monotone u := by
    intro i j hij
    apply Real.smoothTransition.monotone
    have := div_le_div_of_nonneg_right (Nat.cast_le.mpr hij : (i : ℝ) ≤ j) hx.le
    linarith
  have hv : Antitone v := by
    intro i j hij
    apply Real.smoothTransition.monotone
    have := div_le_div_of_nonneg_right (Nat.cast_le.mpr hij : (i : ℝ) ≤ j) hx.le
    linarith
  simpa only [u, v, taper, Nat.cast_add, Nat.cast_one] using product_variation_le_two u v hu hv
    (fun _ => Real.smoothTransition.nonneg _) (fun _ => Real.smoothTransition.le_one _)
    (fun _ => Real.smoothTransition.nonneg _) (fun _ => Real.smoothTransition.le_one _) n

/-- Pages 24 to 27, tapering costs at most three in any uniform prefix norm estimate. -/
theorem tapered_sum_norm_le {x : ℝ} (hx : 0 < x) (g : ℕ → ℂ) (n : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (hg : ∀ j ≤ n, ‖∑ i ∈ Finset.range j, g i‖ ≤ K) :
    ‖∑ i ∈ Finset.range n, (taper x i : ℂ) * g i‖ ≤ 3 * K := by
  have hw : |taper x ((n - 1 : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (taper_bounds _ _).1]
    exact (taper_bounds _ _).2
  have hv : (∑ i ∈ Finset.range (n - 1), |taper x ((i + 1 : ℕ) : ℝ) - taper x i|) ≤ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using taper_variation_le_two hx (n - 1)
  exact (weighted_sum_norm_le (fun i => taper x i) g n hK hg).trans
    (mul_le_mul_of_nonneg_right (by linarith) hK)

end LeanLab.BHP1997.Decomp528b
