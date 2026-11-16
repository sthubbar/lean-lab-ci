import LeanLab.Zinoviev1997.Series

/-!
The exact finite coefficient of the full smoothed von Mangoldt series.
P0011 printed page 100, the interchange preceding the formula for J.
The positive-frequency convention reverses both Fourier signs together.
The prime-power correction still requires its own estimate.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997.SeriesFinite623
open Finset Filter Topology
open LeanLab.Zinoviev1997 LeanLab.CircleOrth

/-- Once every coordinate through N is retained, the triple coefficient is stable.
P0011 page 100, the nonnegative-frequency coefficient extraction step.
-/
theorem T3_stable623 (N M : ℕ) (hM : N ≤ M) : T3 N M = T3 N N := by
  classical
  let f : ℕ → ℕ → ℕ → ℝ := fun x y z =>
    if x + y + z = N then aZ N x * aZ N y * aZ N z else 0
  have hsub : Icc 1 N ⊆ Icc 1 M := Icc_subset_Icc le_rfl hM
  have hgt (x : ℕ) (hx : x ∈ Icc 1 M) (hn : x ∉ Icc 1 N) : N < x := by
    simp only [mem_Icc] at hx hn
    omega
  change (∑ x ∈ Icc 1 M, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M, f x y z) =
    ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 N, f x y z
  calc
    _ = ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 M, ∑ z ∈ Icc 1 M, f x y z := by
      symm
      apply sum_subset hsub
      intro x hx hn
      have hxgt := hgt x hx hn
      apply sum_eq_zero
      intro y hy
      apply sum_eq_zero
      intro z hz
      simp [f, show x + y + z ≠ N by omega]
    _ = ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, ∑ z ∈ Icc 1 M, f x y z := by
      apply sum_congr rfl
      intro x hx
      symm
      apply sum_subset hsub
      intro y hy hn
      have hygt := hgt y hy hn
      apply sum_eq_zero
      intro z hz
      simp [f, show x + y + z ≠ N by omega]
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      symm
      apply sum_subset hsub
      intro z hz hn
      have hzgt := hgt z hz hn
      simp [f, show x + y + z ≠ N by omega]

/-- The full absolutely convergent cube integral is its exact finite triple coefficient.
P0011 page 100, summation and integration before bounding the prime-power correction.
The existing series theorem supplies the dominated limit, and stability evaluates it.
-/
theorem SZ_cube_finite623 {N : ℕ} (hN : 0 < N) :
    (∫ α in (0 : ℝ)..1, SZ N α ^ 3 * ee (-((N : ℤ) * α))) = (T3 N N : ℂ) := by
  have hfinite : Tendsto (fun M : ℕ => (T3 N M : ℂ)) atTop (𝓝 (T3 N N : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with M hM
    rw [T3_stable623 N M hM]
  exact tendsto_nhds_unique (SZ_cube_tendsto hN) hfinite

example : T3 9 10 = T3 9 9 := T3_stable623 9 10 (by norm_num)
example : 3 ∈ Icc (1 : ℕ) 9 ∧ 3 + 3 + 3 = 9 := by norm_num

end LeanLab.DERZ1997.SeriesFinite623
