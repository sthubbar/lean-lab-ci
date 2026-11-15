/-
Jia 1996 pages 261 and 262, the finite base checks in Lemma 20.
Source https://doi.org/10.4064/aa-77-3-207-287.
Only two finite grid statements remain OPEN in this numerical input.
Interpolation and propagation use the actual constructed Buchstab function.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Bounds578
import LeanLab.Languasco2004.Endpoints578

namespace LeanLab.Languasco2004.Decomp578e
open Real Finset intervalIntegral Buchstab578 Bounds578 Geometry565
noncomputable section

/-- LEAF. Jia page 262 first finite base grid, restricted to the unresolved interior.
The two endpoint values at three and four are proved in Endpoints578.
Only the 9999 interior grid values remain in this proper input. -/
theorem grid_three_interior : ∀ k : ℕ, 0 < k → k < 10000 →
    0.56081 ≤ buchstab (3 + 0.0001 * (k : ℝ)) ∧
      buchstab (3 + 0.0001 * (k : ℝ)) ≤ 0.56439 := by sorry

/-- LEAF. Jia page 262 second finite base grid after its proved initial endpoint.
The value at four is already certified. Only the remaining 10000 values are asserted. -/
theorem grid_four_tail : ∀ k : ℕ, 0 < k → k ≤ 10000 →
    0.5613 ≤ buchstab (4 + 0.0001 * (k : ℝ)) ∧
      buchstab (4 + 0.0001 * (k : ℝ)) ≤ 0.5616 := by sorry

/-- Jia page 262 proof of Lemma 20, the first two unnumbered finite grid bounds.
CONDITIONAL ON grid_three_interior only.
The function is the constructed solution of display 40. Only 10001 base values are asserted.
This is a proper finite input, not the global numerical conclusion. -/
theorem grid_three : ∀ k : ℕ, k ≤ 10000 →
    0.56081 ≤ buchstab (3 + 0.0001 * (k : ℝ)) ∧
      buchstab (3 + 0.0001 * (k : ℝ)) ≤ 0.56439 := by
  intro k hk
  by_cases hz : k = 0
  · subst k
    simpa using Endpoints578.grid_three_start
  by_cases ht : k = 10000
  · subst k
    norm_num only
    have h := Endpoints578.grid_four_start
    constructor <;> linarith [h.1, h.2]
  exact grid_three_interior k (by omega) (by omega)

/-- Jia page 262 proof of Lemma 20, the second pair of unnumbered finite grid bounds.
CONDITIONAL ON grid_four_tail only.
Only the printed base grid on four through five is asserted, with its original constants. -/
theorem grid_four : ∀ k : ℕ, k ≤ 10000 →
    0.5613 ≤ buchstab (4 + 0.0001 * (k : ℝ)) ∧
      buchstab (4 + 0.0001 * (k : ℝ)) ≤ 0.5616 := by
  intro k hk
  by_cases hz : k = 0
  · subst k
    simpa using Endpoints578.grid_four_start
  exact grid_four_tail k (by omega) hk

/-- Page 262 interpolation support: the constructed function is 0.0224 Lipschitz above three. -/
theorem buchstab_lipschitz (x y : ℝ) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    |buchstab x - buchstab y| ≤ 0.0224 * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (3 : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (buchstab_derivative z (by linarith [show (3 : ℝ) ≤ z from hz])).differentiableAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using buchstab_derivative_0224 z hz) hy hx

/-- Page 262: the source grid mesh loses at most 0.00000224 between a grid point and a real argument.
CONDITIONAL ON the supplied finite grid bounds. -/
theorem grid_interpolation (a l U : ℝ) (ha : 3 ≤ a)
    (hgrid : ∀ k : ℕ, k ≤ 10000 → l ≤ buchstab (a + 0.0001 * (k : ℝ)) ∧
      buchstab (a + 0.0001 * (k : ℝ)) ≤ U)
    (u : ℝ) (hu : a ≤ u) (hu1 : u ≤ a + 1) :
    l - 0.00000224 ≤ buchstab u ∧ buchstab u ≤ U + 0.00000224 := by
  let k := ⌊10000 * (u - a)⌋₊
  have hk : k ≤ 10000 := by
    calc k ≤ ⌊(10000 : ℝ)⌋₊ := Nat.floor_mono (by linarith)
         _ = 10000 := by norm_num
  have hkl := Nat.floor_le (show 0 ≤ 10000 * (u - a) by positivity)
  have hku := Nat.lt_floor_add_one (10000 * (u - a))
  have hgL : a + 0.0001 * (k : ℝ) ≤ u := by dsimp [k]; linarith
  have hgU : u - (a + 0.0001 * (k : ℝ)) ≤ 0.0001 := by dsimp [k]; linarith
  have hg3 : 3 ≤ a + 0.0001 * (k : ℝ) := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hd := buchstab_lipschitz u (a + 0.0001 * (k : ℝ)) (ha.trans hu) hg3
  rw [abs_of_nonneg (sub_nonneg.mpr hgL)] at hd
  have he : |buchstab u - buchstab (a + 0.0001 * (k : ℝ))| ≤ 0.00000224 := by
    nlinarith
  have hb := hgrid k hk
  obtain ⟨heL, heU⟩ := abs_le.mp he
  constructor <;> linarith [hb.1, hb.2]

/-- Display 41 support: reuse the existing weighted strip comparison at an arbitrary starting interval.
CONDITIONAL ON the stated bounds on that one interval. -/
theorem bounds_propagate (K l U : ℝ) (hK : 2 ≤ K)
    (hbase : ∀ u ∈ Set.Icc K (K + 1), l ≤ buchstab u ∧ buchstab u ≤ U) :
    ∀ u : ℝ, K ≤ u → l ≤ buchstab u ∧ buchstab u ≤ U := by
  have hstrip : ∀ j : ℕ, ∀ u ∈ Set.Icc (K + (j : ℝ)) (K + (j : ℝ) + 1),
      l ≤ buchstab u ∧ buchstab u ≤ U := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      intro u hu
      simp only [Nat.cast_add, Nat.cast_one] at hu
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hKu : K + (j : ℝ) + 1 ≤ u := by linarith [hu.1]
      have hKp : 0 < K + (j : ℝ) + 1 := by linarith
      have hw := ih (K + (j : ℝ) + 1) ⟨by linarith, le_rfl⟩
      have hi := buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume)
        ((K + (j : ℝ) + 1) - 1) (u - 1)
      have hb : ∀ t ∈ Set.Icc ((K + (j : ℝ) + 1) - 1) (u - 1),
          l ≤ buchstab t ∧ buchstab t ≤ U := by
        intro t ht
        exact ih t ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
      exact buchstab_strip_from_recurrence buchstab (K + (j : ℝ) + 1) u l U
        hKp hKu hw hi hb (buchstab_anchored_recurrence _ _ (by linarith) hKu)
  intro u hu
  let j := ⌊u - K⌋₊
  have hjL := Nat.floor_le (show 0 ≤ u - K by linarith)
  have hjU := Nat.lt_floor_add_one (u - K)
  exact hstrip j u ⟨by dsimp [j]; linarith, by dsimp [j]; linarith⟩

/-- Page 262 Lemma 20 part ii: interpolate and propagate the first finite base grid.
CONDITIONAL ON grid_three only. -/
theorem global_three_from_grid : ∀ u : ℝ, 3 ≤ u →
    0.5607 ≤ buchstab u ∧ buchstab u ≤ 0.5644 := by
  apply bounds_propagate 3 0.5607 0.5644 (by norm_num)
  intro u hu
  have h := grid_interpolation 3 0.56081 0.56439 (by norm_num) grid_three u hu.1 hu.2
  constructor <;> linarith [h.1, h.2]

/-- Page 262 Lemma 20 part iii: interpolate and propagate the second finite base grid.
CONDITIONAL ON grid_four only. -/
theorem global_four_from_grid : ∀ u : ℝ, 4 ≤ u →
    0.5612 ≤ buchstab u ∧ buchstab u ≤ 0.5617 := by
  apply bounds_propagate 4 0.5612 0.5617 (by norm_num)
  intro u hu
  have h := grid_interpolation 4 0.5613 0.5616 (by norm_num) grid_four u hu.1 hu.2
  constructor <;> linarith [h.1, h.2]

/-- Jia Lemma 20 parts ii and iii: every source solution obeys the required global bounds.
CONDITIONAL ON the two proper finite grid leaves only. -/
theorem lemma20_bounds_from_grids :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) →
      (∀ u : ℝ, 3 ≤ u → w u ≤ 0.5644) ∧
      (∀ u : ℝ, 4 ≤ u → 0.5612 ≤ w u ∧ w u ≤ 0.5617) := by
  intro w hc h0 hr
  have he := solution_eq_buchstab w h0 hr
  constructor
  · intro u hu
    rw [he u (by linarith)]
    exact (global_three_from_grid u hu).2
  · intro u hu
    rw [he u (by linarith)]
    exact global_four_from_grid u hu

#print axioms grid_three_interior
#print axioms grid_four_tail
#print axioms grid_three
#print axioms grid_four
#print axioms buchstab_lipschitz
#print axioms grid_interpolation
#print axioms bounds_propagate
#print axioms global_three_from_grid
#print axioms global_four_from_grid
#print axioms lemma20_bounds_from_grids
end
end LeanLab.Languasco2004.Decomp578e
