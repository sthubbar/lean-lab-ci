import LeanLab.HelfgottMajor.SPLIT_norm_LFunctionTrivChar_one_ge_near_one

/-!
# Split of `norm_main_part_ge` (`HelfgottMajor/SPLIT_norm_LFunctionTrivChar_one_ge_near_one`)

The target says the ten term Euler Maclaurin main part
`M(u) = (u - 1) ∑_{n ≤ 10} n^{-u} + 10^{1-u}` of `(u - 1) ζ(u)` has norm at least `1` on the
two pieces `1 ≤ Re u ≤ 6/5`, `Im u = ± 3/2`.

The cut is a grid with a Lipschitz bound, the standard reduction of a bound on a segment to
finitely many evaluations:

* `norm_main_part_grid_ge`: `‖M(1 + k/20 ± 3i/2)‖ ≥ 11/10` for `k = 0, ..., 4`, ten finite
  evaluations; mpmath gives the minimum `1.1479` over these points;
* `norm_main_part_sub_le`: `‖M(a) - M(b)‖ ≤ 2 ‖a - b‖` for `a`, `b` on the same piece, a mean
  value bound from `M'(u) = ∑_{n ≤ 10} n^{-u} (1 - (u - 1) log n) - 10^{1-u} log 10`;
  mpmath gives `max ‖M'‖ = 0.7404` on the pieces.

Every point of a piece is within `1/40` of a grid point, so `‖M(u)‖ ≥ 11/10 - 2/40 ≥ 1`; the twin
`norm_main_part_ge_of_leaves` proves the target statement verbatim from the two leaves.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitMainPartGrid

open Real Complex

/-- LEAF: the main part at the ten grid points `1 + k/20 ± 3i/2`, `k ≤ 4`, of the two pieces,
the finite evaluation step of `norm_main_part_ge`; each value is a sum of ten complex powers
`n^{-u}`, evaluated with explicit `exp`, `cos`, `sin` and `log` bounds.  mpmath gives the
minimum `1.1479`.  MEDIUM. -/
theorem norm_main_part_grid_ge (k : ℕ) (hk : k ≤ 4) (y : ℝ) (hy : y = 3 / 2 ∨ y = -(3 / 2)) :
    11 / 10 ≤ ‖((1 + (k : ℝ) / 20 : ℝ) + y * I - 1) *
        (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ (((1 + (k : ℝ) / 20 : ℝ) : ℂ) + y * I)) +
      (10 : ℂ) ^ (1 - (((1 + (k : ℝ) / 20 : ℝ) : ℂ) + y * I))‖ := by
  sorry

/-- LEAF: the main part is `2`-Lipschitz on each piece, the interpolation step of
`norm_main_part_ge`; by the mean value inequality from
`M'(u) = ∑_{n ≤ 10} n^{-u} (1 - (u - 1) log n) - 10^{1-u} log 10` and `‖n^{-u}‖ = n^{-Re u}`,
mpmath gives `max ‖M'‖ = 0.7404` there.  MEDIUM. -/
theorem norm_main_part_sub_le (a b : ℂ) (ha1 : 1 ≤ a.re) (ha2 : a.re ≤ 6 / 5) (hb1 : 1 ≤ b.re)
    (hb2 : b.re ≤ 6 / 5) (him : a.im = b.im) (hy : a.im = 3 / 2 ∨ a.im = -(3 / 2)) :
    ‖((a - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ a) + (10 : ℂ) ^ (1 - a)) -
      ((b - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ b) + (10 : ℂ) ^ (1 - b))‖ ≤
      2 * ‖a - b‖ := by
  sorry

/-- Every `x ∈ [1, 6/5]` is within `1/40` of a grid point `1 + k/20`, `k ≤ 4`.  Proved. -/
theorem exists_grid_near {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 6 / 5) :
    ∃ k : ℕ, k ≤ 4 ∧ |x - (1 + (k : ℝ) / 20)| ≤ 1 / 40 := by
  set t := (x - 1) * 20 + 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; nlinarith
  refine ⟨⌊t⌋₊, ?_, ?_⟩
  · have : ⌊t⌋₊ < 5 := by
      rw [Nat.floor_lt ht0]; push_cast; rw [ht]; linarith
    omega
  · have hf1 := Nat.floor_le ht0
    have hf2 := Nat.lt_floor_add_one t
    rw [abs_le]
    constructor <;> nlinarith

/-- The target `SplitPrincipalLowerEM.norm_main_part_ge`, verbatim, from the two leaves:
`‖M(u)‖ ≥ 11/10 - 2 · (1/40) ≥ 1`. -/
theorem norm_main_part_ge_of_leaves (u : ℂ) (h1 : 1 ≤ u.re) (h2 : u.re ≤ 6 / 5)
    (him : u.im = 3 / 2 ∨ u.im = -(3 / 2)) :
    1 ≤ ‖(u - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) + (10 : ℂ) ^ (1 - u)‖ := by
  obtain ⟨k, hk, hd⟩ := exists_grid_near h1 h2
  set v : ℂ := ((1 + (k : ℝ) / 20 : ℝ) : ℂ) + u.im * I with hv
  have hvre : v.re = 1 + (k : ℝ) / 20 := by simp [hv]
  have hvim : v.im = u.im := by simp [hv]
  have hkr : (k : ℝ) ≤ 4 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hG := norm_main_part_grid_ge k hk u.im him
  have hL := norm_main_part_sub_le u v h1 h2 (by rw [hvre]; linarith) (by rw [hvre]; linarith)
    hvim.symm him
  have hdist : ‖u - v‖ ≤ 1 / 40 := by
    have : u - v = ((u.re - (1 + (k : ℝ) / 20) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hv]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hd
  have htri := norm_sub_norm_le
    ((v - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ v) + (10 : ℂ) ^ (1 - v))
    ((v - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ v) + (10 : ℂ) ^ (1 - v) -
      ((u - 1) * (∑ n ∈ Finset.Icc (1 : ℕ) 10, 1 / (n : ℂ) ^ u) + (10 : ℂ) ^ (1 - u)))
  rw [sub_sub_cancel] at htri
  rw [norm_sub_rev] at hL
  rw [hv] at htri hL
  rw [hv] at hdist
  have : ‖u - (((1 + (k : ℝ) / 20 : ℝ) : ℂ) + u.im * I)‖ =
      ‖(((1 + (k : ℝ) / 20 : ℝ) : ℂ) + u.im * I) - u‖ := norm_sub_rev _ _
  linarith

end LeanLab.HelfgottMajor.SplitMainPartGrid
