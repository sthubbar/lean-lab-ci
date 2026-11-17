import LeanLab.HelfgottMajor.SPLIT_polya_vinogradov_4_20

/-!
Split of the odd branch `leaf_odd_case` of the explicit Polya-Vinogradov inequality for a
primitive character modulo `q > 1`.

The odd branch bounds the supremum over `n` of the norm of the partial sums of an odd primitive
character by `1/(2*pi) * sqrt q * log q + 1/pi * sqrt q * log (log q) + sqrt q`.

The route is the odd sawtooth kernel. The partial sum of `chi` up to `n` is the `H`-truncated
Fourier expansion of that kernel summed against `chi`: the `h`-th coefficient of the odd kernel is
of size `1/(pi*h)`, the Gauss sums attached to a primitive character have norm `sqrt q`, and what the
truncation drops is a kernel error of size `q * log q / H`. Summing the coefficients over the
harmonic range `h <= H` therefore gives `sqrt q / pi` times the harmonic sum plus that error, and the
cutoff `H = ceil (sqrt q * log q)` turns `log H` into `(1/2) log q + log log q` up to the additive
`log 2` that the ceiling costs. Feeding those two estimates and a harmonic sum bound into the display
is where the three coefficients `1/(2*pi)`, `1/pi` and `1` come from.

The lemmas below are exactly those steps:

* `leaf_odd_kernel_truncation` is the kernel step, the truncated Fourier expansion with its error;
* `leaf_log_harmonic_cutoff` is the estimate on the logarithm of the chosen cutoff `H`;
* `leaf_odd_small_modulus` is the finite range `q <= 8`, where the trivial bound on a partial sum of
  a non-principal character together with the explicit values of the right-hand side closes the case.

Everything is assembled in `leaf_odd_case_split`, which has the statement of the odd branch and uses
no hypothesis beyond the ones the display carries.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the kernel step of the odd branch. For an odd primitive character modulo `q >= 8` and any
cutoff `H >= 1`, every partial sum of `chi` is bounded by `sqrt q / pi` times the harmonic sum over
`h <= H` plus the truncation error of the odd sawtooth kernel, written here as `(2/5) * q * log q / H`:
the `h`-th coefficient of the odd kernel is at most `1/(pi*h)` and the Gauss sums have norm
`sqrt q`, which gives the harmonic term, and the dropped tail of the kernel is of size `q * log q / H`
with `2/5` a safe constant in front. This is one pointwise estimate in `n`, not the display. -/
theorem leaf_odd_kernel_truncation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hq8 : 8 ≤ q)
    (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) := by
  sorry

/-- LEAF: the cutoff estimate. For `q >= 8` the ceiling of `sqrt q * log q` is at most twice
`sqrt q * log q`, because `sqrt q * log q` is at least `4` there, and the logarithm of
`sqrt q * log q` is `log (sqrt q) + log (log q)`, that is `(1/2) log q + log log q`. So the log of the
cutoff is at most `(1/2) log q + log (log q) + log 2`. This is one elementary inequality, not the
display. -/
theorem leaf_log_harmonic_cutoff {q : ℕ} [NeZero q] (hq8 : 8 ≤ q) :
    log (Nat.ceil (sqrt (q : ℝ) * log (q : ℝ)) : ℝ) ≤
      1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2 := by
  sorry

/-- LEAF: the finite range `q <= 8` of the odd branch. For these moduli a partial sum of a
non-principal character is at most `q/2` in norm, and `q/2` is below the right-hand side of the
display for each of `q = 2, ..., 8`, so the display holds there with room to spare. This is a finite
range only and says nothing about `q >= 8`. -/
theorem leaf_odd_small_modulus {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hq8 : q ≤ 8) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- Arithmetic core of the assembly, with `u = sqrt q`, `v = log q` and `w = log log q`: after the
harmonic factor `1 + (v/2 + w + log 2)` and the truncation error `(2/5) * u` are put in, what is left
is `u * (1 + log 2) <= (3/5) * u * pi`, true because `log 2 < 0.694` and `pi > 3`. -/
private lemma odd_case_arith {u v w : ℝ} (hu : 0 ≤ u) :
    u / π * (1 + (1 / 2 * v + w + log 2)) + 2 / 5 * u ≤
      1 / (2 * π) * u * v + 1 / π * u * w + u := by
  have hπ : (0 : ℝ) < π := pi_pos
  have h3 : (3 : ℝ) < π := pi_gt_three
  have hl : log 2 < 0.6931471808 := log_two_lt_d9
  have key : u * (1 + (1 / 2 * v + w + log 2)) + 2 / 5 * (u * π) ≤
      u * v / 2 + u * w + u * π := by
    nlinarith [hu, h3, hl]
  have hπne : π ≠ 0 := ne_of_gt hπ
  field_simp
  nlinarith [key]

/-- The odd branch of the display, assembled from the three leaves: the finite range `q <= 8` is the
first leaf, and for `q >= 8` the kernel leaf is fed the cutoff `H = ceil (sqrt q * log q)`, the
logarithm of the cutoff from the second leaf, the harmonic sum bound `sum 1/h <= 1 + log H`, and the
truncation error `(2/5) * q * log q / H <= (2/5) * sqrt q` which the choice of `H` gives. -/
theorem leaf_odd_case_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  by_cases hsmall : q ≤ 8
  · exact leaf_odd_small_modulus χ hχ hq h_odd hsmall
  have hq8 : 8 ≤ q := Nat.le_of_lt (Nat.lt_of_not_le hsmall)
  have hqR : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq8
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hsqrt2 : (2 : ℝ) ≤ sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hqpos)]
    nlinarith
  have hlog8 : (2 : ℝ) ≤ log 8 := by
    have h8 : log (8 : ℝ) = 3 * log 2 := by
      rw [show ((8 : ℝ)) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h8]
    nlinarith [Real.log_two_gt_d9]
  have hlogq : (2 : ℝ) ≤ log (q : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) hqR)
  set H : ℕ := Nat.ceil (sqrt (q : ℝ) * log (q : ℝ)) with hHdef
  have hx4 : (4 : ℝ) ≤ sqrt (q : ℝ) * log (q : ℝ) := by nlinarith
  have hHle : sqrt (q : ℝ) * log (q : ℝ) ≤ (H : ℝ) := by
    rw [hHdef]
    exact Nat.le_ceil _
  have hH1 : 1 ≤ H := by
    rw [hHdef]
    have h : (1 : ℝ) ≤ ((Nat.ceil (sqrt (q : ℝ) * log (q : ℝ))) : ℝ) := by
      linarith [Nat.le_ceil (sqrt (q : ℝ) * log (q : ℝ))]
    exact_mod_cast h
  have hbound : (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) :=
    ciSup_le fun n => leaf_odd_kernel_truncation χ hχ hq h_odd hq8 H hH1 n
  have hharm : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) ≤ 1 + log (H : ℝ) := by
    have heq : (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rat.cast_inv, Rat.cast_natCast]
      simp [one_div]
    rw [heq]
    exact harmonic_le_one_add_log H
  have hlogH : log (H : ℝ) ≤ 1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2 := by
    rw [hHdef]
    exact leaf_log_harmonic_cutoff hq8
  have herr : 2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) ≤ 2 / 5 * sqrt (q : ℝ) := by
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
    have hxpos : (0 : ℝ) < sqrt (q : ℝ) * log (q : ℝ) := by linarith
    have hqsq : (q : ℝ) = sqrt (q : ℝ) * sqrt (q : ℝ) := by
      rw [Real.mul_self_sqrt (le_of_lt hqpos)]
    rw [div_le_iff₀ hHpos]
    nlinarith [hHle, hxpos, hqsq]
  have hfinal : sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) +
        2 / 5 * ((q : ℝ) * log (q : ℝ)) / (H : ℝ) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
    have hu : (0 : ℝ) ≤ sqrt (q : ℝ) / π := by positivity
    have h1 : sqrt (q : ℝ) / π * (∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ)) ≤
        sqrt (q : ℝ) / π * (1 + (1 / 2 * log (q : ℝ) + log (log (q : ℝ)) + log 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hu
      linarith
    have h2 := odd_case_arith (u := sqrt (q : ℝ)) (v := log (q : ℝ)) (w := log (log (q : ℝ)))
      (by positivity)
    linarith
  linarith

end LeanLab.HelfgottMajor.PolyaVinogradov123
