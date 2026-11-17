import LeanLab.HelfgottMajor.SPLIT_polya_vinogradov_4_20

/-!
Split of `leaf_even_case`, the even branch of the explicit Polya-Vinogradov inequality of the
parent module `SPLIT_polya_vinogradov_4_20`.

The even branch comes from two steps. First, the `h`-th Fourier coefficient of the even sawtooth
kernel is summed over the truncated harmonic range `h <= H`, which leaves the partial sum of `chi`
bounded by the term `q / H` for the modulus divided by the truncation length, plus a
`sqrt q log H` term whose coefficient is `4 / pi ^ 2`, plus a bounded remainder `sqrt q / 4`;
that step carries the free parameter `H` and no choice of it. Second, `H` is chosen of the size of
`sqrt q`, so that `log H` turns into `log q / 2`, the first term becomes the printed
`2 / pi ^ 2 * sqrt q * log q`, and the correction term in `log log q` together with the printed
`3 / 2 * sqrt q` covers what is left of the remainder.

The two steps are the two leaves below: the truncated harmonic-range estimate with free `H`, and
the choice `H = sqrt q` with the arithmetic of the constants, stated as an inequality between
explicit real expressions in `q`. The assembly instantiates the first leaf at `H = sqrt q` and
closes with the second; it uses no definition, and `M(q)` stays the supremum of the norms of the
partial sums, written out inline.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the truncated harmonic-range estimate for the even branch. For an even primitive
character modulo `q > 1`, every partial sum of `chi` up to a length `n` has norm at most
`q / H + 4 / pi ^ 2 * sqrt q * log H + sqrt q / 4`, for every truncation length `H` between `1`
and `q`. This is the step that sums the Fourier coefficients of the even sawtooth kernel over the
range `h <= H` and keeps the remainder; it makes no choice of `H`, so it is one estimate and not
the whole branch. Its instances at `H = 1` (here the bound is `q` up to the remainder, and the
partial sums have norm at most `q`) and at `H = q` are both true, as is the case `n = 0`, where the
sum is empty. -/
theorem leaf_even_fourier_truncation_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) (n : ℕ) (H : ℝ)
    (hH_one : 1 ≤ H) (hH_q : H ≤ (q : ℝ)) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      (q : ℝ) / H + 4 / π ^ 2 * sqrt q * log H + 1 / 4 * sqrt q := by
  sorry

/-- LEAF: the choice of the truncation length and the arithmetic of the constants. For `q` at
least `2`, the bound of the first leaf taken at `H = sqrt q`, that is
`q / sqrt q + 4 / pi ^ 2 * sqrt q * log (sqrt q) + sqrt q / 4`, is at most the printed right-hand
side `2 / pi ^ 2 * sqrt q * log q + 4 / pi ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q`. This is
where `q / sqrt q = sqrt q` and `log (sqrt q) = log q / 2` are used, so that the `log q` terms
match with coefficient `2 / pi ^ 2`, and where the remaining `log log q` and constant terms are
checked to cover the leftover `sqrt q / 4` of the remainder. The case `q = 2` is the sharpest one
of the inequality, and it holds there with about a tenth of `sqrt q` to spare. -/
theorem leaf_even_harmonic_optimization {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ) / sqrt q + 4 / π ^ 2 * sqrt q * log (sqrt q) + 1 / 4 * sqrt q ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  sorry

/-- The even branch, assembled from the two leaves: bound every partial sum by the truncated
harmonic-range estimate at the truncation length `H = sqrt q`, which lies in `[1, q]`, and then
replace that bound by the printed right-hand side with the arithmetic of the constants. -/
theorem leaf_even_case_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := Nat.pos_of_ne_zero hq0
    exact_mod_cast this
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hH_one : (1 : ℝ) ≤ sqrt (q : ℝ) := by
    rw [Real.one_le_sqrt]
    linarith
  have hH_q : sqrt (q : ℝ) ≤ (q : ℝ) := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr hq1
  refine ciSup_le (fun n => ?_)
  have hmain :=
    leaf_even_fourier_truncation_bound χ hχ hq h_even n (sqrt (q : ℝ)) hH_one hH_q
  calc ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖
      ≤ (q : ℝ) / sqrt (q : ℝ) + 4 / π ^ 2 * sqrt (q : ℝ) * log (sqrt (q : ℝ)) +
          1 / 4 * sqrt (q : ℝ) := hmain
    _ ≤ 2 / π ^ 2 * sqrt (q : ℝ) * log (q : ℝ) +
          4 / π ^ 2 * sqrt (q : ℝ) * log (log (q : ℝ)) + 3 / 2 * sqrt (q : ℝ) :=
        leaf_even_harmonic_optimization hq2

end LeanLab.HelfgottMajor.PolyaVinogradov123
