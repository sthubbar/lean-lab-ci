import LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt

/-!
Feed file for `KaracubaSplit.leaf_mvt_threshold` of
`LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt`: the mean value bound of Vinogradov at the
least admissible exponent `b_l = n l + [n(n+1)/4 + 1]`.

Source: A. A. Karacuba, Estimates of trigonometric sums by the method of I. M. Vinogradov
and their applications, Trudy Mat. Inst. Steklov 112 (1971) 241-255, chapter I section 1,
Lemma 1 on p. 243, which Karacuba cites from Vinogradov, The method of trigonometric sums in
the theory of numbers, his reference [1]. Karacuba gives no proof; the statement is a pure
citation, so it stays as one cited leaf, CITED-LEFT. The case `b = b_l` is exactly the
statement of Lemma 1 at its least exponent, and the induction to larger `b` is already proved
in the parent file.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- LEAF: Karacuba 1971, Lemma 1 on p. 243, the mean value theorem of Vinogradov, cited by
Karacuba from Vinogradov's monograph, his reference [1], at the least admissible exponent
`b = b_l = n l + [n(n+1)/4 + 1]`: for `n ≥ 12`, `l > 0`, `P > 0` the integral over the unit
cube of the `2 b_l`-th power of the Weyl sum is below
`D_l P^(2 b_l - n(n+1)/2 + n(n+1)/2 (1 - 1/n)^l)` with `D_l = (20 n)^(n(n+1) l / 2)`.
Class HARD: a cited analytic theorem, Vinogradov's induction on `l` with the explicit
constant, not split further. -/
theorem feed1122_vinogradov_mvt_least_exponent :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  sorry

/-- Assembly, statement copied verbatim from `leaf_mvt_threshold`, from the cited leaf. -/
theorem leaf_mvt_threshold_feed :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) :=
  feed1122_vinogradov_mvt_least_exponent

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
