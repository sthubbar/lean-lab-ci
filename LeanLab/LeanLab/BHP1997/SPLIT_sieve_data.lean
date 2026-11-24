/-
Burst 2026-11-22, S83, BHP1997, split of `Decomp132.sieve_data`.
Source: P0069 Baker Harman Pintz 1997, Theorem 2 on page 3, its use on page 2 through
displays 1.3 to 1.6, and the proof in Sections 2 to 5.

`Decomp132.sieve_data` is the dead duplicate named in its audit note: its statement is
identical to `DecompC165b.sieve_data`, the live assembly on the route `AssemblyC165.theorem1`,
which is already cut into the paper's own steps, Section 2 circle method, Section 3 mean
values, Section 4 lower and upper sieve weights, Section 5 weights and Lemma 9. Earlier
attempts noted that importing `DecompC165b` into `Decomp132` closes an import cycle, since
`DecompC165b` imports `Decomp132`. This new file sits above both, so there is no cycle, and
the logical dependency is not circular either: nothing on the `DecompC165b` route uses
`Decomp132.sieve_data` or `Decomp132.theorem1`.

So no new LEAF is needed: the leaves of this split are the open leaves of `DecompC165b`.
`sieve_data_split` has exactly the statement of `Decomp132.sieve_data`, with no sorry of its
own. CONDITIONAL on the open leaves of the `DecompC165b` route. The sorry of
`Decomp132.sieve_data` stays in its own file, unchanged.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165b

namespace LeanLab.BHP1997.Decomp132
open Classical Real Filter

/-- Exactly the statement of `Decomp132.sieve_data`, P0069 Theorem 2 on page 3 with its use
on page 2. PROVED from the live assembly `DecompC165b.sieve_data`, whose statement is the same
proposition. No sorry here. CONDITIONAL on the open leaves of the `DecompC165b` route. -/
theorem sieve_data_split :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 :=
  LeanLab.BHP1997.DecompC165b.sieve_data

/-- The statement match, checked by the kernel: the type of `sieve_data_split` is the type of
the original `Decomp132.sieve_data`. -/
theorem sieve_data_split_twin : type_of% @sieve_data := @sieve_data_split

end LeanLab.BHP1997.Decomp132
