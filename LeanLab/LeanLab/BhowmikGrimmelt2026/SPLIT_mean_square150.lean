/-
A split of `mean_square150` into four leaves, with an assembly that uses nothing but the leaves.

The sum in `MeanSquare38` runs over every `N ≤ X`, so the first thing to fix is the parity of
`N`.  At an odd `N` the singular series vanishes: a pair of odd summands cannot sum to an odd
number, and the factor at the prime two in the Euler product records exactly that, so the main
term `N 𝔖(N)` drops out and `E2 N` is just the weighted representation count `r2 N`.  Moreover,
at an odd `N` one of the two summands is even, hence a power of two, so `r2 N` is a short sum of
`vonMangoldt` values and its second moment over the odd `N ≤ X` costs only `X ^ 2` up to a
constant.  The even `N` are where the main term lives and where the whole analytic content sits,
and they are left as one leaf carrying the exponent `3 / 2 + 2 * Θ + ε`.  Finally, the exponent
comparison `2 ≤ 3 / 2 + 2 * Θ + ε` needs `Θ ≥ 1 / 2`, which the functional equation supplies: a
zero-free bound cannot hold below `Θ = 1 / 2`.

So the leaves are: (1) `Θ ≥ 1 / 2` under `ZeroBound Θ`; (2) the singular series vanishes at an
odd `N`; (3) the second moment of `r2` over the odd `N ≤ X` is bounded by a constant times `X ^ 2`;
(4) the second moment of `E2` over the even `N ≤ X` is bounded by a constant times
`X ^ (3 / 2 + 2 * Θ + ε)`.  The assembly adds (3) and (4) and absorbs (3) into (4) by (1).

AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150a
import LeanLab.BhowmikGrimmelt2026.SPLIT_meanSquare38

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

/-- LEAF. Step 1, the exponent comparison.  A zero-free bound at level `Θ` cannot hold with `Θ`
below one half: the functional equation puts a zero of the Riemann zeta function at real part
`1 / 2`, which is a zero of an `LFunction` of modulus `1` inside the open strip `0 < re s < 1`.
This is the step that later makes `2 ≤ 3 / 2 + 2 * Θ + ε` for every `ε > 0`, and hence lets the
`X ^ 2` bound on the odd `N` be absorbed into the target exponent. -/
theorem mean_square150_theta_ge_half {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  exact meanSquare38_theta_lower hZ

/-- LEAF. Step 2, the odd `N`: the singular series vanishes there.  The local factor at the prime
two counts the representations of `N` as a sum of two units modulo two; at an odd `N` the two
summands would have to be odd, whose sum is even, so that local count is zero and the whole
series `Σ_q μ(q)² c_q(N) / φ(q)²` vanishes.  This is the step that removes the main term
`N * singular N` from `E2 N` at an odd `N`. -/
theorem mean_square150_odd_singular (N : ℕ) (hN : Odd N) : singular N = 0 :=
  meanSquare38_odd_singular N hN

/-- LEAF. Step 3, the second moment over the odd `N`.  At an odd `N` a summand of `N` which is a
prime power is either odd or a power of two, and exactly one of the two summands is even, so
`r2 N` is at most `log 2` times a sum of `vonMangoldt` over the few shifted points `N - 2 ^ k`,
which is bounded by a fixed power of `log N`.  Squaring and summing over the odd `N ≤ X`
therefore costs a constant times `X ^ 2`.  The constant is chosen positive, and the bound is
genuinely a bound: at `X = 1` the sum is `(r2 1) ^ 2 = 0`. -/
theorem mean_square150_odd_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 ≤ C * (X : ℝ) ^ 2 :=
  meanSquare38_odd_energy

/-- LEAF. Step 4, the second moment over the even `N`: this is the analytic core, for the `N`
that carry a main term.  The circle method writes `r2` on the major arcs, where the zero-free
hypothesis governs the zeros and produces the exponent `2 * Θ` after Parseval, and bounds the
minor arcs by a second moment of the prime exponential sum; the two contributions combine to a
mean square of `E2` over the even `N ≤ X` of at most a constant times
`X ^ (3 / 2 + 2 * Θ + ε)`.  The constant depends on `Θ` and `ε` and is only asserted to exist.
This leaf is strictly weaker than the target, which asks the same bound for all `N ≤ X`. -/
theorem mean_square150_even_second_moment (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  exact meanSquare38_even_energy Θ hΘ hZ

/-- The mean square estimate, assembled from the four leaves.  Split the sum over `N ≤ X` into
the even and the odd `N`; on the odd `N` the main term drops out by Step 2, so that half becomes
the second moment of `r2` and is bounded by a constant times `X ^ 2` by Step 3; the even half is
bounded by Step 4.  Step 1 gives `2 ≤ 3 / 2 + 2 * Θ + ε`, so the `X ^ 2` term is dominated by
`X ^ (3 / 2 + 2 * Θ + ε)` and the two constants add. -/
theorem mean_square150_split : MeanSquare38 := by
  intro Θ hΘ hZ ε hε
  obtain ⟨Ce, heEven⟩ := mean_square150_even_second_moment Θ hΘ hZ ε hε
  obtain ⟨Co, hoPos, hoOdd⟩ := mean_square150_odd_second_moment
  refine ⟨Ce + Co, ?_⟩
  intro X hX
  have hhalf : (1 : ℝ) / 2 ≤ Θ := mean_square150_theta_ge_half hZ
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hexp : (2 : ℝ) ≤ 3 / 2 + 2 * Θ + ε := by linarith
  have hmono : (X : ℝ) ^ (2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hmono' : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    simpa using hmono
  have hsplit :
      (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
      ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 X)
      (p := fun N => Even N) (f := fun N => (E2 N) ^ 2)
  have hodd :
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 ≤
        Co * (X : ℝ) ^ 2 := by
    have hEq :
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 := by
      refine Finset.sum_congr ?_ ?_
      · ext N
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, Nat.not_even_iff_odd.mp h.2⟩,
          fun h => ⟨h.1, Nat.not_even_iff_odd.mpr h.2⟩⟩
      · intro N hN
        rw [Finset.mem_filter] at hN
        have h0 : singular N = 0 := mean_square150_odd_singular N hN.2
        simp only [E2, h0, mul_zero, sub_zero]
    rw [hEq]
    exact hoOdd X hX
  have heven := heEven X hX
  calc ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2
      = (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
          ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 := hsplit.symm
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ 2 := by linarith
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
      have hCo := mul_le_mul_of_nonneg_left hmono' hoPos.le
      linarith
    _ = (Ce + Co) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.mean_square150_split
