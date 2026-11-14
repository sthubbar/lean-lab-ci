/-
Split of `leaf_four_rough_siegel_walfisz` in LeanLab.BHP1997.Decomp514a into three leaves.

The sealed statement is unchanged and is neither imported nor used here. It asks, for a small
positive `ε`, and then for every `A > 0`, a constant `C` such that for every real `x ≥ C`, every
modulus `q` with `1 ≤ q ≤ (log x)^A`, every non-principal character `χ` modulo `q` and every real
`t ≤ 2 x^(11/20+ε)`, the four-prime part `lowerFourTerms` of the lower coefficient, summed over
the right interval truncated at `t` and against `χ`, is at most `C x^(11/20+ε) (log x)^(-A)`.

The split follows the way such a sum is treated: the sum is cut at the midpoint of the right
interval, and each half is further cut into the integers that keep a large prime factor, where
the character sum has to be won, and the integers that keep none, where the coefficient already
vanishes. Leaf 1 is the lower half, leaf 2 the upper half, leaf 3 the vanishing on the
complement of the large-prime-factor set. Each of leaves 1 and 2 is strictly weaker than the
statement: leaf 1 restricts `t` to the lower half of the interval, and both leaves drop every
integer without a large prime factor, which is a proper sub-collection of the summands of the
statement and never the whole of it. Leaf 3 is not an estimate at all, it is the identity that
the part of the sum off that set is zero, which holds because `lowerFourTerms` vanishes on every
integer that keeps no prime factor above the scale `Z ^ c1`.

The assembly `leaf_four_rough_siegel_walfisz_split` restates the statement. It splits the
sum over the truncated interval at `(3/2) x^(11/20+ε)`: the prefix is the truncated interval up
to the minimum of `t` and that midpoint, which is exactly the index set of leaf 1, and the
remainder is the set of integers strictly above the midpoint and at most `t`, which is exactly
the index set of leaf 2. On each of the two pieces leaf 3 removes the integers without a large
prime factor, and the two halves are then bounded by leaves 1 and 2 and added by the triangle
inequality, with one common constant `2 * max (max C1 C2) 1` chosen at least one so that the
weight `x^(11/20+ε) (log x)^(-A)` is nonnegative on `x ≥ 1`. It has no unfinished step of its
own and does not name the sealed statement.

Leaves 1 and 2 remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.Decomp514a
open Classical Complex Decomp132 DecompC165b DecompC165d LeanLab.BHP1997.LowerShortC165
open scoped BigOperators
set_option maxHeartbeats 400000

/-! ### The two halves of the interval, on the integers with a large prime factor -/

/-- LEAF: step 1 of the split, the lower half of the right interval. The four-prime part of the
lower coefficient, summed against a non-principal character over the right interval truncated at
`t`, where `t` stays below the midpoint `(3/2) x^(11/20+ε)` of the interval and where the
summand is kept only on integers that keep a prime factor at or above the scale `Z ^ c1`, carries
the factor `x^(11/20+ε) (log x)^(-A)` for every `A`, uniformly in `q ≤ (log x)^A` and in `t`.
This is the unordered prime expansion of the four-prime sum on the first half of the interval,
with the character sum in the last prime variable. -/
theorem leaf_four_rough_low_coarse {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 3 / 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).filter
              (fun m : ℕ => RoughAbove ε x m),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: step 2 of the split, the upper half of the right interval. The same four-prime sum
against a non-principal character, over the integers of the right interval strictly above the
midpoint `(3/2) x^(11/20+ε)` and at most `t`, again kept only on integers that keep a prime
factor at or above the scale `Z ^ c1`. The index set is a proper part of the index set of the
sealed statement for every `t`, and empty for `t` below the midpoint, so this is strictly weaker
than the statement. This is the same unordered prime expansion on the second half of the
interval, where the cofactor of the four primes is shorter. -/
theorem leaf_four_rough_tail_coarse {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ,
          ‖∑ m ∈ ((rightInterval ε x).filter
                (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t)).filter
              (fun m : ℕ => RoughAbove ε x m),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: step 3 of the split, the integers with no large prime factor contribute nothing. For
every finite set of integers, the part of the sum that keeps no prime factor at or above the
scale `Z ^ c1` is zero, because a nonzero value of `lowerFourTerms` forces such a prime factor:
the four outer primes of the coefficient are ordered and each carries an exponent at or above
`c1`, so the smallest of them already bounds every prime factor of the integer from below. This
is an identity, not an estimate: it says which integers the coefficient can live on, and it
carries no saving in `x`. It is not one of the two halves. -/
theorem leaf_four_rough_off_support (ε x : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) :
    ∑ m ∈ S.filter (fun m : ℕ => ¬ RoughAbove ε x m),
      ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) = 0 := by
  refine Finset.sum_eq_zero fun m hm => ?_
  have h2 : ¬ RoughAbove ε x m := (Finset.mem_filter.mp hm).2
  have hz : lowerFourTerms ε x m = 0 := by
    by_contra hne
    exact h2 (lowerFourTerms_support hne)
  simp [hz]

/-- The assembly, with nothing open. The same statement as the sealed leaf, built from the three
leaves above. For a given `A` the two halves supply constants `C1` and `C2`; with
`K = max (max C1 C2) 1` and the common constant `2 * K` both halves are available at the same
scale and at every `x ≥ 1`. The truncated interval is split at the midpoint into the prefix up
to `min t (3/2) x^(11/20+ε)` and the remainder `(3/2) x^(11/20+ε) < m ≤ t`; on each piece leaf 3
removes the integers without a large prime factor, the two pieces are bounded by leaves 1 and 2,
and the triangle inequality adds them. No step uses the sealed statement. -/
theorem leaf_four_rough_siegel_walfisz_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := leaf_four_rough_low_coarse hε hε8 A hA
  obtain ⟨C2, h2⟩ := leaf_four_rough_tail_coarse hε hε8 A hA
  refine ⟨2 * max (max C1 C2) 1, fun x hx q hq hqA χ hχ t ht => ?_⟩
  set K := max (max C1 C2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ 2 * K := by linarith
    linarith
  have hF : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hC1K : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2K : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  -- the cut of the truncated interval at the midpoint
  have hkey :
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => (m : ℝ) ≤ min t (3 / 2 * x ^ (11 / 20 + ε))),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) +
          ∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) := by
    have hset : ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)).filter
          (fun m : ℕ => ¬ (m : ℝ) ≤ 3 / 2 * x ^ (11 / 20 + ε)) =
        (rightInterval ε x).filter
          (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t) := by
      ext m
      simp only [Finset.mem_filter, not_le]
      tauto
    rw [← Finset.sum_filter_add_sum_filter_not
        (s := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t))
        (p := fun m : ℕ => (m : ℝ) ≤ 3 / 2 * x ^ (11 / 20 + ε)),
      prefix_filter_min (rightInterval ε x) t (3 / 2 * x ^ (11 / 20 + ε)), hset]
  rw [hkey]
  -- the lower half: leaf 3 removes the integers without a large prime factor, leaf 1 bounds it
  have hlow :
      ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => (m : ℝ) ≤ min t (3 / 2 * x ^ (11 / 20 + ε))),
          ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ m ∈ ((rightInterval ε x).filter
              (fun m : ℕ => (m : ℝ) ≤ min t (3 / 2 * x ^ (11 / 20 + ε)))).filter
            (fun m : ℕ => RoughAbove ε x m),
          ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) := by
    rw [← Finset.sum_filter_add_sum_filter_not
        (s := (rightInterval ε x).filter
          (fun m : ℕ => (m : ℝ) ≤ min t (3 / 2 * x ^ (11 / 20 + ε))))
        (p := fun m : ℕ => RoughAbove ε x m),
      leaf_four_rough_off_support ε x q χ _, add_zero]
  have hupper :
      ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t),
          ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
        ∑ m ∈ ((rightInterval ε x).filter
              (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t)).filter
            (fun m : ℕ => RoughAbove ε x m),
          ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) := by
    rw [← Finset.sum_filter_add_sum_filter_not
        (s := (rightInterval ε x).filter
          (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t))
        (p := fun m : ℕ => RoughAbove ε x m),
      leaf_four_rough_off_support ε x q χ _, add_zero]
  have hb1 := h1 x (by linarith) q hq hqA χ hχ (min t (3 / 2 * x ^ (11 / 20 + ε)))
    (min_le_right _ _)
  have hb2 := h2 x (by linarith) q hq hqA χ hχ t
  have hs1 : ‖∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => (m : ℝ) ≤ min t (3 / 2 * x ^ (11 / 20 + ε))),
      ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
      K * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
    rw [hlow]
    refine (hb1.trans ?_)
    calc C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = C1 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ K * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right hC1K hF
  have hs2 : ‖∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => 3 / 2 * x ^ (11 / 20 + ε) < (m : ℝ) ∧ (m : ℝ) ≤ t),
      ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
      K * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
    rw [hupper]
    refine (hb2.trans ?_)
    calc C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = C2 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ K * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right hC2K hF
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hs1 hs2) (le_of_eq ?_)
  ring

end LeanLab.BHP1997.Decomp514a
