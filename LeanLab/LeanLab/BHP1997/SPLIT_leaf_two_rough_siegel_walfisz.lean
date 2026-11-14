/-
Split of the two-prime rough input `leaf_two_rough_siegel_walfisz` of `Decomp514a`
into three leaves, with the sealed statement left unchanged and the target neither
imported nor used.

Where the cut is made. The coefficient `lowerTwoTerms` is a finite sum over the ordered
prime pairs `p2 < p1` with `p1 * p2 ∣ m` whose exponent pair lies in the discarded region.
Write `n = m / (p1 * p2)` for the rough cofactor. The ordered two-prime expansion is cut
at `n = p2`: a pair is long when `p2 ≤ n` and short otherwise, which is the cut the argument
itself makes, since a long cofactor is the case where the rough variable is long enough to
carry the character saving, and a short one forces `n < p2 < p1` and hence `n ^ 3 < m`, a
short rough variable. The recorded obstruction for this input names exactly two missing
pieces, the ordered prime factor reindexing and the character cancellation after summing the
outer exponent pairs; the first leaf is the reindexing bookkeeping and is proved here, the
other two leaves are the cancellation on the two ranges. Each sub-sum is strictly smaller
than the whole family: it drops the other range of pairs, keeps the same quantifier block
and the same modulus range, and adds no hypothesis that the family does not already satisfy.
The extension at the end is the triangle inequality together with the two constants; it has
no unproved step.

Degenerate readings checked before keeping the leaves. At `m = 0` the divisor set is empty
(`Nat.divisors 0 = ∅`) and all three sums are zero, so the identity holds there too. At
`m = 1`, and at every `m` with no admissible ordered pair, both sides are zero as well. The
split condition `p2 ≤ m / (p1 * p2)` is the truncated natural division, which is harmless
here because the guard `p1 * p2 ∣ m` makes the quotient exact on every term that survives
it; when the guard fails the term is zero on both sides. At `ε > 0` the exponent
`11 / 20 + ε` stays in `(11 / 20, 11 / 20 + 1/10^8]`, so no negative power of `x` appears.
In the extension the constant is `max (2 * max C1 C2) 1`, which is at least one, so `x ≥ 1`,
hence `Real.log x ≥ 0` and the factor `Real.log x ^ (-A)` is nonnegative; that also excludes
`x = 0`. A negative leaf constant is allowed and does not break the extension: the two leaf
bounds are added and compared with `max (2 * max C1 C2) 1`, which dominates `C1 + C2` in both
sign regimes.

The two analytic leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-- LEAF 1 of 3. Step: the pointwise bookkeeping identity. The coefficient of `m` in the
ordered two-prime expansion equals its long-cofactor piece, where the rough cofactor `n`
satisfies `p2 ≤ n`, plus its short-cofactor piece, where `n < p2`. Both pieces keep the same
guards: both primes, `p2 < p1`, `p1 * p2 ∣ m`, and the discarded exponent region. Proved
here, so this leaf is closed. -/
theorem leaf_two_terms_pair_split (ε x : ℝ) (m : ℕ) :
    lowerTwoTerms ε x m = (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) + (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) := by
  have hp : ∀ p1 p2 : ℕ,
      (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) then rough (m / (p1 * p2)) p2 else (0 : ℝ)) =
        (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2) then rough (m / (p1 * p2)) p2 else 0) +
          (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2)) then rough (m / (p1 * p2)) p2 else 0) := by
    intro p1 p2
    by_cases hb : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
    · by_cases he : p2 ≤ m / (p1 * p2)
      · rw [ite_eq_left hb, ite_eq_left ⟨hb, he⟩, ite_eq_right (by simp [he]), add_zero]
      · rw [ite_eq_left hb, ite_eq_right (by simp [he]), ite_eq_left ⟨hb, he⟩, zero_add]
    · rw [ite_eq_right hb, ite_eq_right (fun h : (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧ p2 ≤ m / (p1 * p2) => hb h.1),
        ite_eq_right (fun h : (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) ∧ ¬ (p2 ≤ m / (p1 * p2)) => hb h.1), add_zero]
  unfold lowerTwoTerms
  calc (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
        (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) then rough (m / (p1 * p2)) p2 else (0 : ℝ)))
      = ∑ p1 ∈ m.divisors,
          ((∑ p2 ∈ m.divisors,
              (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
                  ∧ p2 ≤ m / (p1 * p2) then rough (m / (p1 * p2)) p2 else 0)) +
            (∑ p2 ∈ m.divisors,
              (if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
                  ∧ ¬ (p2 ≤ m / (p1 * p2)) then rough (m / (p1 * p2)) p2 else 0))) := by
        refine Finset.sum_congr rfl (fun p1 _ => ?_)
        exact (Finset.sum_congr rfl (fun p2 _ => hp p1 p2)).trans Finset.sum_add_distrib
    _ = (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) + (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) := Finset.sum_add_distrib

/-- LEAF 2 of 3. Step: the long-cofactor sub-sum. The ordered pairs whose coarse factor
`p1 * p2` leaves a rough cofactor of at least `p2` obey the logarithmic saving with a
polylogarithmic modulus. Strictly easier than the whole family: it keeps only the pairs with
`p2 ≤ m / (p1 * p2)`. Open. -/
theorem leaf_two_rough_long_cofactor {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 3 of 3. Step: the short-cofactor sub-sum. The ordered pairs whose rough cofactor is
smaller than `p2` obey the same logarithmic saving; there `n < p2 < p1`, so `n ^ 3 < m` and
the rough variable is short. Strictly easier than the whole family: it keeps only the pairs
with `¬ (p2 ≤ m / (p1 * p2))`. Open. -/
theorem leaf_two_rough_short_cofactor {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The sealed statement, proved from the three leaves: split the coefficient pointwise,
distribute the finite sum, apply the triangle inequality, and compare the two leaf constants
with `max (2 * max C1 C2) 1`, which is at least one so that `x ≥ 1` and the logarithmic
factor is nonnegative. -/
theorem leaf_two_rough_siegel_walfisz_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := leaf_two_rough_long_cofactor hε hε8 A hA
  obtain ⟨C2, h2⟩ := leaf_two_rough_short_cofactor hε hε8 A hA
  refine ⟨max (2 * max C1 C2) 1, ?_⟩
  intro x hx q hq hqA χ hχ t ht
  have hx1 : 1 ≤ x := le_trans (le_max_right (2 * max C1 C2) (1 : ℝ)) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hC1 : C1 ≤ max (2 * max C1 C2) 1 := by
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
      have h2' : max C1 C2 ≤ 2 * max C1 C2 := by linarith
      have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
      have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  have hC2 : C2 ≤ max (2 * max C1 C2) 1 := by
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h1' : C2 ≤ max C1 C2 := le_max_right C1 C2
      have h2' : max C1 C2 ≤ 2 * max C1 C2 := by linarith
      have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h1' : C2 ≤ max C1 C2 := le_max_right C1 C2
      have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  have hCs : C1 + C2 ≤ max (2 * max C1 C2) 1 := by
    have h1' : C1 ≤ max C1 C2 := le_max_left C1 C2
    have h2' : C2 ≤ max C1 C2 := le_max_right C1 C2
    rcases le_or_gt 0 (max C1 C2) with h | h
    · have h3' : 2 * max C1 C2 ≤ max (2 * max C1 C2) 1 := le_max_left _ _
      linarith
    · have h3' : (1 : ℝ) ≤ max (2 * max C1 C2) 1 := le_max_right _ _
      linarith
  set Y := x ^ (11 / 20 + ε) with hYs
  set L := Real.log x ^ (-A) with hLs
  have hY0 : 0 ≤ Y := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg hx1) _
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) with hSs
  have hpt : ∀ m : ℕ, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
      (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) + (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) := by
    intro m
    rw [leaf_two_terms_pair_split ε x m, ofReal_add]
    ring
  have hsplit : (∑ m ∈ S, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)) =
      (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
        (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) := by
    calc (∑ m ∈ S, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q))
        = ∑ m ∈ S, ((((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q) + (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) :=
          Finset.sum_congr rfl (fun m _ => hpt m)
      _ = (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
            (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) := Finset.sum_add_distrib
  rw [hsplit]
  have hb1 := h1 x (le_trans hC1 hx) q hq hqA χ hχ t ht
  have hb2 := h2 x (le_trans hC2 hx) q hq hqA χ hχ t ht
  have htri : ‖(∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)) +
      (∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q))‖ ≤
      ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ +
        ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ := norm_add_le _ _
  have hsum : ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ p2 ≤ m / (p1 * p2)
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ +
      ‖∑ m ∈ S, (((∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
            if (p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧ lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2))
            ∧ ¬ (p2 ≤ m / (p1 * p2))
            then rough (m / (p1 * p2)) p2 else (0 : ℝ)) : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤ C1 * Y * L + C2 * Y * L :=
    add_le_add hb1 hb2
  have hcancel : C1 * Y * L + C2 * Y * L = ((C1 + C2) * Y) * L := by ring
  have hstep : ((C1 + C2) * Y) * L ≤ ((max (2 * max C1 C2) 1) * Y) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs hY0) hL0
  linarith
