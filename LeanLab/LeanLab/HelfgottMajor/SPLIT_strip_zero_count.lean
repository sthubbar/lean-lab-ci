import LeanLab.HelfgottMajor.Decomp389c

/-!
# Split of `strip_zero_count` (`HelfgottMajor/Decomp389c`)

`strip_zero_count` bounds the total multiplicity of the zeros of `L(·,χ)` in the critical
strip with `|Im ρ| ≤ T`, for a primitive `χ` mod `q`, by

`T / π * log (qT / (2πe)) + 0.5 * log (qT) + 17.7`.

The statement is cut into four leaves, along the ranges on which the two mechanisms of the
count behave differently:

* `strip_count_summable` — the counting summand is summable, i.e. the set of strip zeros
  with `|Im ρ| ≤ T` is finite. This is the first half of the target's conjunction and
  carries no estimate at all.
* `strip_count_short_height`, `1 ≤ T ≤ 2` — the Stirling main term
  `T/π * log (qT/2π) − T/π` is negative or zero throughout, so this range gets no help
  from it; the zeros counted sit below height `2` and the constant `17.7` alone carries
  the inequality.
* `strip_count_band`, `2 ≤ T` and `q * T ≤ 2πe` — the band forces `q ≤ 2πe/T ≤ 8.6`, so
  both the conductor and the height are bounded and only finitely many zeros are counted,
  with a small multiplicity.
* `strip_count_main_range`, `2 ≤ T` and `2πe ≤ q * T` — here the Stirling main term is
  available and nonnegative, and this range carries the asymptotic content of the count.

The three ranges cover `T ≥ 1` and are disjoint; `strip_zero_count_split` chooses among
them. A cut by the height of the zero, rather than by the size of `T`, does not work here:
at height `2` the count already grows like `(2/π) log q`, while the budget of the target
spends `T/π * log (qT)` plus `0.5 * log (qT)` on `log q`, so the two ranges would have to
share that `0.5` in a ratio fixed by the true asymptotics, with no room to spare.
-/

namespace LeanLab.HelfgottMajor.Decomp389c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- LEAF. Finiteness step: the counting summand of the strip zeros with `|Im ρ| ≤ T` is
summable. The zeros of `L(·,χ)` in the strip are discrete and the closed box
`0 ≤ re ≤ 1`, `|im| ≤ T` is compact, so only finitely many of them lie in it, and the
multiplicity sum is a finite sum of natural numbers. This is the first conjunct of the
target and asserts no bound at all. -/
theorem strip_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (stripCountTerm χ T) := by
  sorry

/-- LEAF. Short height range, `1 ≤ T ≤ 2`. On this range `qT / (2πe) ≤ 2q / (2πe)`, so the
leading term `T/π * log (qT / (2πe))` is at most `T/π` in size and the inequality rests on
the constant `17.7` together with `0.5 * log (qT) ≥ 0`. The zeros counted here are the
zeros with `|Im ρ| ≤ 2`, whose number with multiplicity is a bounded multiple of `log q`;
the constant `17.7` is far above what that count needs, and for small `q` the range
contains no zero at all, so the statement is trivial there. -/
theorem strip_count_short_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) (hT2 : T ≤ 2) :
    (∑' ρ, stripCountTerm χ T ρ) ≤
      T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
        0.5 * log ((q : ℝ) * T) + 17.7 := by
  sorry

/-- LEAF. Bounded band, `2 ≤ T` and `q * T ≤ 2πe`. The band bounds the conductor by
`q ≤ 2πe / T ≤ πe < 8.6` while the height is at most `2πe`, so only finitely many zeros of
the finitely many `L`-functions involved, below the fixed height `2πe`, are counted, and
their number with multiplicity is a small absolute constant. The right side is at least
`16.7` on the band, since the leading term is at worst `−T/π ≥ −2πe/π`, which leaves room
for that count. -/
theorem strip_count_band (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hband : (q : ℝ) * T ≤ 2 * π * exp 1) :
    (∑' ρ, stripCountTerm χ T ρ) ≤
      T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
        0.5 * log ((q : ℝ) * T) + 17.7 := by
  sorry

/-- LEAF. Main range, `2 ≤ T` and `2πe ≤ q * T`. Here the argument principle for the
completed `L`-function applies: the Stirling estimate for the `Γ`-factor contributes
`T/π * log (qT/2π) − T/π`, the variation of the argument of `L` on the vertical line and on
the two horizontal segments contributes `O(log qT)`, and the multiplicities add the same
again, so that `0.5 * log (qT) + 17.7` covers both. Since `2πe ≤ qT` the leading term is
nonnegative on the whole range, so no separate small-height argument is needed here. -/
theorem strip_count_main_range (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) (hT2 : 2 ≤ T)
    (hmain : 2 * π * exp 1 ≤ (q : ℝ) * T) :
    (∑' ρ, stripCountTerm χ T ρ) ≤
      T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
        0.5 * log ((q : ℝ) * T) + 17.7 := by
  sorry

/-- Assembly: the target statement follows from the four leaves. The count is summable by
`strip_count_summable`, and the inequality holds on the short height range, on the band
`2 ≤ T`, `qT ≤ 2πe`, and on the main range `2 ≤ T`, `2πe ≤ qT`; these ranges exhaust
`T ≥ 1`. -/
theorem strip_zero_count_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (stripCountTerm χ T) ∧
      (∑' ρ, stripCountTerm χ T ρ) ≤
        T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * T) + 17.7 := by
  refine ⟨strip_count_summable q χ hχ T hT, ?_⟩
  by_cases hshort : T ≤ 2
  · exact strip_count_short_height q χ hχ T hT hshort
  · have hT2 : 2 ≤ T := (not_le.mp hshort).le
    by_cases hband : (q : ℝ) * T ≤ 2 * π * exp 1
    · exact strip_count_band q χ hχ T hT hT2 hband
    · exact strip_count_main_range q χ hχ T hT hT2 (not_le.mp hband).le

end LeanLab.HelfgottMajor.Decomp389c
