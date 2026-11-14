import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper

/-!
# Split of `book_zero_count_large_height_upper_short`
(`HelfgottMajor/SPLIT_book_zero_count_large_height_upper`)

The leaf asks, on the short heights `2 ≤ T ≤ 20` together with `2 * π * exp 1 ≤ q * T`, for the
upper side

`bookCount χ T - bookMain q T ≤ bookError q T`,

that is, for the half-weighted zero count `bookCount χ T` not to exceed the main term
`T / (2π) log (qT / (2πe))` by more than `0.15 log (qT) + 3.389`.

On this range the height is bounded, so `T / (2π) ≤ 20 / (2π) < 3.2` and the main term is at most
`3.2 log (qT / (2πe))`: the whole estimate is a statement about how fast the count can grow with
the conductor `q`, and the answer is a factor `T / (2π) + 0.15` in front of `log q`. There are
therefore two mechanisms, and the range is cut between them by comparing the conductor with the
height:

* `q = 1` is level one: one `L`-function, conductor contributing `log 1 = 0`, and the whole error
  `0.15 log T + 3.389` is at the disposal of a count that is an absolute constant, since the
  height never exceeds `20`. Here the main term can be dropped entirely, and that is what the
  first leaf does: it bounds the count by `3.389` alone, a statement with no main term in it.
  The assembly recovers the estimate from it using only `bookMain q T ≥ 0` on the range and
  `bookError q T ≥ 3.389`, both proved below without any input.
* `2 ≤ q ≤ T` puts both the conductor and the height at most `20`, so only the finitely many
  `L`-functions of conductor at most `20` are involved and the count is again an absolute
  constant; but here the main term already grows like `T / (2π) log q` and the constrained budget
  `0.15 log (qT) + 3.389` no longer carries the count on its own, so the main term has to be
  kept. This leaf is the target on a compact range: a finite amount of explicit information
  about finitely many `L`-functions would settle it, which is a different task from the next
  one, where the conductor is unbounded.
* `2 ≤ q` with `T < q` is the range where the conductor is the large parameter: `log q` can
  exceed anything the height supplies, the main term itself grows like `T / (2π) log q`, and
  the count is bounded above by that main term with the whole error left over. This is the
  uniform-in-`q` direction.

The last two leaves are the target statement restricted to a proper subrange of its hypotheses
rather than a decomposition of the estimate: the analytic input, the bound on the increment of
the argument of the completed `L`-function around the rectangle with corners `1 ± iT`, `-iT`,
is the same in both, which is why neither is weaker in content than the target, only in range.
The first leaf is weaker in content, not just in range.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- The main term is nonnegative as soon as `2πe ≤ q * T`. No input. -/
private lemma bookMain_nonneg_of_two_pi_e_le
    {T : ℝ} (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) : 0 ≤ bookMain q T := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpe : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have hqT : (0 : ℝ) < (q : ℝ) * T := lt_of_lt_of_le hpe hmain
  have hT0 : (0 : ℝ) < T := by nlinarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpe]
    linarith
  unfold bookMain
  exact mul_nonneg (by positivity) hlog

/-- LEAF. Level one, `q = 1`. The zeros counted are those of a single `L`-function with
imaginary part in the fixed stretch `0 ≤ Im ρ ≤ T ≤ 20`, so the half-weighted multiplicity sum
is an absolute constant: dropping the main term entirely, `bookCount χ T ≤ 3.389`, which is the
constant part of the error. This is strictly weaker than the target on this range: no main term
appears, and no dependence on `q` or on a Stirling increment. -/
theorem book_zero_count_large_height_upper_short_level_one (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) {T : ℝ} (hT : 1 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T ≤ 3.389 := by
  sorry

/-- LEAF. Small conductor, `2 ≤ q ≤ T ≤ 20`. Both the conductor and the height are at most
`20`, so the count is a multiplicity sum over the zeros below height `20` of one of the finitely
many `L`-functions of conductor at most `20`; but since `q ≤ T`, the main term
`T / (2π) log (qT / (2πe))` is already comparable with the error and cannot be dropped, so the
main term is kept and the leaf is the target inequality on this compact subrange. -/
theorem book_zero_count_large_height_upper_short_conductor_le_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hqT : (q : ℝ) ≤ T)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- LEAF. Large conductor, `2 ≤ q` with `T < q`. The conductor is the large parameter and is
not bounded by the height, so `log q` is free to grow, and the main term `T / (2π) log (qT /
(2πe))` grows like `T / (2π) log q` with it; the leaf is the target inequality on this subrange,
which is where the uniform-in-`q` bound on the increment of the argument of the completed
`L`-function is needed. -/
theorem book_zero_count_large_height_upper_short_conductor_gt_height
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq2 : 2 ≤ q) {T : ℝ}
    (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20) (hTq : T < (q : ℝ))
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  sorry

/-- Assembly: case `q = 1` gives the count by the constant `3.389` alone, and then
`bookCount χ T - bookMain q T ≤ 3.389 ≤ bookError q T` since the main term is nonnegative on
the range; otherwise `q ≥ 2` and the two remaining leaves cover `q ≤ T` and `T < q`. The target
is nowhere used. -/
theorem book_zero_count_large_height_upper_short_split (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hT2 : 2 ≤ T) (hT20 : T ≤ 20)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  rcases eq_or_ne q 1 with hq | hq
  · have hcount := book_zero_count_large_height_upper_short_level_one χ hχ hq hT hT20 hmain
    have hnn := bookMain_nonneg_of_two_pi_e_le (q := q) hmain
    have herr := bookError_ge_agy37 (q := q) hT
    linarith
  · have hq2 : 2 ≤ q := by
      have h0 : q ≠ 0 := NeZero.ne q
      omega
    rcases le_or_gt ((q : ℝ)) T with hqT | hTq
    · exact book_zero_count_large_height_upper_short_conductor_le_height χ hχ hq2 hT hT2 hT20
        hqT hmain
    · exact book_zero_count_large_height_upper_short_conductor_gt_height χ hχ hq2 hT hT2 hT20
        hTq hmain

#print axioms book_zero_count_large_height_upper_short_split

end LeanLab.HelfgottMajor.ZeroCount1623
