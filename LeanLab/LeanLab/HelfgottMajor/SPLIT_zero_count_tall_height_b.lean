import LeanLab.HelfgottMajor.SPLIT_zero_count_explicit_upper

/-!
Second split of `zero_count_tall_height`, burst-20261122.

The first split, `SPLIT_zero_count_tall_height.lean`, cuts the range into four pieces, and its
very low height piece `zero_count_tall_low_height` is closed by calling the parent
`zero_count_tall_height` itself, so that split is circular on `1 ≤ t ≤ 2`.  This file removes
the circularity: on the whole range `1 ≤ t`, with no use of `2 * π * exp 1 ≤ q * t`, the target
is exactly the upper half of the two sided count `ZeroCount1623.strip_count`, which is
arXiv 1305.2897v4 pages 37 and 38, displays 4.25 and 4.26, itself reduced in `ZeroCount1623`
to the single cited input `ZeroCount1623.book_zero_count`, the book chapter 16 Lemma 16.9 count
with error display 16.21.  That input is already a LEAF in `ZeroCount1623.lean` and is split
further in `SPLIT_book_zero_count.lean`; no new LEAF is stated here.

So `zero_count_tall_height_split` below has no `sorry` of its own and depends on nothing but
`book_zero_count`.  Proof written by AI.  The theorem sits in the subnamespace `TallB` of
the original namespace so that it does not clash with the theorem of the same short name in
`SPLIT_zero_count_tall_height.lean` when both files are imported together.
-/

namespace LeanLab.HelfgottMajor.Decomp388a.TallB
open Real DecompJ1153

/-- The indicator set inside `zeroWeight` is `ZeroCount1623.stripZeros χ t`. -/
private theorem tallB_set_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ t}
      = ZeroCount1623.stripZeros χ t := by
  ext ρ
  simp [ZeroCount1623.stripZeros]

/-- `zeroCount` is the finite multiplicity sum over the strip zeros at height `t`. -/
private theorem tallB_eq_finset (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    zeroCount χ t = ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ t).toFinset,
      (ZeroCount1623.mult χ ρ : ℝ) := by
  classical
  have hset := tallB_set_eq q χ t
  have hfin : (ZeroCount1623.stripZeros χ t).Finite := ZeroCount1623.stripZeros_finite χ t
  have hzero : ∀ ρ : ℂ, ρ ∉ (ZeroCount1623.stripZeros χ t) → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    have h' : ρ ∉ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
        ρ.re < 1 ∧ |ρ.im| ≤ t} := by rw [hset]; exact hρ
    simp [zeroWeight, h']
  have houtside : ∀ ρ : ℂ, ρ ∉ hfin.toFinset → zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    exact hzero ρ (fun hc => hρ (hfin.mem_toFinset.mpr hc))
  have hinside : ∀ ρ : ℂ, ρ ∈ hfin.toFinset →
      zeroWeight χ t ρ = (ZeroCount1623.mult χ ρ : ℝ) := by
    intro ρ hρ
    have hc : ρ ∈ ZeroCount1623.stripZeros χ t := hfin.mem_toFinset.mp hρ
    simp [zeroWeight, ZeroCount1623.mult, hset, hc]
  unfold zeroCount
  rw [tsum_eq_sum (f := zeroWeight χ t) houtside]
  exact Finset.sum_congr rfl (fun ρ hρ => hinside ρ hρ)

/-- The explicit upper count on the whole range `1 ≤ t`, from `ZeroCount1623.strip_count`. -/
private theorem tallB_le_strip_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 := by
  rw [tallB_eq_finset q χ t,
    ← ZeroCount1623.tsum_zeroIdx χ t (fun z => (ZeroCount1623.mult χ z : ℝ))]
  exact ZeroCount1623.strip_count χ hχ t ht

/-- `zero_count_tall_height`, with exactly its statement, from the cited count
`ZeroCount1623.book_zero_count` through `ZeroCount1623.strip_count`.  The range hypothesis
`2 * π * exp 1 ≤ q * t` is not needed. -/
theorem zero_count_tall_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : 2 * π * exp 1 ≤ q * t) :
    zeroCount χ t ≤ t / π * log (q * t / (2 * π * exp 1)) +
      0.5 * log (q * t) + 17.7 :=
  tallB_le_strip_count q χ hχ t ht

end LeanLab.HelfgottMajor.Decomp388a.TallB
