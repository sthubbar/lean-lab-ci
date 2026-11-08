import LeanLab.ExceptionalSet.SPLIT_leaf_poisson

/-!
Split of the sealed statement `leaf_poisson_index` of
`LeanLab.ExceptionalSet.SPLIT_leaf_poisson` into strictly smaller steps, plus an assembly
`leaf_poisson_index_split` whose statement is the sealed statement and whose proof uses only
the new leaves.

The statement says that every integer shift `m` other than `-⌊v⌋` and `-(⌊v⌋ + 1)` moves `v`
to a point at distance at least `1` from the origin. Writing `k = m + ⌊v⌋`, so that
`v + m = fract v + k`, the argument has four parts:

* the shift identity, rewriting `v + m` in terms of the fractional part of `v` and of `k`;
* the translation of the two forbidden shifts into the conditions `k ≠ 0` and `k ≠ -1`;
* the elementary dichotomy that an integer other than `0` and `-1` is either at least `1`
  or at most `-2`;
* the two one-sided estimates, using `0 ≤ fract v < 1`, that each of those ranges puts
  `fract v + k` at distance at least `1` from `0`.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Shift identity: the translated point `v + m` is the fractional part of `v` plus the
integer `m + ⌊v⌋`. This is the only place where the floor decomposition of `v` is introduced,
and it is one rearrangement of `Int.floor_add_fract`. -/
theorem leaf_poisson_index_shift (v : ℝ) (m : ℤ) :
    v + (m : ℝ) = Int.fract v + ((m + ⌊v⌋ : ℤ) : ℝ) := by
  push_cast
  linarith [Int.floor_add_fract v]

/-- LEAF. First forbidden shift: if `m ≠ -⌊v⌋` then the shifted integer `m + ⌊v⌋` is not
zero. One step of integer arithmetic, with no analysis. -/
theorem leaf_poisson_index_ne_zero (v : ℝ) (m : ℤ) (hm : m ≠ -⌊v⌋) :
    m + ⌊v⌋ ≠ 0 := by
  exact fun h => hm (add_eq_zero_iff_eq_neg.mp h)

/-- LEAF. Second forbidden shift: if `m ≠ -(⌊v⌋ + 1)` then the shifted integer `m + ⌊v⌋` is
not `-1`. One step of integer arithmetic, with no analysis. -/
theorem leaf_poisson_index_ne_neg_one (v : ℝ) (m : ℤ) (hm : m ≠ -(⌊v⌋ + 1)) :
    m + ⌊v⌋ ≠ -1 := by
  omega

/-- LEAF. Dichotomy: an integer which is neither `0` nor `-1` is at least `1` or at most
`-2`. A case distinction on `1 ≤ k`, with no real numbers involved. -/
theorem leaf_poisson_index_dichotomy (k : ℤ) (h0 : k ≠ 0) (h1 : k ≠ -1) :
    1 ≤ k ∨ k ≤ -2 := by
  omega

/-- LEAF. Upper range estimate: for an integer `k ≥ 1`, the point `fract v + k` is at
distance at least `1` from the origin, because `fract v ≥ 0`. -/
theorem leaf_poisson_index_upper (v : ℝ) (k : ℤ) (hk : 1 ≤ k) :
    1 ≤ |Int.fract v + (k : ℝ)| := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact (by linarith [Int.fract_nonneg v] : (1 : ℝ) ≤ Int.fract v + (k : ℝ)).trans
    (le_abs_self _)

/-- LEAF. Lower range estimate: for an integer `k ≤ -2`, the point `fract v + k` is at most
`-1`, hence again at distance at least `1` from the origin; this is where `fract v < 1` is
used. -/
theorem leaf_poisson_index_lower (v : ℝ) (k : ℤ) (hk : k ≤ -2) :
    1 ≤ |Int.fract v + (k : ℝ)| := by
  have hkR : (k : ℝ) ≤ -2 := by exact_mod_cast hk
  have hneg : Int.fract v + (k : ℝ) < -1 := by linarith [Int.fract_lt_one v]
  exact (by linarith : (1 : ℝ) ≤ -(Int.fract v + (k : ℝ))).trans (neg_le_abs _)

/-- Assembly: the sealed statement, from the shift identity, the two forbidden-shift
translations, the integer dichotomy and the two one-sided estimates. -/
theorem leaf_poisson_index_split (v : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) → 1 ≤ |v + (m : ℝ)| := by
  intro m hm hm'
  rw [leaf_poisson_index_shift v m]
  have h0 : m + ⌊v⌋ ≠ 0 := leaf_poisson_index_ne_zero v m hm
  have h1 : m + ⌊v⌋ ≠ -1 := leaf_poisson_index_ne_neg_one v m hm'
  rcases leaf_poisson_index_dichotomy (m + ⌊v⌋) h0 h1 with hk | hk
  · exact leaf_poisson_index_upper v (m + ⌊v⌋) hk
  · exact leaf_poisson_index_lower v (m + ⌊v⌋) hk

end LeanLab.ExceptionalSet.Decomp371d
