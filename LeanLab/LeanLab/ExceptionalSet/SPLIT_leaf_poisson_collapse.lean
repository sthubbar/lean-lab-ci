import LeanLab.ExceptionalSet.SPLIT_leaf_poisson

/-!
Split of the sealed statement `leaf_poisson_collapse` of
`LeanLab.ExceptionalSet.SPLIT_leaf_poisson` into four strictly smaller steps, plus an assembly
`leaf_poisson_collapse_split` whose statement is the sealed statement and whose proof uses only
the four leaves.

The steps, in the order in which the assembly uses them:

* away from the two integer shifts `-⌊v⌋` and `-(⌊v⌋ + 1)`, every term of the series vanishes,
  because there the frequency `v + m` is at distance at least one from the origin;
* a series over `ℤ` whose terms vanish off a two-element set of distinct indices equals the sum
  of those two terms;
* the term at the shift `-⌊v⌋` is the first term of the right-hand side;
* the term at the shift `-(⌊v⌋ + 1)` is the second term of the right-hand side.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371d

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck)

/-- LEAF. Vanishing step: every term of the series whose integer shift `m` is neither `-⌊v⌋`
nor `-(⌊v⌋ + 1)` is zero. The frequency `v + m` is then at distance at least one from the
origin, and the Fourier transform of `K` vanishes there. -/
theorem leaf_collapse_index_vanishes (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    ∀ m : ℤ, m ≠ -⌊v⌋ → m ≠ -(⌊v⌋ + 1) →
      eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)) = 0 := by
  intro m hm₀ hm₁
  rw [leaf_poisson_endpoint K hK hcont hsupp _ (leaf_poisson_index v m hm₀ hm₁),
    mul_zero]

/-- LEAF. Collapse step for a two-point series: a `ℤ`-indexed series over `ℂ` whose terms
vanish off two distinct indices `a` and `b` equals `F a + F b`. This is the step that turns the
vanishing of the tail into a finite sum. -/
theorem leaf_collapse_tsum_pair (F : ℤ → ℂ) (a b : ℤ) (hab : a ≠ b)
    (h : ∀ m : ℤ, m ≠ a → m ≠ b → F m = 0) :
    (∑' m : ℤ, F m) = F a + F b := by
  have hzero : ∀ m ∉ ({a, b} : Finset ℤ), F m = 0 := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact h m hm.1 hm.2
  rw [tsum_eq_sum hzero, Finset.sum_pair hab]

/-- LEAF. First surviving term: at the shift `-⌊v⌋` the frequency is exactly `Int.fract v` and
the phase is `-(α * ⌊v⌋)`, so the term is the first term of the right-hand side. -/
theorem leaf_collapse_term_floor (K : ℝ → ℂ) (v α : ℝ) :
    eC (α * ((-⌊v⌋ : ℤ) : ℝ)) * ftR K (v + ((-⌊v⌋ : ℤ) : ℝ)) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) := by
  simp only [Int.cast_neg, mul_neg, Int.fract, sub_eq_add_neg]

/-- LEAF. Second surviving term: at the shift `-(⌊v⌋ + 1)` the frequency is exactly
`Int.fract v - 1` and the phase is `-(α * (⌊v⌋ + 1))`, so the term is the second term of the
right-hand side. -/
theorem leaf_collapse_term_succ (K : ℝ → ℂ) (v α : ℝ) :
    eC (α * ((-(⌊v⌋ + 1) : ℤ) : ℝ)) * ftR K (v + ((-(⌊v⌋ + 1) : ℤ) : ℝ)) =
      eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  have hfreq : v + ((-(⌊v⌋ + 1) : ℤ) : ℝ) = Int.fract v - 1 := by
    simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.fract]
    ring
  rw [hfreq, Int.cast_neg, mul_neg]

/-- Assembly: the sealed statement, from the four leaves above. The two integer shifts
`-⌊v⌋` and `-(⌊v⌋ + 1)` are distinct, so the collapse step applies, and the two surviving
terms are identified with the two terms of the right-hand side. -/
theorem leaf_poisson_collapse_split (K : ℝ → ℂ) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v α : ℝ) :
    (∑' m : ℤ, eC (α * (m : ℝ)) * ftR K (v + (m : ℝ))) =
      eC (-(α * (⌊v⌋ : ℝ))) * ftR K (Int.fract v) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) * ftR K (Int.fract v - 1) := by
  have hne : (-⌊v⌋ : ℤ) ≠ -(⌊v⌋ + 1) := by omega
  rw [leaf_collapse_tsum_pair (fun m : ℤ => eC (α * (m : ℝ)) * ftR K (v + (m : ℝ)))
    (-⌊v⌋) (-(⌊v⌋ + 1)) hne (leaf_collapse_index_vanishes K hK hcont hsupp v α)]
  rw [leaf_collapse_term_floor K v α, leaf_collapse_term_succ K v α]

end LeanLab.ExceptionalSet.Decomp371d
