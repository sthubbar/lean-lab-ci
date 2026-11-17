import LeanLab.HelfgottMajor.SPLIT_zero_multiplicity_subexponential

/-!
Splitting `order_le_book_count_lower` into three steps.

The target counts a zero of `L (·, χ)` with negative imaginary part by the multiplicity
weighted zero count of the inverse character, taken at the reflected height `|im| + 1`. The
proof has two ingredients: the conjugation symmetry of `L (·, χ)`, which reflects a zero below
the real axis into a zero of `χ⁻¹` above it with the same multiplicity, and the one sided zero
count for a character at a point of the closed upper half plane.

* `zero_of_conj_neg_im` is the vanishing half of the symmetry: the reflected point is a zero of
  the inverse character. Nothing about multiplicities is claimed.
* `order_conj_eq` is the multiplicity half: the analytic order of `L (·, χ)` at the point below
  the axis and the analytic order of `L (·, χ⁻¹)` at the reflected point agree.
* `order_le_book_count_reflected` is the counting input, stated at the reflected point and
  already at the height `|im| + 1` of the target, so no height rewriting is left for the
  assembly.

`order_le_book_count_lower` and `order_le_book_count_upper` are not used.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The vanishing half of the conjugation symmetry. A zero of `L (·, χ)` at a point `s`
below the real axis is, after reflection in the real axis, a zero of the inverse character:
`L (χ⁻¹, star s) = 0`, where `star` is complex conjugation. The reflection is the termwise
identity `L (χ⁻¹, star z) = star (L (χ, z))` of the Dirichlet series, continued to the strip and
evaluated at the zero. The hypothesis `s.im < 0` only matches the use site; the identity itself
holds on the whole plane. -/
theorem zero_of_conj_neg_im (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : DirichletCharacter.LFunction χ s = 0) (himneg : s.im < 0) :
    DirichletCharacter.LFunction χ⁻¹ (star s) = 0 := by
  sorry

/-- LEAF. The multiplicity half of the conjugation symmetry. The order of vanishing of
`L (·, χ)` at `s` equals the order of vanishing of `L (·, χ⁻¹)` at the reflected point
`star s`. The two functions are related by `L (χ⁻¹, star z) = star (L (χ, z))` and conjugation
is an isometry which preserves the order of a holomorphic function at a point, so the two orders
coincide; in particular the multiplicity of a zero is unchanged by reflection. This is an
identity, not an inequality, and it needs no hypothesis. -/
theorem order_conj_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) s =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) := by
  sorry

/-- LEAF. The counting input at the reflected point. If the reflected point `star s` is a zero of
`L (·, χ⁻¹)`, lies in the open strip and in the closed upper half plane, and has height at least
`100`, then the multiplicity weighted count `bookCount χ⁻¹ (|im| + 1)` at the height of the
target dominates its analytic order. This is the one sided explicit zero count of the file
applied to the inverse character at the reflected point, with the height rewritten from
`|(star s).im| + 1` to `|s.im| + 1`; only the upper half plane is needed, so it is weaker than
the two sided count. -/
theorem order_le_book_count_reflected (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hz : DirichletCharacter.LFunction χ⁻¹ (star s) = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) (himneg : s.im < 0) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) : ℝ) ≤
      ZeroCount1623.bookCount χ⁻¹ (|s.im| + 1) := by
  sorry

/-- The target, assembled from the three steps. The reflection turns the zero of `χ` below the
axis into a zero of `χ⁻¹` above it, the order identity transports the multiplicity to the
reflected point, and the counting leaf bounds that multiplicity by the count of `χ⁻¹` at the
height `|im| + 1` of the target. No case distinction is left, because the hypothesis already
fixes the sign of the imaginary part. -/
theorem order_le_book_count_lower_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : DirichletCharacter.LFunction χ s = 0) (hre0 : 0 < s.re) (hre1 : s.re < 1)
    (him : 100 ≤ |s.im|) (himneg : s.im < 0) :
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) s : ℝ) ≤
      ZeroCount1623.bookCount χ⁻¹ (|s.im| + 1) := by
  have hz : DirichletCharacter.LFunction χ⁻¹ (star s) = 0 :=
    zero_of_conj_neg_im q χ s hs himneg
  have hcount : (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) : ℝ) ≤
      ZeroCount1623.bookCount χ⁻¹ (|s.im| + 1) :=
    order_le_book_count_reflected q χ s hz hre0 hre1 him himneg
  have hord : analyticOrderNatAt (DirichletCharacter.LFunction χ) s =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) :=
    order_conj_eq q χ s
  rw [hord]
  exact hcount
