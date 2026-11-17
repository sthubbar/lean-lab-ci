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
  have h1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    linarith
  rw [Complex.star_def, ZeroCount1623.LFunction_inv_conj χ h1, hs, map_zero]

/-- A private helper: the `L`-function of the trivial character mod `q` is not analytic at `1`,
because `(s - 1) * L (s)` has a nonzero limit there while `s - 1` tends to zero. -/
private lemma not_analyticAt_LFunction_triv (q : ℕ) [NeZero q] :
    ¬ AnalyticAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) 1 := by
  intro h
  have hct : ContinuousAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) 1 :=
    h.continuousAt
  have h0 : Tendsto
      (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 0) := by
    have h1 : Tendsto (fun s : ℂ => s - 1) (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 0) := by
      have hsub : ContinuousAt (fun s : ℂ => s - 1) 1 :=
        continuousAt_id.sub continuousAt_const
      simpa using hsub.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ)
        (nhds (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1)) :=
      hct.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.mul h2
  have hres :
      Tendsto (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
        (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹))) :=
    DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
  have hne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)) ≠ 0 := by
    have h := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero (n := q)
    simpa [DirichletCharacter.LFunctionTrivChar₁] using h
  have hlim : (0 : ℂ) = ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) :=
    tendsto_nhds_unique h0 hres
  exact hne hlim.symm

/-- A private helper: the analytic order of `L (·, χ)` at `1` is zero, for every `χ`. Either
`χ` is nontrivial, where `L (1, χ) ≠ 0`, or `χ` is trivial and `L` is not even analytic there,
in which case the order is the junk value `0`. -/
private lemma analyticOrderNatAt_LFunction_one (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) 1 = 0 := by
  by_cases hχ : χ = 1
  · subst hχ
    exact analyticOrderNatAt_of_not_analyticAt (not_analyticAt_LFunction_triv q)
  · have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 1 :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt 1
    have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
      DirichletCharacter.LFunction_apply_one_ne_zero hχ
    simp [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hne]

/-- LEAF. The multiplicity half of the conjugation symmetry. The order of vanishing of
`L (·, χ)` at `s` equals the order of vanishing of `L (·, χ⁻¹)` at the reflected point
`star s`. The two functions are related by `L (χ⁻¹, star z) = star (L (χ, z))` and conjugation
is an isometry which preserves the order of a holomorphic function at a point, so the two orders
coincide; in particular the multiplicity of a zero is unchanged by reflection. This is an
identity, not an inequality, and it needs no hypothesis. -/
theorem order_conj_eq (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) s =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) := by
  by_cases hs : s = 1
  · subst hs
    have h2 : analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star (1 : ℂ)) =
        analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 : ℂ) := by rw [star_one]
    rw [analyticOrderNatAt_LFunction_one q χ, h2, analyticOrderNatAt_LFunction_one q χ⁻¹]
  · have hm := ZeroCount1623.mult_inv_conj χ hs
    simpa only [ZeroCount1623.mult, Complex.star_def] using hm.symm

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
  classical
  have him' : (star s).im = |s.im| := by
    rw [Complex.star_def, Complex.conj_im, abs_of_neg himneg]
  have hre0' : 0 < (star s).re := by simpa [Complex.star_def] using hre0
  have hre1' : (star s).re < 1 := by simpa [Complex.star_def] using hre1
  have him0' : 0 ≤ (star s).im := by rw [him']; exact abs_nonneg _
  have hle : |(star s).im| ≤ |s.im| + 1 := by rw [him', abs_abs]; linarith
  have hmem : star s ∈ (ZeroCount1623.stripZeros_finite χ⁻¹ (|s.im| + 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im) := by
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ZeroCount1623.stripZeros]
    exact ⟨⟨hz, hre0', hre1', hle⟩, him0'⟩
  have hzero : (star s).im ≠ 0 := by
    rw [him']
    have h' : |s.im| = -s.im := abs_of_neg himneg
    linarith
  have hneT : (star s).im ≠ |s.im| + 1 := by
    rw [him']
    intro h
    linarith
  have hw : ZeroCount1623.halfWeight (|s.im| + 1) (star s).im = 1 := by
    unfold ZeroCount1623.halfWeight
    exact ite_eq_right (not_or.mpr ⟨hzero, hneT⟩)
  have hnonneg : ∀ ρ ∈ (ZeroCount1623.stripZeros_finite χ⁻¹ (|s.im| + 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im),
      0 ≤ ZeroCount1623.halfWeight (|s.im| + 1) ρ.im * (ZeroCount1623.mult χ⁻¹ ρ : ℝ) := by
    intro ρ _
    unfold ZeroCount1623.halfWeight
    split
    · positivity
    · positivity
  have hsingle := Finset.single_le_sum hnonneg hmem
  unfold ZeroCount1623.bookCount
  calc (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (star s) : ℝ)
      = ZeroCount1623.halfWeight (|s.im| + 1) (star s).im *
          (ZeroCount1623.mult χ⁻¹ (star s) : ℝ) := by
        rw [hw, one_mul]
    _ ≤ ∑ ρ ∈ (ZeroCount1623.stripZeros_finite χ⁻¹ (|s.im| + 1)).toFinset.filter
          (fun ρ => 0 ≤ ρ.im),
          ZeroCount1623.halfWeight (|s.im| + 1) ρ.im * (ZeroCount1623.mult χ⁻¹ ρ : ℝ) := hsingle

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
