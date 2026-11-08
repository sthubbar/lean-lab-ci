import LeanLab.HelfgottMajor.DecompJ1233
import LeanLab.HelfgottMajor.Decomp388a

/-!
Split of `leaf_very_low_zero_count` in `HelfgottMajor.DecompJ1233`.

The target bounds the multiplicity weighted count of the nontrivial zeros of a
primitive `L`-function whose imaginary part is at most `1` by `0.819 * log q + 16.8`.
The height `T` in the indexing subtype of `veryLowCountTerm` only has to be at least
`1`: the indicator already cuts at height `1`, so the sum is the same multiplicity
count as the one at height `1`, and the estimate is the explicit zero count at height
one, in the printed form.  The written proof therefore has three steps, one for each
leaf below: the support of the counting term is finite, so the counting term is
summable; the counting sum is at most the multiplicity weighted zero count at height
one; and that count obeys the printed height one bound.  What remains after those
three is elementary arithmetic, which `Decomp388a.count_one_arithmetic` already
checks, so the assembly below has no sorry of its own.

The target `leaf_very_low_zero_count` is not used anywhere in this file.
-/

namespace LeanLab.HelfgottMajor.DecompJ1233
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389a Decomp388a

/-- CARRY.  The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Multiplier trick: `s ↦ (s - 1) * L χ s` is entire (for the trivial character the
pole-removed `LFunctionTrivChar₁` is used instead), it vanishes at every zero of `L χ`
inside the strip, and it is not identically zero.  Hence its zero set is discrete, and a
closed bounded box meets it finitely.

This proof block is carried verbatim from `LeanLab.HelfgottMajor.DecompJ1153`, where it
sits as the private theorem `zeros_strip_finite`; that file is inside this target's
import closure, so no new import is needed, but a `private` name cannot be referenced
from here. -/
private theorem zeros_strip_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  classical
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
  have hKc : IsCompact K := by
    have himg : K = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-T) T) := by
      ext z
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, abs_le.mp h3⟩, by apply Complex.ext <;> simp⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨⟨h1, h2⟩, h3⟩ := hp
        exact ⟨by simpa using h1, by simpa using h2, by simpa using abs_le.mpr h3⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  set g : ℂ → ℂ := if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q
    else fun s => (s - 1) * DirichletCharacter.LFunction χ s with hg
  have hg1 : χ = 1 → g = DirichletCharacter.LFunctionTrivChar₁ q := by
    intro h; rw [hg, if_pos h]
  have hg2 : χ ≠ 1 → g = fun s => (s - 1) * DirichletCharacter.LFunction χ s := by
    intro h; rw [hg, if_neg h]
  have hgd : Differentiable ℂ g := by
    by_cases h : χ = 1
    · rw [hg1 h]
      exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    · rw [hg2 h]
      have h1' : Differentiable ℂ fun s : ℂ => s - 1 := by fun_prop
      exact h1'.mul (DirichletCharacter.differentiable_LFunction h)
  have hex : ∃ w, g w ≠ 0 := by
    by_cases h : χ = 1
    · refine ⟨1, ?_⟩
      rw [hg1 h]
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · refine ⟨2, ?_⟩
      rw [hg2 h]
      have h2 : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
        DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl h) (by norm_num)
      exact mul_ne_zero (by norm_num) h2
  have hne : ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 → z.re < 1 → g z = 0 := by
    intro z hL h1
    by_cases h : χ = 1
    · have hz1 : z ≠ 1 := by
        rintro rfl
        rw [Complex.one_re] at h1
        exact absurd h1 (by norm_num)
      have hL1 : DirichletCharacter.LFunctionTrivChar q z = 0 := by
        have h' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z = 0 := by
          rw [← h]; exact hL
        exact h'
      rw [hg1 h]
      simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1, hL1, mul_zero]
    · rw [hg2 h]
      simp only [hL, mul_zero]
  have hcod : g ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete (f := g)
      (hgd.differentiableOn.analyticOnNhd isOpen_univ) hex.choose_spec
  rw [Set.preimage_compl] at hcod
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  refine Set.Finite.subset ((hKc.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)) ?_
  rintro z ⟨hL, h0, h1, him⟩
  exact ⟨⟨le_of_lt h0, le_of_lt h1, him⟩, hne z hL h1⟩

/-- LEAF. Summability of the very low counting term. The terms that can be nonzero
are the nontrivial zeros of the `L`-function with imaginary part at most `1`, weighted
by their multiplicity; the zeros are isolated and the height cut bounds them, so this
support is finite and the term is summable. No critical line hypothesis is used. -/
theorem very_low_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) := by
  classical
  have hfin : (Set.Finite {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) := zeros_strip_finite q χ T
  letI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := hfin.fintype
  exact summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))

/-- LEAF. The very low counting sum is at most the multiplicity weighted zero count at
height one. A zero that the indicator keeps has imaginary part at most `1`, hence at
most `T` because `T` is at least `1`, so its index condition is exactly the one of
the zero count at height one, and every multiplicity is nonnegative. -/
theorem very_low_count_le_zero_count_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ, veryLowCountTerm χ T ρ) ≤ zeroCount χ 1 := by
  classical
  have hL : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, veryLowCountTerm χ T ρ) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.indicator
        (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
          (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z) z := by
    rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
      (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z)]
    refine tsum_congr fun ρ => ?_
    by_cases h : |ρ.val.im| ≤ 1 <;> simp [veryLowCountTerm, Set.indicator, h]
  have key : (∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.indicator
        (fun z => Set.indicator {z : ℂ | |z.im| ≤ 1}
          (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z) z) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}.indicator
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z := by
    refine tsum_congr fun z => ?_
    by_cases h1 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}
    · have h2 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} :=
        ⟨h1.1, h1.2.1, h1.2.2.1, le_trans h1.2.2.2 hT⟩
      rw [Set.indicator_of_mem h2]
      rw [Set.indicator_of_mem (show z ∈ {w : ℂ | |w.im| ≤ 1} from h1.2.2.2)]
      rw [Set.indicator_of_mem h1]
    · by_cases h2 : z ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}
      · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1]
        have him : ¬ |z.im| ≤ 1 := fun h => h1 ⟨h2.1, h2.2.1, h2.2.2.1, h⟩
        simp [Set.indicator, him]
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h1]
  have hR : (∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}.indicator
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z) =
      zeroCount χ 1 := by
    rw [zeroCount]
    exact tsum_congr fun z => rfl
  rw [hL, key, hR]

/-- LEAF. The explicit upper count at height one, with the main term kept: multiplicity
weighted nontrivial zeros of height at most one, bounded by
`log (q / (2 * π * exp 1)) / π + log q / 2 + 17.7`.  This is the height one instance of
the quantitative count for primitive characters. -/
theorem zero_count_one_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ 1 ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 := by
  sorry

/-- The sealed statement, assembled from the three leaves above. The last step is the
elementary conversion of the height one count into the printed coefficients. -/
theorem leaf_very_low_zero_count_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  refine ⟨very_low_count_summable q χ T hT, ?_⟩
  calc (∑' ρ, veryLowCountTerm χ T ρ)
      ≤ zeroCount χ 1 := very_low_count_le_zero_count_one q χ T hT
    _ ≤ 1 / π * log ((q : ℝ) / (2 * π * exp 1)) + 0.5 * log (q : ℝ) + 17.7 :=
        zero_count_one_bound q χ hχ
    _ ≤ 0.819 * log (q : ℝ) + 16.8 :=
        count_one_arithmetic (q : ℝ) (by exact_mod_cast NeZero.one_le)

end LeanLab.HelfgottMajor.DecompJ1233
