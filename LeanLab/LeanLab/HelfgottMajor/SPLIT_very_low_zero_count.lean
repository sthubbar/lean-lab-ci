import LeanLab.HelfgottMajor.Decomp389a

/-!
Split of `very_low_zero_count`, the very low zero paragraph of the major arcs paper.

The count of the strip zeros of a primitive character, weighted by multiplicity, is
cut into four steps.  The truncation height does not matter once it is at least one,
so the sum is the multiplicity count of the zeros of absolute imaginary part at most
one.  That count is the classical explicit count at height one, kept with the
archimedean term and with the coefficient `1 / π` of the height term at height one.
The last step is the arithmetic that turns `1 / π` into `0.819` and the archimedean
term into `16.8`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp389a

open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp269b

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.

Multiplier trick: `s ↦ (s - 1) * L χ s` is entire (for the trivial character the
pole-removed `LFunctionTrivChar₁` is used instead), it vanishes at every zero of `L χ`
inside the strip, and it is not identically zero.  Hence its zero set is discrete, and a
closed bounded box meets it finitely.

Carried from `LeanLab.HelfgottMajor.DecompJ1153.zeros_strip_finite` (same private proof,
that file is outside this target's import closure). -/
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

/-- LEAF. Summability step.  The strip zeros of the character below the height `T` are
counted with multiplicity, and this weighted count is a summable family: the zeros in a
bounded part of the strip are finitely many, so the term has finite support and the sum
is a genuine absolutely convergent sum. -/
theorem very_low_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) := by
  classical
  have hfin : (Set.Finite {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}) := zeros_strip_finite q χ T
  letI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := hfin.fintype
  exact summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))

/-- LEAF. Height step.  The very low count is the indicator of `|im| ≤ 1` applied to the
multiplicity, so for `T ≥ 1` the truncation at height `T` is invisible: the sum is the
multiplicity count of those zeros of the strip that have absolute imaginary part at most
one, and the larger index set contributes nothing outside it. -/
theorem very_low_count_le_strip_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}, veryLowCountTerm χ T ρ) ≤
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) := by
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
  have hR : (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑' z : ℂ, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}.indicator
        (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)) z := by
    rw [← tsum_subtype {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1}
      (fun z => (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ))]
    exact tsum_congr fun ρ => rfl
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
  rw [hL, hR, key]

/-- LEAF. Counting step.  The multiplicity count of the zeros of the primitive character in
the critical strip with absolute imaginary part at most one is bounded by the explicit count
at height one: the archimedean term `log (q / (2 π e)) / π` at height one, the half of
`log q` coming from the `q` dependence of the count, and the absolute constant `17.7`. -/
theorem strip_count_at_one_le_explicit (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 := by
  sorry

/-- LEAF. Arithmetic step.  The explicit count at height one is at most the printed budget:
`1 / π` is at most `0.319`, and `0.9 π` is at most `log 2 + log π + 1`, so the coefficient
of `log q` drops below `0.819` and the constant `17.7 - log (2 π e) / π` drops below `16.8`.
This step holds for every nonzero modulus and carries no character. -/
theorem explicit_count_arithmetic (q : ℕ) [NeZero q] :
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 ≤ 0.819 * log q + 16.8 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hpi0 : (0 : ℝ) < π := pi_pos
  have hpi1 : (3.1415 : ℝ) < π := pi_gt_d4
  have hpi2 : π < 3.1416 := pi_lt_d4
  have hlog2 : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hlog3 : (1.0986122885 : ℝ) < log 3 := log_three_gt_d9
  have hlogpi : (1.1436 : ℝ) < log π := by
    have hsplit : log π = log 3 + log (π / 3) := by
      rw [← log_mul (by norm_num) (by positivity)]
      ring_nf
    have hthird : (0 : ℝ) < π / 3 := by linarith
    have hlow : (1 : ℝ) - (π / 3)⁻¹ ≤ log (π / 3) := one_sub_inv_le_log_of_pos hthird
    have hinv : (π / 3)⁻¹ ≤ 3 / 3.1415 := by
      rw [inv_le_comm₀ hthird (by norm_num)]
      nlinarith
    rw [hsplit]
    linarith
  have hL : log (2 * π * exp 1) = 1 + log 2 + log π := by
    rw [log_mul (by positivity) (exp_pos 1).ne', log_mul (by norm_num) hpi0.ne', log_exp]
    ring
  have hsplit' : log (q / (2 * π * exp 1)) = log q - log (2 * π * exp 1) :=
    log_div hq0.ne' (by positivity)
  have hlogq : 0 ≤ log q := log_nonneg hq1
  have hcoef : 0.5 + 1 / π ≤ 0.819 := by
    have hinv : 1 / π ≤ 1 / 3.1415 :=
      one_div_le_one_div_of_le (by norm_num) hpi1.le
    linarith
  have hB : 0.9 * π < 1 + log 2 + log π := by nlinarith
  have hconst : (0.9 : ℝ) ≤ (1 / π) * (1 + log 2 + log π) := by
    have hmul : 0.9 * π * (1 / π) ≤ (1 + log 2 + log π) * (1 / π) :=
      mul_le_mul_of_nonneg_right hB.le (by positivity)
    have hsimp : 0.9 * π * (1 / π) = (0.9 : ℝ) := by field_simp
    nlinarith
  rw [hsplit', hL]
  have hstep : (1 / π) * (log q - (1 + log 2 + log π)) + 0.5 * log q + 17.7 =
      (0.5 + 1 / π) * log q - (1 / π) * (1 + log 2 + log π) + 17.7 := by
    field_simp
    ring
  rw [hstep]
  have h1 : (0.5 + 1 / π) * log q ≤ 0.819 * log q := by nlinarith
  nlinarith

/-- The very low zero count, assembled from the four steps above. -/
theorem very_low_zero_count_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 := by
  refine ⟨very_low_count_summable q χ hχ T hT, ?_⟩
  exact (very_low_count_le_strip_count q χ T hT).trans
    ((strip_count_at_one_le_explicit q χ hχ).trans (explicit_count_arithmetic q))

end LeanLab.HelfgottMajor.Decomp389a
