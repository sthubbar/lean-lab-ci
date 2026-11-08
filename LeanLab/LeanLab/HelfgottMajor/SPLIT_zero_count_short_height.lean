import LeanLab.HelfgottMajor.SPLIT_zero_count_explicit_upper

/-!
Split of the short height range of the explicit upper count for the nontrivial zeros of a
primitive Dirichlet `L`-function.

On the range `q * t ≤ 2 * π` with `t ≥ 1` the height is at most `2 * π / q`, and the
multiplicity weighted count only grows with the height, so the whole range is controlled by
the single endpoint height `t = 2 * π / q`, where the sealed right hand side is at its
smallest.  The three steps are therefore: the count is monotone in the height; the count at
the endpoint `2 * π / q` is bounded by the sealed right hand side evaluated there; and the
endpoint value of the right hand side is at most the right hand side at the interior height,
because the logarithm only gains `log (2 * π / (q * t))` while the linear main term gains
`(2 / q - t / π) * log (2 * π * exp 1)`, which is larger.  The assembly at the end of the
file is exactly that chain of three inequalities.
-/

namespace LeanLab.HelfgottMajor.Decomp388a
open Real DecompJ1153

/-- The zeros of `L χ` in the strip `0 < re < 1` with `|im| ≤ T` are finite.
Carried verbatim from `LeanLab.HelfgottMajor.DecompJ1153` (private there). -/
private theorem zeros_strip_finite' (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
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

/-- The weight of a single zero is nonnegative. -/
private lemma zeroWeight_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    (ρ : ℂ) : 0 ≤ zeroWeight χ t ρ := by
  classical
  simp only [zeroWeight, Set.indicator_apply]
  split_ifs with h
  · exact Nat.cast_nonneg _
  · exact le_refl 0

/-- The weight of a single zero grows with the height. -/
private lemma zeroWeight_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s t : ℝ}
    (hst : s ≤ t) (ρ : ℂ) : zeroWeight χ s ρ ≤ zeroWeight χ t ρ := by
  classical
  have hs : ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s} → ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t} := by
    rintro ⟨a, b, c, d⟩
    exact ⟨a, b, c, le_trans d hst⟩
  simp only [zeroWeight, Set.indicator_apply]
  by_cases h : ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s}
  · rw [if_pos h, if_pos (hs h)]
  · rw [if_neg h]
    split_ifs with h2
    · exact Nat.cast_nonneg _
    · exact le_refl 0

/-- LEAF. Monotonicity of the multiplicity weighted count in the height.  Raising the
height can only add nontrivial zeros to the counted set of `zeroCount`, and every weight is
a nonnegative natural number cast to a real, so the weighted sum over the plane grows.  This
is the step that carries the count from an interior height up to the endpoint `2 * π / q` of
the short range. -/
theorem zeroCount_mono_height (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    {s t : ℝ} (hst : s ≤ t) : zeroCount χ s ≤ zeroCount χ t := by
  classical
  have hfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ t}.Finite := zeros_strip_finite' q χ t
  have hsub : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s} ⊆ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t} := by
    rintro ρ ⟨a, b, c, d⟩
    exact ⟨a, b, c, le_trans d hst⟩
  have hsfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ s}.Finite := hfin.subset hsub
  set Ss := hsfin.toFinset with hSsdef
  set St := hfin.toFinset with hStdef
  have hSs : ∀ ρ : ℂ, ρ ∈ Ss ↔ (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ s) := by
    intro ρ; rw [hSsdef]; simp
  have hSt : ∀ ρ : ℂ, ρ ∈ St ↔ (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧
      ρ.re < 1 ∧ |ρ.im| ≤ t) := by
    intro ρ; rw [hStdef]; simp
  have hzero : ∀ ρ ∉ Ss, zeroWeight χ s ρ = 0 := by
    intro ρ hρ
    simp only [zeroWeight, Set.indicator_apply]
    rw [if_neg]
    intro hmem
    exact hρ ((hSs ρ).2 hmem)
  have h1 : zeroCount χ s = ∑ ρ ∈ Ss, zeroWeight χ s ρ := by
    rw [zeroCount]
    exact tsum_eq_sum hzero
  have h0t : ∀ ρ ∉ St, zeroWeight χ t ρ = 0 := by
    intro ρ hρ
    simp only [zeroWeight, Set.indicator_apply]
    rw [if_neg]
    intro hmem
    exact hρ ((hSt ρ).2 hmem)
  have h2 : zeroCount χ t = ∑ ρ ∈ St, zeroWeight χ t ρ := by
    rw [zeroCount]
    exact tsum_eq_sum h0t
  have h4 : ∑ ρ ∈ Ss, zeroWeight χ s ρ ≤ ∑ ρ ∈ St, zeroWeight χ t ρ := by
    refine le_trans (Finset.sum_le_sum (fun ρ _ => zeroWeight_le χ hst ρ)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ρ hρ
      exact (hSt ρ).2 (hsub ((hSs ρ).1 hρ))
    · intro ρ _ _
      exact zeroWeight_nonneg χ t ρ
  rw [h1, h2]
  exact h4

/-- LEAF. The counting input of the short range, at the endpoint height `2 * π / q`.  This is
the multiplicity weighted count of the nontrivial zeros of a primitive character below the
single height `q * t = 2 * π`, bounded by the sealed right hand side evaluated at that height,
that is by `0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1)`.  It is the only step
of this split that uses primitivity, and it needs no interior height. -/
theorem zero_count_endpoint_short (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    zeroCount χ (2 * π / q) ≤ 0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) := by
  sorry

/-- Real core of `short_height_endpoint_le`: for `1 ≤ t` and `q * t ≤ 2 * π` the value of the
sealed right hand side at the endpoint `2 * π / q` is at most its value at `t`. -/
private lemma short_core (q t : ℝ) (hq : 0 < q) (ht : 1 ≤ t) (hqt : q * t ≤ 2 * π) :
    0.5 * log (2 * π) - (2 / q) * log (2 * π * exp 1) ≤
      0.5 * log (q * t) - (t / π) * log (2 * π * exp 1) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hqt0 : (0 : ℝ) < q * t := mul_pos hq ht0
  have hC2 : (2 : ℝ) ≤ log (2 * π * exp 1) := by
    have h := LeanLab.HelfgottMajor.log_two_pi_gt
    rw [log_mul (by positivity) (exp_pos 1).ne', log_exp]
    linarith
  have hfac : (0 : ℝ) ≤ 2 * π - q * t := by linarith
  have hkey : (0.5 : ℝ) / (q * t) ≤ log (2 * π * exp 1) / (q * π) := by
    rw [div_le_div_iff₀ hqt0 (by positivity)]
    have hp : (0.5 : ℝ) * π ≤ 2 * t := by
      have := pi_lt_four
      linarith
    have h1 : (0.5 : ℝ) * π * q ≤ 2 * t * q := by nlinarith [hp, hq]
    have h2 : (2 : ℝ) * (q * t) ≤ log (2 * π * exp 1) * (q * t) :=
      mul_le_mul_of_nonneg_right hC2 hqt0.le
    nlinarith [h1, h2]
  have e1 : 0.5 * (2 * π / (q * t) - 1) = (2 * π - q * t) * (0.5 / (q * t)) := by
    have h := hqt0.ne'
    field_simp
  have e2 : log (2 * π) - log (q * t) = log (2 * π / (q * t)) := by
    rw [log_div (by positivity) hqt0.ne']
  have e3 : (2 * π - q * t) * (log (2 * π * exp 1) / (q * π)) =
      (2 / q - t / π) * log (2 * π * exp 1) := by
    have h := hqt0.ne'
    field_simp
  have hlog1 : log (2 * π / (q * t)) ≤ 2 * π / (q * t) - 1 :=
    log_le_sub_one_of_pos (by positivity)
  have hmain : 0.5 * log (2 * π) - 0.5 * log (q * t) ≤
      (2 / q - t / π) * log (2 * π * exp 1) := by
    calc 0.5 * log (2 * π) - 0.5 * log (q * t)
        = 0.5 * (log (2 * π) - log (q * t)) := by ring
      _ = 0.5 * log (2 * π / (q * t)) := by rw [e2]
      _ ≤ 0.5 * (2 * π / (q * t) - 1) := by linarith
      _ = (2 * π - q * t) * (0.5 / (q * t)) := e1
      _ ≤ (2 * π - q * t) * (log (2 * π * exp 1) / (q * π)) :=
            mul_le_mul_of_nonneg_left hkey hfac
      _ = (2 / q - t / π) * log (2 * π * exp 1) := e3
  linarith [hmain]

/-- LEAF. The elementary endpoint comparison on the short range.  For `1 ≤ t` with
`q * t ≤ 2 * π`, the value of the sealed right hand side at the endpoint `2 * π / q` is at
most its value at the interior height `t`.  The difference is
`log (2 * π / (q * t)) / 2 + (t / π - 2 / q) * log (2 * π * exp 1)`, whose first term is at
most zero on the range and whose second term is at least zero there and dominates the first,
the case `t = 1` being the worst one. -/
theorem short_height_endpoint_le (q : ℕ) [NeZero q] (t : ℝ) (ht : 1 ≤ t)
    (hqt : q * t ≤ 2 * π) :
    0.5 * log (2 * π) + 17.7 - (2 / q) * log (2 * π * exp 1) ≤
      0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h := short_core (q : ℝ) t hq ht hqt
  linarith

/-- The explicit upper count at short heights, assembled from the endpoint count, the
monotonicity of the count in the height and the endpoint comparison. -/
theorem zero_count_short_height_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (t : ℝ) (ht : 1 ≤ t) (hqt : q * t ≤ 2 * π) :
    zeroCount χ t ≤ 0.5 * log (q * t) + 17.7 - (t / π) * log (2 * π * exp 1) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hmono : t ≤ 2 * π / q := by
    rw [le_div_iff₀ hq]
    linarith
  have h1 := zeroCount_mono_height q χ hmono
  have h2 := zero_count_endpoint_short q χ hχ
  have h3 := short_height_endpoint_le q t ht hqt
  linarith
