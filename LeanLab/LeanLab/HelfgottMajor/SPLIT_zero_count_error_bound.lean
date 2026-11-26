import LeanLab.HelfgottMajor.ZeroCount1623

/-!
Split of `Decomp431a.zero_count_error_bound` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes`, the per sign zero
count of book display 3.95, section 3.7.3.3 of P0014, with the error `g_χ` of display 16.21
on book page 431, as used in the proof of Lemma 16.9.

The book's `N(T, χ)` of page 431 counts zeros with `0 ≤ im ≤ T` and gives half weight to zeros
at height exactly `0` and `T`.  That is the lab statement `ZeroCount1623.book_zero_count`,
already on main and reused here as the single cited LEAF.  The parent counts `0 < im ≤ t` with
full weight at `t` and allows a constant shift `c`.  The step from the book form to the parent
form is proved below with no new input:
* `c` is half the multiplicity weighted count of zeros at height `0`;
* just to the right of `t`, at a height `s` below the next zero height, the book count at `s`
  equals the parent count at `t` plus `c`;
* the main term and `g_χ` are continuous at `t`, so the book bound at `s` passes to the limit
  `s → t+`, which is the remark of the proof of Lemma 16.9 that the count is right continuous.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCountErrorBound
open Real Filter Topology LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- The parent's count over `0 < im ≤ t`, a `tsum` over a subtype, as a finite sum over the
strip zeros of height at most `u ≥ t`. -/
lemma upCount_eq_sum (χ : DirichletCharacter ℂ q) {t u : ℝ} (htu : t ≤ u) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑ ρ ∈ (stripZeros_finite χ u).toFinset,
        if 0 < ρ.im ∧ ρ.im ≤ t then (mult χ ρ : ℝ) else 0 := by
  have h1 := tsum_subtype ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t} : Set ℂ)
      (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
  refine h1.trans ?_
  rw [tsum_eq_sum (s := (stripZeros_finite χ u).toFinset)]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hz := (Set.Finite.mem_toFinset _).mp hρ
    simp only [stripZeros, Set.mem_setOf_eq] at hz
    rw [Set.indicator_apply]
    by_cases h : 0 < ρ.im ∧ ρ.im ≤ t
    · rw [if_pos h, if_pos (show ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t} from ⟨hz.1, hz.2.1, hz.2.2.1, h⟩)]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.2.2.1, h'.2.2.2.2⟩)]
  · intro ρ hρ
    rw [Set.indicator_apply, if_neg]
    intro h
    apply hρ
    rw [Set.Finite.mem_toFinset]
    simp only [stripZeros, Set.mem_setOf_eq]
    exact ⟨h.1, h.2.1, h.2.2.1, by rw [abs_of_pos h.2.2.2.1]; exact h.2.2.2.2.trans htu⟩

/-- The book count of page 431 at height `s ≤ u` as a finite sum over the strip zeros of
height at most `u`. -/
lemma bookCount_eq_sum (χ : DirichletCharacter ℂ q) {s u : ℝ} (hsu : s ≤ u) :
    bookCount χ s = ∑ ρ ∈ (stripZeros_finite χ u).toFinset,
      if 0 ≤ ρ.im ∧ ρ.im ≤ s then halfWeight s ρ.im * (mult χ ρ : ℝ) else 0 := by
  unfold bookCount
  rw [Finset.sum_filter]
  refine (Finset.sum_congr rfl fun ρ hρ => ?_).trans (Finset.sum_subset ?_ ?_)
  · have hz := (Set.Finite.mem_toFinset _).mp hρ
    simp only [stripZeros, Set.mem_setOf_eq] at hz
    by_cases h : 0 ≤ ρ.im
    · rw [if_pos h, if_pos ⟨h, (le_abs_self _).trans hz.2.2.2⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  · intro ρ hρ
    have hz := (Set.Finite.mem_toFinset _).mp hρ
    rw [Set.Finite.mem_toFinset]
    simp only [stripZeros, Set.mem_setOf_eq] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hsu⟩
  · intro ρ hρu hρs
    have hz := (Set.Finite.mem_toFinset _).mp hρu
    simp only [stripZeros, Set.mem_setOf_eq] at hz
    rw [if_neg]
    rintro ⟨h0, hs⟩
    apply hρs
    rw [Set.Finite.mem_toFinset]
    simp only [stripZeros, Set.mem_setOf_eq]
    exact ⟨hz.1, hz.2.1, hz.2.2.1, by rw [abs_of_nonneg h0]; exact hs⟩

/-- Half the weighted count of zeros at height `0`, written as a sum over the strip zeros of
height at most `u ≥ 0`. -/
lemma half_zero_eq_sum (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 0 ≤ u) :
    ∑ ρ ∈ (stripZeros_finite χ 0).toFinset, (1 / 2 : ℝ) * (mult χ ρ : ℝ) =
      ∑ ρ ∈ (stripZeros_finite χ u).toFinset,
        if ρ.im = 0 then (1 / 2 : ℝ) * (mult χ ρ : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, stripZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h5 : ρ.im = 0 := abs_nonpos_iff.mp h4
    exact ⟨⟨h1, h2, h3, by rw [h5, abs_zero]; exact hu⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
    exact ⟨h1, h2, h3, by rw [h5, abs_zero]⟩

/-- The proved step from the book form of display 3.95, half weight at heights `0` and `T`,
to the per sign form used by the parent, with full weight at `t` and a constant shift `c`.
No input beyond the book bound for all `T ≥ 1`. -/
theorem count_of_book (χ : DirichletCharacter ℂ q)
    (hbook : ∀ T : ℝ, 1 ≤ T → |bookCount χ T - bookMain q T| ≤ bookError q T) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389 := by
  refine ⟨∑ ρ ∈ (stripZeros_finite χ 0).toFinset, (1 / 2 : ℝ) * (mult χ ρ : ℝ),
    fun t ht => ?_⟩
  have hF := upCount_eq_sum χ (t := t) (u := t + 1) (by linarith)
  have hc := half_zero_eq_sum χ (u := t + 1) (by linarith)
  set c := ∑ ρ ∈ (stripZeros_finite χ 0).toFinset, (1 / 2 : ℝ) * (mult χ ρ : ℝ) with hcdef
  set F := (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) with hFdef
  have hev : ∀ᶠ s in 𝓝[>] t, t < s ∧ s < t + 1 ∧
      ∀ ρ ∈ (stripZeros_finite χ (t + 1)).toFinset, t < ρ.im → s < ρ.im := by
    have hA : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
    refine hA.and ((?_ : ∀ᶠ s in 𝓝[>] t, s < t + 1).and ?_)
    · exact nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
    · rw [Filter.eventually_all_finset]
      intro ρ _
      by_cases h : t < ρ.im
      · filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds h)] with s hs _ using hs
      · exact Filter.Eventually.of_forall fun s h' => absurd h' h
  have hkey : ∀ᶠ s in 𝓝[>] t, |F + c - bookMain q s| - bookError q s ≤ 0 := by
    filter_upwards [hev] with s hs
    obtain ⟨hts, hsu, hgap⟩ := hs
    have hb := hbook s (by linarith)
    have hcount : bookCount χ s = F + c := by
      rw [bookCount_eq_sum χ hsu.le, hF, hc, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rcases lt_trichotomy ρ.im 0 with h | h | h
      · rw [if_neg (fun h' => absurd h'.1 (not_le.mpr h)),
          if_neg (fun h' => absurd h'.1 (not_lt.mpr h.le)), if_neg h.ne]
        ring
      · rw [if_pos ⟨h.ge, by linarith⟩, if_neg (fun h' => by linarith [h'.1]), if_pos h,
          halfWeight, if_pos (Or.inl h)]
        ring
      · by_cases hte : ρ.im ≤ t
        · rw [if_pos ⟨h.le, by linarith⟩, if_pos ⟨h, hte⟩, if_neg h.ne', halfWeight,
            if_neg (by rintro (h1 | h1) <;> linarith)]
          ring
        · have hgs := hgap ρ hρ (not_le.mp hte)
          rw [if_neg (fun h' => by linarith [h'.2]), if_neg (fun h' => hte h'.2),
            if_neg h.ne']
          ring
    rw [hcount] at hb
    linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : (q : ℝ) * t / (2 * π * exp 1) ≠ 0 := by
    have : 0 < (q : ℝ) * t := mul_pos hq (by linarith)
    positivity
  have h2 : (q : ℝ) * t ≠ 0 := (mul_pos hq (by linarith)).ne'
  have hm : ContinuousAt (fun s => |F + c - bookMain q s| - bookError q s) t := by
    unfold bookMain bookError
    fun_prop (disch := assumption)
  have hlim := le_of_tendsto (hm.tendsto.mono_left nhdsWithin_le_nhds) hkey
  have h3 := sub_nonpos.mp hlim
  exact h3

/-- Sorry free assembly with the exact statement of `Decomp431a.zero_count_error_bound`, from
the single cited LEAF `ZeroCount1623.book_zero_count`, book display 3.95 with the error of
display 16.21. -/
theorem zero_count_error_bound_of_leaves (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389 :=
  count_of_book χ (fun _ hT => book_zero_count χ hχ hT)

end LeanLab.HelfgottMajor.ZeroCountErrorBound

#print axioms LeanLab.HelfgottMajor.ZeroCountErrorBound.count_of_book
#print axioms LeanLab.HelfgottMajor.ZeroCountErrorBound.zero_count_error_bound_of_leaves
