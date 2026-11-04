import LeanLab.OpenProblems.KohonenAsymptotic

/-!
# The extremal range and Kohonen's literal liminf bound

AI wrote the Lean code. Goldbach remains OPEN. This is known mathematics.
Source: Kohonen, https://arxiv.org/abs/1606.04770, version 2,
page 1 definition of `n(k)` and equation 1. A range n includes zero through n.
The supremum below is finite by pair counting. At cardinality zero its value
is defined to be zero by the natural-number supremum convention.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

open scoped Pointwise

/-- The largest initial range covered by pair sums of a set of exactly k elements.
At k = 0 the empty supremum is zero. -/
noncomputable def maximalRange (k : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ A : Finset ℕ, A.card = k ∧
    ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m}

/-- Covering zero through n requires at least n plus one ordered pairs. -/
theorem covered_range_le_card_sq {A : Finset ℕ} {n : ℕ}
    (h : ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m) : n + 1 ≤ A.card ^ 2 := by
  have hsub : Finset.range (n + 1) ⊆ A + A := by
    intro m hm
    exact Finset.mem_add.mpr (h m (by simpa using hm))
  have hc := (Finset.card_le_card hsub).trans Finset.card_add_le
  simpa [pow_two] using hc

/-- The extremal range is finite and bounded by the square of the cardinality. -/
theorem maximalRange_le_sq (k : ℕ) : maximalRange k ≤ k ^ 2 := by
  apply csSup_le'
  rintro n ⟨A, hA, hn⟩
  have h := covered_range_le_card_sq hn
  rw [hA] at h
  omega

/-- Any explicit initial-range certificate bounds the extremal range from below. -/
theorem le_maximalRange {A : Finset ℕ} {k n : ℕ} (hA : A.card = k)
    (hn : ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m) : n ≤ maximalRange k := by
  apply le_csSup
  · refine ⟨k ^ 2, ?_⟩
    rintro r ⟨B, hB, hr⟩
    have h := covered_range_le_card_sq hr
    rw [hB] at h
    omega
  · exact ⟨A, hA, hn⟩

/-- The real range-to-size-squared ratios stay at most one, including cardinality zero. -/
theorem maximalRange_ratio_le_one (k : ℕ) :
    (maximalRange k : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have h : (maximalRange k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast maximalRange_le_sq k
    exact (div_le_one (by positivity)).mpr h

/-- Equation 1 of Kohonen's paper, with the extremal range as defined on page one. -/
theorem kohonen_liminf :
    (85 / 294 : ℝ) ≤ Filter.liminf (fun k : ℕ => (maximalRange k : ℝ) / (k : ℝ) ^ 2)
      Filter.atTop := by
  have hco := Filter.isCoboundedUnder_ge_of_le Filter.atTop maximalRange_ratio_le_one
  apply le_of_forall_lt
  intro b hb
  let ε := (85 / 294 - b) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      85 / 294 - ε ≤ (maximalRange k : ℝ) / (k : ℝ) ^ 2 := by
    filter_upwards [kohonen_asymptotic ε hε, Filter.eventually_ge_atTop 1] with k hk hk1
    obtain ⟨A, hA, n, hn, hcover⟩ := hk
    have hnR : (n : ℝ) ≤ maximalRange k := by exact_mod_cast le_maximalRange hA hcover
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    apply (le_div_iff₀ (by positivity)).mpr
    exact hn.trans hnR
  have hlim := Filter.le_liminf_of_le hco hev
  dsimp [ε] at hlim
  linarith

/-- Unordered pairs give the usual sharper counting bound from the paper's introduction. -/
theorem covered_range_le_choose_two {A : Finset ℕ} {n : ℕ}
    (h : ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m) :
    n + 1 ≤ Nat.choose (A.card + 1) 2 := by
  let f : Sym2 ℕ → ℕ := Sym2.lift ⟨(· + ·), Nat.add_comm⟩
  have hsub : Finset.range (n + 1) ⊆ A.sym2.image f := by
    intro m hm
    obtain ⟨a, ha, b, hb, hab⟩ := h m (by simpa using hm)
    refine Finset.mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩
    simpa only [f, Sym2.lift_mk] using hab
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa only [Finset.card_range, Finset.card_sym2] using hcard

/-- The standard unordered-pair upper bound on the extremal range. -/
theorem maximalRange_le_choose_two (k : ℕ) : maximalRange k ≤ Nat.choose (k + 1) 2 := by
  apply csSup_le'
  rintro n ⟨A, hA, hn⟩
  have h := covered_range_le_choose_two hn
  rw [hA] at h
  omega

/-- For positive cardinality the supremum is attained and the next integer is absent.
Thus maximalRange agrees with the page-one definition of a maximal exact range. -/
theorem maximalRange_attained (k : ℕ) (hk : 0 < k) :
    ∃ A : Finset ℕ, A.card = k ∧
      (∀ m ≤ maximalRange k, ∃ a ∈ A, ∃ b ∈ A, a + b = m) ∧
      ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = maximalRange k + 1 := by
  have hne : {n : ℕ | ∃ A : Finset ℕ, A.card = k ∧
      ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m}.Nonempty := by
    refine ⟨0, Finset.range k, Finset.card_range k, ?_⟩
    intro m hm
    have hm0 : m = 0 := by omega
    exact ⟨0, by simpa using hk, 0, by simpa using hk, by omega⟩
  have hbdd : BddAbove {n : ℕ | ∃ A : Finset ℕ, A.card = k ∧
      ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m} := by
    refine ⟨k ^ 2, ?_⟩
    rintro n ⟨A, hA, hn⟩
    have h := covered_range_le_card_sq hn
    rw [hA] at h
    omega
  obtain ⟨A, hA, hcover⟩ : ∃ A : Finset ℕ, A.card = k ∧
      ∀ m ≤ maximalRange k, ∃ a ∈ A, ∃ b ∈ A, a + b = m := Nat.sSup_mem hne hbdd
  refine ⟨A, hA, hcover, ?_⟩
  rintro ⟨a, ha, b, hb, hab⟩
  have hnext : ∀ m ≤ maximalRange k + 1, ∃ a ∈ A, ∃ b ∈ A, a + b = m := by
    intro m hm
    by_cases hle : m ≤ maximalRange k
    · exact hcover m hle
    · exact ⟨a, ha, b, hb, by omega⟩
  have := le_maximalRange hA hnext
  omega

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.covered_range_le_card_sq
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.maximalRange_le_sq
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.le_maximalRange
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.maximalRange_ratio_le_one
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_liminf

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.covered_range_le_choose_two
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.maximalRange_le_choose_two
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.maximalRange_attained
