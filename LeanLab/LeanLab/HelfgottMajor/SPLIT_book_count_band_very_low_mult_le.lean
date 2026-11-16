import LeanLab.HelfgottMajor.SPLIT_book_count_band_count_le

/-!
# Split of `book_count_band_very_low_mult_le` (`HelfgottMajor/SPLIT_book_count_band_count_le`)

The target bounds the multiplicities of the strip zeros of one primitive `L`-function whose
height lies between `0` and `1`, on the band `1 ≤ T`, `q * T ≤ 2πe`. Because the height is at
least one on the band, the conductor is at most `2πe`, so the band only concerns the finitely
many `L`-functions of conductor at most `17`.

The sum is cut at the height `0`. A zero of the strip with `0 ≤ Im ρ ≤ 1` either has
`Im ρ = 0`, that is it is a real zero, or it has `0 < Im ρ ≤ 1`:

* `very_low_mult_le_one_of_im_eq_zero`: a real zero of the strip has multiplicity at most one.
* `very_low_real_zero_card_le_one`: there is at most one real zero of the strip. Together with
  the previous leaf this bounds the real part of the sum by one, since each term of that sum is
  a multiplicity at most one and the summands are nonnegative.
* `very_low_no_zero_of_im_pos_le_one`: no zero of the strip has imaginary part in `(0, 1]`, so
  the open part of the sum is empty and contributes zero.

The assembly adds the two pieces. Since the multiplicities are nonnegative naturals cast to
`ℝ`, the bound on the number of real zeros together with the bound on their multiplicity is
exactly the bound on their contribution.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF. Multiplicity of a real zero: on the band `1 ≤ T`, `q * T ≤ 2πe`, a strip zero with
imaginary part `0` is a simple zero, that is its multiplicity is at most one. Nothing is
asserted about zeros off the real axis, and nothing about how many real zeros there are. -/
theorem very_low_mult_le_one_of_im_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ stripZeros χ T, ρ.im = 0 → mult χ ρ ≤ 1 := by
  sorry

/-- LEAF. Number of real zeros: on the band `1 ≤ T`, `q * T ≤ 2πe`, the strip zeros with
imaginary part `0` number at most one. Nothing is asserted about the multiplicity of that
zero, and nothing about zeros off the real axis. -/
theorem very_low_real_zero_card_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ((stripZeros_finite χ T).toFinset.filter (fun ρ => ρ.im = 0)).card ≤ 1 := by
  sorry

/-- LEAF. No low zero off the real axis: on the band `1 ≤ T`, `q * T ≤ 2πe`, every strip zero
with positive imaginary part has imaginary part above `1`. Equivalently the closed segment of
heights from `0` to `1` carries no zero of positive height. Nothing is asserted about real
zeros, nor about zeros above height one. -/
theorem very_low_no_zero_of_im_pos_le_one (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    ∀ ρ ∈ stripZeros χ T, 0 < ρ.im → 1 < ρ.im := by
  sorry

/-- Two filters of one finset with pointwise equivalent predicates give equal sums. -/
private lemma sum_filter_congr_of_iff {α : Type*} (s : Finset α) (f : α → ℝ)
    (p r : α → Prop) [DecidablePred p] [DecidablePred r] (h : ∀ x, p x ↔ r x) :
    ∑ x ∈ s.filter p, f x = ∑ x ∈ s.filter r, f x := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hx, hp⟩ => ⟨hx, (h x).mp hp⟩, fun ⟨hx, hr⟩ => ⟨hx, (h x).mpr hr⟩⟩

/-- Assembly: the very low multiplicities on the band are at most one. The index set is the
strip zeros with height between `0` and `1`; cutting it at height `0` gives the real zeros,
which are at most one and each of multiplicity at most one, and the zeros of positive height
at most `1`, of which there are none. -/
theorem book_count_band_very_low_mult_le_split (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 1 ≤ T) (hband : (q : ℝ) * T ≤ 2 * Real.pi * Real.exp 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  set s := (stripZeros_finite χ T).toFinset with hs
  have hmem : ∀ ρ ∈ s, ρ ∈ stripZeros χ T := by
    intro ρ hρ
    rw [hs] at hρ
    simpa using hρ
  have hsplit :
      (∑ ρ ∈ s.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1), (mult χ ρ : ℝ)) =
        (∑ ρ ∈ s.filter (fun ρ => ρ.im = 0), (mult χ ρ : ℝ)) +
        (∑ ρ ∈ s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1), (mult χ ρ : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := s.filter (fun ρ => 0 ≤ ρ.im ∧ ρ.im ≤ 1)) (p := fun ρ => ρ.im = 0)]
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact sum_filter_congr_of_iff s (fun ρ => (mult χ ρ : ℝ))
        (fun ρ => (0 ≤ ρ.im ∧ ρ.im ≤ 1) ∧ ρ.im = 0) (fun ρ => ρ.im = 0) (by
          intro ρ
          constructor
          · rintro ⟨-, h⟩
            exact h
          · intro h
            rw [h]
            norm_num)
    · exact sum_filter_congr_of_iff s (fun ρ => (mult χ ρ : ℝ))
        (fun ρ => (0 ≤ ρ.im ∧ ρ.im ≤ 1) ∧ ¬ ρ.im = 0) (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) (by
          intro ρ
          constructor
          · rintro ⟨⟨h0, h1⟩, hne⟩
            exact ⟨lt_of_le_of_ne h0 (Ne.symm hne), h1⟩
          · rintro ⟨h0, h1⟩
            exact ⟨⟨le_of_lt h0, h1⟩, ne_of_gt h0⟩)
  have hempty : s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro ρ hρ
    rintro ⟨h1, h2⟩
    have h3 := very_low_no_zero_of_im_pos_le_one χ hχ hT hband ρ (hmem ρ hρ) h1
    linarith
  have hnod : (∑ ρ ∈ s.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1), (mult χ ρ : ℝ)) = 0 := by
    rw [hempty]
    simp
  have hcard : (s.filter (fun ρ => ρ.im = 0)).card ≤ 1 := by
    have := very_low_real_zero_card_le_one χ hχ hT hband
    rwa [← hs] at this
  have hterm : ∀ ρ ∈ s.filter (fun ρ => ρ.im = 0), (mult χ ρ : ℝ) ≤ 1 := by
    intro ρ hρ
    have hρs : ρ ∈ s := (Finset.mem_filter.mp hρ).1
    have him : ρ.im = 0 := (Finset.mem_filter.mp hρ).2
    have := very_low_mult_le_one_of_im_eq_zero χ hχ hT hband ρ (hmem ρ hρs) him
    exact_mod_cast this
  have hreal : (∑ ρ ∈ s.filter (fun ρ => ρ.im = 0), (mult χ ρ : ℝ)) ≤ 1 := by
    have h1 := Finset.sum_le_card_nsmul (s.filter (fun ρ => ρ.im = 0))
      (fun ρ => (mult χ ρ : ℝ)) 1 hterm
    have h2 : (s.filter (fun ρ => ρ.im = 0)).card • (1 : ℝ) ≤ 1 := by
      have h3 : ((s.filter (fun ρ => ρ.im = 0)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      simpa using h3
    exact h1.trans h2
  rw [hsplit, hnod]
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623
