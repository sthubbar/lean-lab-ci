import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.Decomp389c

/-!
Endpoint extension for the inclusive zero count of P0014 page 38, display 4.26.
The quantitative bound remains a cited input. The limit argument uses finite strip zeros.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.CountLimit433
open Filter Set Topology Real
open ZeroCount1623 Decomp389c

/-- The inclusive multiplicity count is nondecreasing in height.
This is the counting function used before display 4.26 on P0014 page 38.
-/
theorem count_monotone {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Monotone (fun t => ∑' ρ, stripCountTerm χ t ρ) := by
  classical
  intro s t hst
  change (∑' ρ : ZeroIdx χ s, (mult χ ρ.val : ℝ)) ≤
    ∑' ρ : ZeroIdx χ t, (mult χ ρ.val : ℝ)
  rw [tsum_zeroIdx χ s (fun z => (mult χ z : ℝ)),
    tsum_zeroIdx χ t (fun z => (mult χ z : ℝ))]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    have hz := (stripZeros_finite χ s).mem_toFinset.mp hρ
    exact (stripZeros_finite χ t).mem_toFinset.mpr
      ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hst⟩
  · intro ρ _ _
    exact Nat.cast_nonneg _

/-- The inclusive multiplicity count is locally constant to the right of each height.
Formal endpoint bookkeeping for the count defined before display 4.26 on P0014 page 38.
-/
theorem count_eventuallyEq_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (fun t => ∑' ρ, stripCountTerm χ t ρ) =ᶠ[𝓝[>] T]
      (fun _ => ∑' ρ, stripCountTerm χ T ρ) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + ε)] with t ht
  change (∑' ρ : ZeroIdx χ t, (mult χ ρ.val : ℝ)) =
    ∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)
  rw [tsum_zeroIdx χ t (fun z => (mult χ z : ℝ)),
    tsum_zeroIdx χ T (fun z => (mult χ z : ℝ))]
  exact sum_eq_of_strip_eq χ (hgap t ht.1 ht.2) _

/-- The closed count has its own value as a right limit, even at a zero ordinate.
Formal endpoint bookkeeping for P0014 page 38, display 4.26.
-/
theorem count_tendsto_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Tendsto (fun t => ∑' ρ, stripCountTerm χ t ρ) (𝓝[>] T)
      (𝓝 (∑' ρ, stripCountTerm χ T ρ)) := by
  exact tendsto_const_nhds.congr' (count_eventuallyEq_right χ T).symm

/-- A continuous upper bound proved away from zero ordinates extends to the inclusive count.
CONDITIONAL ON hbound. Formal endpoint extension for P0014 page 38, display 4.26.
-/
theorem count_le_of_off_ordinates {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (B : ℝ → ℝ) (hB : ContinuousAt B T)
    (hbound : ∀ᶠ t in 𝓝[>] T, (∀ ρ ∈ stripZeros χ t, |ρ.im| ≠ t) →
      (∑' ρ, stripCountTerm χ t ρ) ≤ B t) :
    (∑' ρ, stripCountTerm χ T ρ) ≤ B T := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  have hev : ∀ᶠ t in 𝓝[>] T, (∑' ρ, stripCountTerm χ t ρ) ≤ B t := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + ε), hbound] with t ht hb
    apply hb
    intro ρ hρ heq
    rw [hgap t ht.1 ht.2] at hρ
    have hle := hρ.2.2.2
    linarith [ht.1]
  exact le_of_tendsto_of_tendsto (count_tendsto_right χ T)
    (hB.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- At an endpoint ordinate, the inclusive count restores the missing half multiplicity.
P0014 page 38 defines the inclusive count. Book page 431 uses half weight at each endpoint.
-/
theorem count_eq_book_add_boundary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 0 < T) :
    (∑' ρ, stripCountTerm χ T ρ) = bookCount χ T + bookCount χ⁻¹ T +
      (1 / 2 : ℝ) * ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter
        (fun ρ => |ρ.im| = T), (mult χ ρ : ℝ) := by
  classical
  change (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) = _
  rw [tsum_zeroIdx χ T (fun z => (mult χ z : ℝ)), bookCount_inv]
  unfold bookCount
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rcases lt_trichotomy ρ.im 0 with h | h | h
  · have hn : ¬ 0 ≤ ρ.im := not_le.mpr h
    rw [ite_eq_right hn, ite_eq_left h.le, zero_add, abs_of_neg h]
    by_cases he : -ρ.im = T
    · simp [halfWeight, he]
      ring
    · simp [halfWeight, he, neg_ne_zero.mpr h.ne]
  · simp [h, halfWeight]
    split_ifs with hh <;> nlinarith [hT]
  · have hn : ¬ ρ.im ≤ 0 := not_le.mpr h
    rw [ite_eq_left h.le, ite_eq_right hn, add_zero, abs_of_pos h]
    by_cases he : ρ.im = T
    · simp [halfWeight, he]
      ring
    · simp [halfWeight, he, h.ne']

/-- The sum of the book counts never exceeds the inclusive count.
Book page 431 gives half weight to zeros at height T. P0014 page 38 gives full weight.
-/
theorem book_pair_le_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 0 < T) :
    bookCount χ T + bookCount χ⁻¹ T ≤ ∑' ρ, stripCountTerm χ T ρ := by
  rw [count_eq_book_add_boundary χ T hT]
  have h : 0 ≤ (1 / 2 : ℝ) * ∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter
      (fun ρ => |ρ.im| = T), (mult χ ρ : ℝ) := by positivity
  linarith

/-- The two book half weighted counts tend from the right to the full inclusive count.
This reconciles book page 431 with P0014 page 38 without discarding endpoint zeros.
-/
theorem book_pair_tendsto_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun t => bookCount χ t + bookCount χ⁻¹ t) (𝓝[>] T)
      (𝓝 (∑' ρ, stripCountTerm χ T ρ)) := by
  apply (count_tendsto_right χ T).congr'
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  filter_upwards [Ioo_mem_nhdsGT (by linarith : T < T + ε)] with t ht
  change (∑' ρ : ZeroIdx χ t, (mult χ ρ.val : ℝ)) = _
  rw [tsum_zeroIdx χ t (fun z => (mult χ z : ℝ))]
  apply two_sided_split χ (by linarith [ht.1])
  intro ρ hρ heq
  rw [hgap t ht.1 ht.2] at hρ
  have hle := hρ.2.2.2
  linarith [ht.1]

/-- A continuous upper bound on the book pair above T bounds the inclusive count at T.
CONDITIONAL ON hbound. Endpoint extension from book page 431 to P0014 page 38.
-/
theorem count_le_of_book_pair_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (hT : 0 < T) (B : ℝ → ℝ) (hB : ContinuousAt B T)
    (hbound : ∀ᶠ t in 𝓝[>] T, bookCount χ t + bookCount χ⁻¹ t ≤ B t) :
    (∑' ρ, stripCountTerm χ T ρ) ≤ B T := by
  exact le_of_tendsto_of_tendsto (book_pair_tendsto_right χ T hT)
    (hB.tendsto.mono_left nhdsWithin_le_nhds) hbound

/-- The exact sealed count follows from its numerical upper bound away from zero ordinates.
CONDITIONAL ON hcount. The numerical input is displays 4.25 and 4.26 on P0014 page 38.
This proves no explicit zero counting constant.
-/
theorem strip_zero_count_of_off_ordinates (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (hT : 1 ≤ T)
    (hcount : ∀ t : ℝ, 1 ≤ t → (∀ ρ ∈ stripZeros χ t, |ρ.im| ≠ t) →
      (∑' ρ, stripCountTerm χ t ρ) ≤
        t / π * log ((q : ℝ) * t / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * t) + 17.7) :
    Summable (stripCountTerm χ T) ∧
      (∑' ρ, stripCountTerm χ T ρ) ≤
        T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * T) + 17.7 := by
  refine ⟨summable_zeroIdx χ T _, ?_⟩
  apply count_le_of_off_ordinates χ T
    (fun t => t / π * log ((q : ℝ) * t / (2 * π * exp 1)) +
      0.5 * log ((q : ℝ) * t) + 17.7)
  · have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hT0 : 0 < T := by linarith
    have harg : (q : ℝ) * T / (2 * π * exp 1) ≠ 0 := by positivity
    have hprod : (q : ℝ) * T ≠ 0 := by positivity
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hcount t (le_trans hT (le_of_lt ht))

end LeanLab.HelfgottMajor.CountLimit433
