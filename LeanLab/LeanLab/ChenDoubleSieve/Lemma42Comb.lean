import Mathlib

/-!
# Counting below thresholds in a finite set of naturals, for Wu 2004 Lemma 4.2

Unit U-5402, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.
`R` is a finite set of naturals, `e = R.orderEmbOfFin rfl` lists it in increasing order, and
`Nc R θ = #{x ∈ R : x < θ}` for a real threshold `θ`. Then `e j < θ ↔ j < Nc R θ`, and the
elements of `R` above the first `m` lying in `[lo, hi)` number at least `Nc hi - max m (Nc lo)`.
-/

open Finset

noncomputable section

namespace LeanLab.ChenDoubleSieve.Wu42

/-- `#{x ∈ R : x < θ}`. -/
def Nc (R : Finset ℕ) (θ : ℝ) : ℕ := #{x ∈ R | ((x : ℕ) : ℝ) < θ}

/-- `R` in increasing order. -/
abbrev ord (R : Finset ℕ) : Fin #R ↪o ℕ := R.orderEmbOfFin rfl

lemma mem_iff_exists (R : Finset ℕ) (x : ℕ) : x ∈ R ↔ ∃ i, ord R i = x := by
  have h := R.range_orderEmbOfFin (rfl : #R = #R)
  constructor
  · intro hx
    have : x ∈ Set.range (ord R) := by rw [h]; exact hx
    exact this
  · rintro ⟨i, rfl⟩; exact R.orderEmbOfFin_mem rfl i

lemma filter_lt_ord (R : Finset ℕ) (j : Fin #R) :
    {x ∈ R | x < ord R j} = (Iio j).map (ord R).toEmbedding := by
  ext x
  simp only [mem_filter, mem_map, mem_Iio, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨hx, hlt⟩
    obtain ⟨i, rfl⟩ := (mem_iff_exists R x).1 hx
    exact ⟨i, (ord R).lt_iff_lt.1 hlt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨R.orderEmbOfFin_mem rfl i, (ord R).lt_iff_lt.2 hi⟩

lemma card_lt_ord (R : Finset ℕ) (j : Fin #R) : #{x ∈ R | x < ord R j} = j := by
  rw [filter_lt_ord, card_map, Fin.card_Iio]

lemma card_le_ord (R : Finset ℕ) (j : Fin #R) : #{x ∈ R | x ≤ ord R j} = j + 1 := by
  have : {x ∈ R | x ≤ ord R j} = insert (ord R j) {x ∈ R | x < ord R j} := by
    ext x; simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hx, hle⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hx, h⟩)
      · exact ⟨R.orderEmbOfFin_mem rfl j, le_rfl⟩
      · exact ⟨hx, h.le⟩
  rw [this, card_insert_of_notMem (by simp), card_lt_ord]

/-- `e j < θ ↔ j < Nc R θ`. -/
lemma ord_lt_iff (R : Finset ℕ) (j : Fin #R) (θ : ℝ) :
    ((ord R j : ℕ) : ℝ) < θ ↔ (j : ℕ) < Nc R θ := by
  unfold Nc
  constructor
  · intro h
    rw [← card_lt_ord R j]
    apply card_lt_card
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans (by exact_mod_cast hx.2) h⟩
    · have hm : ord R j ∈ ({x ∈ R | ((x : ℕ) : ℝ) < θ} : Finset ℕ) :=
        mem_filter.2 ⟨R.orderEmbOfFin_mem rfl j, h⟩
      have := mem_filter.1 (hsub hm)
      exact lt_irrefl _ this.2
  · intro h
    by_contra hθ
    push Not at hθ
    have hsub : ({x ∈ R | ((x : ℕ) : ℝ) < θ} : Finset ℕ) ⊆ {x ∈ R | x < ord R j} := by
      intro x hx
      rw [mem_filter] at hx ⊢
      exact ⟨hx.1, by exact_mod_cast lt_of_lt_of_le hx.2 hθ⟩
    have := card_le_card hsub
    rw [card_lt_ord] at this
    omega

lemma le_ord_iff (R : Finset ℕ) (j : Fin #R) (θ : ℝ) :
    θ ≤ ((ord R j : ℕ) : ℝ) ↔ Nc R θ ≤ (j : ℕ) := by
  rw [← not_lt, ord_lt_iff]; omega

lemma Nc_mono (R : Finset ℕ) {θ θ' : ℝ} (h : θ ≤ θ') : Nc R θ ≤ Nc R θ' := by
  unfold Nc
  apply card_le_card
  intro x hx; rw [mem_filter] at hx ⊢; exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

lemma Nc_le_card (R : Finset ℕ) (θ : ℝ) : Nc R θ ≤ #R := by unfold Nc; exact card_filter_le _ _

/-- Elements of `R` above `e (m - 1)` in `[lo, hi)`: at least `Nc hi - max m (Nc lo)`. -/
lemma tail_count (R : Finset ℕ) (m : ℕ) (hm : 1 ≤ m) (hmR : m ≤ #R) (lo hi : ℝ) :
    Nc R hi - max m (Nc R lo) ≤
      #{x ∈ R | ord R ⟨m - 1, by omega⟩ < x ∧ lo ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) < hi} := by
  set t := ord R ⟨m - 1, by omega⟩
  have hcov : ({x ∈ R | ((x : ℕ) : ℝ) < hi} : Finset ℕ) ⊆
      {x ∈ R | t < x ∧ lo ≤ ((x : ℕ) : ℝ) ∧ ((x : ℕ) : ℝ) < hi} ∪
        ({x ∈ R | x ≤ t} ∪ {x ∈ R | ((x : ℕ) : ℝ) < lo}) := by
    intro x hx
    rw [mem_filter] at hx
    simp only [mem_union, mem_filter]
    by_cases h1 : t < x
    · by_cases h2 : lo ≤ ((x : ℕ) : ℝ)
      · exact Or.inl ⟨hx.1, h1, h2, hx.2⟩
      · exact Or.inr (Or.inr ⟨hx.1, lt_of_not_ge h2⟩)
    · exact Or.inr (Or.inl ⟨hx.1, not_lt.1 h1⟩)
  have hmax : #({x ∈ R | x ≤ t} ∪ {x ∈ R | ((x : ℕ) : ℝ) < lo}) ≤ max m (Nc R lo) := by
    have hct : #{x ∈ R | x ≤ t} = m := by
      rw [card_le_ord]; simp; omega
    by_cases hlo : lo ≤ (t : ℝ)
    · rw [union_eq_left.2]
      · rw [hct]; exact le_max_left _ _
      · intro x hx; rw [mem_filter] at hx ⊢
        exact ⟨hx.1, by exact_mod_cast (lt_of_lt_of_le hx.2 hlo).le⟩
    · rw [union_eq_right.2]
      · exact le_max_right _ _
      · intro x hx; rw [mem_filter] at hx ⊢
        push Not at hlo
        exact ⟨hx.1, lt_of_le_of_lt (by exact_mod_cast hx.2) hlo⟩
  have := (card_le_card hcov).trans (card_union_le _ _)
  unfold Nc at hmax ⊢
  omega

end LeanLab.ChenDoubleSieve.Wu42
