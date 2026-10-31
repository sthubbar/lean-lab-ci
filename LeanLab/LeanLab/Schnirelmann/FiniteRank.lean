/-
The finite rank counting statement and its extreme ranks.
Source: Nathanson, arXiv:2407.12253v4, page 5, Theorem 4 and the preceding definitions.
The general finite rank theorem is a cited Prop, not an assertion.
AI wrote this Lean code, OpenAI Codex, task26, 2026-10-22.
-/
import LeanLab.Schnirelmann.Mann

open Finset
open scoped Classical Pointwise

namespace LeanLab.Schnirelmann.Mann
open LeanLab.Ramare1995.Section9 LeanLab.Ramare1995.Theorem91

/-- The sum of the positive counts of all rank r sumsets. -/
noncomputable def rankCount {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) (r n : ℕ) : ℕ :=
  ∑ t ∈ s.powersetCard r, cnt (∑ i ∈ t, A i) n

/-- The finite rank theorem, with the zero convention made explicit. -/
def DysonRankCounting : Prop :=
  ∀ (h n : ℕ) (A : ℕ → Set ℕ) (γ : ℝ), 0 < n →
    (∀ i < h, 0 ∈ A i) →
    (∀ m, 1 ≤ m → m ≤ n → γ * m ≤ (∑ i ∈ range h, (cnt (A i) m : ℝ))) →
    ∀ r, 1 ≤ r → r ≤ h →
      ((h - 1).choose (r - 1) : ℝ) * min 1 γ * n ≤ rankCount (range h) A r n

/-- At rank one, the rank count is the sum of the input counts. -/
theorem rankCount_one {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) (n : ℕ) :
    rankCount s A 1 n = ∑ i ∈ s, cnt (A i) n := by
  unfold rankCount
  rw [powersetCard_one, sum_map]
  simp

/-- At full rank, there is only the sumset using all indices. -/
theorem rankCount_card {ι : Type*} (s : Finset ι) (A : ι → Set ℕ) (n : ℕ) :
    rankCount s A s.card n = cnt (∑ i ∈ s, A i) n := by
  simp [rankCount, powersetCard_self]

/-- The representation sumset agrees with the pointwise sum when zero is allowed. -/
theorem sumSet_eq_sum (A : ℕ → Set ℕ) (h : ℕ) (hA : ∀ i < h, 0 ∈ A i) :
    SumSet A h = ∑ i ∈ range h, A i := by
  ext p
  rw [Set.mem_finsetSum]
  change (∃ f : ℕ → ℕ, (∀ i < h, f i = 0 ∨ f i ∈ A i) ∧
    ∑ i ∈ range h, f i = p) ↔ _
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨f, ?_, he⟩
    intro i hi
    rcases hf i (mem_range.mp hi) with hz | ha
    · rw [hz]
      exact hA i (mem_range.mp hi)
    · exact ha
  · rintro ⟨f, hf, he⟩
    exact ⟨f, fun i hi => Or.inr (hf (mem_range.mpr hi)), he⟩

/-- The full rank case of the finite rank counting theorem. -/
theorem dyson_full_count (h n : ℕ) (hh : 1 ≤ h) (A : ℕ → Set ℕ)
    (hA : ∀ i < h, 0 ∈ A i) (γ : ℝ)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → γ * m ≤ ∑ i ∈ range h, (cnt (A i) m : ℝ)) :
    min 1 γ * n ≤ (rankCount (range h) A h n : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have hd : DysonHypR A (k + 1) n (min 1 γ) := by
    intro m hm hmn
    have hle : min 1 γ * (m : ℝ) ≤ γ * m :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg m)
    simpa [phi] using hle.trans (hyp m hm hmn)
  have hd := dysonR k n A (min 1 γ) (min_le_left _ _) hd
  have hc := rankCount_card (range (k + 1)) A n
  rw [card_range] at hc
  rw [hc, ← sumSet_eq_sum A (k + 1) hA]
  exact hd

/-- The rank one case of the finite rank theorem follows directly from its prefix bound. -/
theorem dyson_rank_one_count (h n : ℕ) (hn : 0 < n) (A : ℕ → Set ℕ) (γ : ℝ)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → γ * m ≤ ∑ i ∈ range h, (cnt (A i) m : ℝ)) :
    ((h - 1).choose (1 - 1) : ℝ) * min 1 γ * n ≤
      (rankCount (range h) A 1 n : ℝ) := by
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul,
    rankCount_one, Nat.cast_sum]
  exact (mul_le_mul_of_nonneg_right (min_le_right 1 γ) (Nat.cast_nonneg n)).trans
    (hyp n hn (le_refl n))

/-- All finite Dyson ranks for at most two inputs are endpoint ranks. -/
theorem dyson_rank_count_of_le_two (h n : ℕ) (hh : h ≤ 2) (hn : 0 < n)
    (A : ℕ → Set ℕ) (hA : ∀ i < h, 0 ∈ A i) (γ : ℝ)
    (hyp : ∀ m, 1 ≤ m → m ≤ n → γ * m ≤ ∑ i ∈ range h, (cnt (A i) m : ℝ))
    (r : ℕ) (hr : 1 ≤ r) (hrh : r ≤ h) :
    ((h - 1).choose (r - 1) : ℝ) * min 1 γ * n ≤
      (rankCount (range h) A r n : ℝ) := by
  rcases (show r = 1 ∨ r = h by omega) with he | he
  · rw [he]
    exact dyson_rank_one_count h n hn A γ hyp
  · rw [he]
    simpa only [Nat.choose_self, Nat.cast_one, one_mul] using
      dyson_full_count h n (by omega) A hA γ hyp

end LeanLab.Schnirelmann.Mann
