import Mathlib

/-!
# R-0040: number rigidity of point processes, Ghosh-Peres, and the reflected pair

U-1366, PC 20261021T0703Z-4724, T3 MOONSHOT. AI wrote this Lean code.

The rigidity step of a point process model can at best recover, from the
configuration outside a window `D = [m - k, m + k]`, the NUMBER of points in `D`.
`rigidity_blind` shows that the outside configuration together with that number
never decides whether `2m` is a sum of two points: two sets agree off `D`, have the
same count in `D`, one contains the reflected pair `m - k, m + k`, the other has no
pair summing to `2m` at all. KNOWN mathematics in substance, barrier map only.
-/

namespace LeanLab.Routes.R0040

/-- `N` is a sum of two elements of `A`. -/
def HasPair (A : Finset ℕ) (N : ℕ) : Prop := ∃ a ∈ A, ∃ b ∈ A, a + b = N

theorem rigidity_blind (B : Finset ℕ) (m k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m)
    (hB : ∀ b ∈ B, b < m - k ∨ m + k < b)
    (hBpair : ∀ a ∈ B, ∀ b ∈ B, a + b ≠ 2 * m) :
    (∀ x, x ∉ Finset.Icc (m - k) (m + k) →
        (x ∈ B ∪ {m - k, m + k} ↔ x ∈ B ∪ {m - k, m - k + 1})) ∧
    ((B ∪ {m - k, m + k}).filter (· ∈ Finset.Icc (m - k) (m + k))).card =
      ((B ∪ {m - k, m - k + 1}).filter (· ∈ Finset.Icc (m - k) (m + k))).card ∧
    HasPair (B ∪ {m - k, m + k}) (2 * m) ∧
    ¬ HasPair (B ∪ {m - k, m - k + 1}) (2 * m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro (h | h | h) <;> first | exact Or.inl h | omega
  · have h1 : (B ∪ {m - k, m + k}).filter (· ∈ Finset.Icc (m - k) (m + k)) =
        {m - k, m + k} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_Icc]
      constructor
      · rintro ⟨h | h | h, h2⟩
        · rcases hB x h with h3 | h3 <;> omega
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h) <;> refine ⟨Or.inr (by omega), by omega⟩
    have h2 : (B ∪ {m - k, m - k + 1}).filter (· ∈ Finset.Icc (m - k) (m + k)) =
        {m - k, m - k + 1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_Icc]
      constructor
      · rintro ⟨h | h | h, h2⟩
        · rcases hB x h with h3 | h3 <;> omega
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h) <;> refine ⟨Or.inr (by omega), by omega⟩
    rw [h1, h2, Finset.card_pair (by omega), Finset.card_pair (by omega)]
  · exact ⟨m - k, by simp, m + k, by simp, by omega⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    have key : ∀ x ∈ B, x + (m - k) ≠ 2 * m ∧ x + (m - k + 1) ≠ 2 * m := by
      intro x hx
      rcases hB x hx with h3 | h3 <;> omega
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha | ha
    · rcases hb with hb | hb | hb
      · exact hBpair a ha b hb hab
      · have := key a ha; omega
      · have := key a ha; omega
    · rcases hb with hb | hb | hb
      · have := key b hb; omega
      · omega
      · omega
    · rcases hb with hb | hb | hb
      · have := key b hb; omega
      · omega
      · omega

/-- Vacuity test with primes: `B` = the primes below 50 outside `[44, 56]` that do not
pair to 100 inside `B`, and the window around `m = 50`, `k = 3`: `A` contains `47, 53`,
both prime, and `47 + 53 = 100`; `A'` swaps `53` for `48`. -/
def B0 : Finset ℕ := {2, 5, 13, 19, 23, 31, 37, 43, 61, 67, 73, 79, 89}

theorem B0_hyp : (∀ b ∈ B0, b < 50 - 3 ∨ 50 + 3 < b) ∧
    (∀ a ∈ B0, ∀ b ∈ B0, a + b ≠ 2 * 50) := by decide

theorem vacuity : HasPair (B0 ∪ {47, 53}) 100 ∧ ¬ HasPair (B0 ∪ {47, 48}) 100 := by
  have := rigidity_blind B0 50 3 (by norm_num) (by norm_num) B0_hyp.1 B0_hyp.2
  exact ⟨this.2.2.1, this.2.2.2⟩

end LeanLab.Routes.R0040
