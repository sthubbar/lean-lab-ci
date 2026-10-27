/-
P0073, equations 2.1 and 2.2. Elementary counting bounds.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.SteinStein1965.Soundness
namespace LeanLab.Stein1965.Counting114

open LeanLab.SteinStein1965
open scoped Pointwise
/-- Equation 2.1, page 427: the number of required even targets is bounded by
the number of unordered pairs of basis elements, with repetition allowed. -/
theorem basis_card_bound (B : List ℕ) (N : ℕ) (hB : IsBasisFor B 6 N) :
    N / 2 - 2 ≤ (B.toFinset.card + 1).choose 2 := by
  let sums : Sym2 ℕ → ℕ := Sym2.lift ⟨(· + ·), Nat.add_comm⟩
  let evens := (Finset.range (N / 2 - 2)).image (fun n => 2 * n + 6)
  have hevens : evens.card = N / 2 - 2 := by
    dsimp [evens]
    rw [Finset.card_image_of_injective _ (by intro x y h; dsimp at h; omega), Finset.card_range]
  have hsub : evens ⊆ B.toFinset.sym2.image sums := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_range.mp hn
    obtain ⟨x, hx, y, hy, hxy⟩ := hB (2 * n + 6) (by omega) (by omega) (by omega)
    apply Finset.mem_image.mpr
    refine ⟨s(x, y), Finset.mk_mem_sym2_iff.mpr ⟨by simpa using hx, by simpa using hy⟩, ?_⟩
    simpa [sums] using hxy
  calc
    N / 2 - 2 = evens.card := hevens.symm
    _ ≤ (B.toFinset.sym2.image sums).card := Finset.card_le_card hsub
    _ ≤ B.toFinset.sym2.card := Finset.card_image_le
    _ = (B.toFinset.card + 1).choose 2 := Finset.card_sym2 _

/-- Equations 2.1 and 2.2: any basis through 10^7 needs at least 3162 distinct elements. -/
theorem basis_1e7_card_lower (B : List ℕ) (hB : IsBasisFor B 6 (10 ^ 7)) :
    3162 ≤ B.toFinset.card := by
  have h := basis_card_bound B (10 ^ 7) hB
  rw [Nat.choose_two_right] at h
  simp only [Nat.add_sub_cancel, Nat.reducePow, Nat.reduceDiv, Nat.reduceSub] at h
  by_contra hn
  have hk : B.toFinset.card ≤ 3161 := by omega
  have hmul : 9999996 ≤ (B.toFinset.card + 1) * B.toFinset.card := by omega
  nlinarith

end LeanLab.Stein1965.Counting114
