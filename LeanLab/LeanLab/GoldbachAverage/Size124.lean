import LeanLab.GoldbachAverage.Decomp124

/-!
The necessary size bound for a thin prime basis in P0098 page 162.
The counting argument works for arbitrary finite sets of natural numbers.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Size124
open Finset
open Decomp124

/-- P0098 page 162, at most k times k plus one over two unordered pairs are available.
Covering every even integer from four to two N therefore requires at least N minus one pairs. -/
theorem pairs_needed (S : Finset ℕ) (N : ℕ)
    (hc : ∀ n ∈ Icc 2 N, ∃ p ∈ S, ∃ q ∈ S, p + q = 2 * n) :
    N - 1 ≤ Nat.choose (S.card + 1) 2 := by
  classical
  let addPair : Sym2 ℕ → ℕ := Sym2.lift ⟨fun a b => a + b, Nat.add_comm⟩
  have hsub : (Icc 2 N).image (fun n => 2 * n) ⊆ S.sym2.image addPair := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    obtain ⟨p, hp, q, hq, heq⟩ := hc k hk
    exact mem_image.mpr ⟨s(p, q), by simp [hp, hq], heq⟩
  have hm := (Finset.card_le_card hsub).trans (card_image_le (f := addPair))
  rw [card_image_of_injective _ (show Function.Injective (fun n : ℕ => 2 * n) by
    intro a b hab; dsimp only at hab; omega), Nat.card_Icc, card_sym2] at hm
  convert hm using 1 <;> omega

/-- P0098 page 162, its displayed quadratic lower bound for the count at two N.
Only the finitely many required representations below two N enter this proof. -/
theorem count_pairs_needed (P : Set ℕ) (N : ℕ)
    (hc : ∀ n : ℕ, Even n → 2 < n → n ≤ 2 * N →
      ∃ p ∈ P, ∃ q ∈ P, p + q = n) :
    N - 1 ≤ Nat.choose (count P (2 * N) + 1) 2 := by
  classical
  let S := (range (2 * N + 1)).filter fun p => p ∈ P
  have hs : S.card = count P (2 * N) := by
    dsimp only [S, count]
    rw [show (2 : ℝ) * N = ((2 * N : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast]
  rw [← hs]
  apply pairs_needed
  intro n hn
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
  obtain ⟨p, hp, q, hq, heq⟩ := hc (2 * n) (even_two_mul n) (by omega) (by omega)
  refine ⟨p, ?_, q, ?_, heq⟩ <;> apply mem_filter.mpr
  · exact ⟨mem_range.mpr (by omega), hp⟩
  · exact ⟨mem_range.mpr (by omega), hq⟩

end LeanLab.GoldbachAverage.Size124
