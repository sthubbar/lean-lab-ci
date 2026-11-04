import LeanLab.Common.Goldbach

/-!
P0011 page 102, Section 4, coverage by translates of a finite prime set.
This states the soundness of the coverage step. It does not reproduce the computation to 10 to the 13.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.DERZ1997

/-- The finite coverage step in P0011 page 102, with both prime lists explicit. -/
theorem prime_cover_interval266 (P Q : Finset ℕ) (A B : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ n : ℕ, Even n → A ≤ n → n ≤ B →
      n ∈ Q.biUnion (fun q => P.image (fun p => p + q))) :
    ∀ n : ℕ, Even n → A ≤ n → n ≤ B → IsGoldbachSum n := by
  intro n hn hA hB
  obtain ⟨q, hq, hn⟩ := Finset.mem_biUnion.mp (hcover n hn hA hB)
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hn
  exact ⟨p, q, hP p hp, hQ q hq, heq⟩

example : ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 10 → IsGoldbachSum n := by
  apply prime_cover_interval266 {3, 5} {3, 5} 6 10
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro n hn h6 h10
    obtain ⟨k, hk⟩ := hn
    have : n = 6 ∨ n = 8 ∨ n = 10 := by omega
    rcases this with rfl | rfl | rfl <;> simp

end LeanLab.DERZ1997
