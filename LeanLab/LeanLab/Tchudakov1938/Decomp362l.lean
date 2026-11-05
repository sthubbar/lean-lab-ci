/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Decomp362a

namespace LeanLab.Tchudakov1938.Decomp362l
open Finset

/-- LEAF. P0064, page 36, inequality 33. For each fixed triple of q, q prime and a double prime, the determinant equation determines a uniquely. -/
theorem determinant_solution_count (A Q R B : Finset ℤ) (hR : ∀ r ∈ R, r ≠ 0) (s : ℤ) :
    ((A ×ˢ (Q ×ˢ (R ×ˢ B))).filter
      (fun t => t.1 * t.2.2.1 - t.2.2.2 * t.2.1 = s)).card ≤ Q.card * R.card * B.card := by
  calc
    _ ≤ (Q ×ˢ (R ×ˢ B)).card := by
      apply Finset.card_le_card_of_injOn (fun t => t.2)
      · intro t ht
        exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
      · intro t ht u hu heq
        have ht' := Finset.mem_filter.mp ht
        have hu' := Finset.mem_filter.mp hu
        simp only [Finset.mem_product] at ht' hu'
        rcases t with ⟨a, q, r, b⟩
        rcases u with ⟨a', q', r', b'⟩
        dsimp at heq
        cases heq
        have hr : r ≠ 0 := hR r ht'.1.2.2.1
        have hmul : a * r = a' * r := by linarith [ht'.2, hu'.2]
        have ha : a = a' := mul_right_cancel₀ hr hmul
        subst a'
        rfl
    _ = _ := by simp [Nat.mul_assoc]


end LeanLab.Tchudakov1938.Decomp362l
