/-
Vaughan 1979 p. 214, the elementary lower bound g 4 at least 19.
https://numdam.org/item/AST_1979__61__213_0/
AI wrote this Lean code. Goldbach remains open.
-/
import Mathlib

namespace LeanLab.Vaughan1979

/-- Vaughan p. 214, the trivial lower bound for fourth powers.
The integer 79 needs at least 19 nonnegative fourth powers. -/
theorem fourth_powers_79_length278 (l : List ℕ)
    (h : (l.map (fun x => x ^ 4)).sum = 79) : 19 ≤ l.length := by
  have split : ∀ t : List ℕ, (t.map (fun x => x ^ 4)).sum ≤ 79 →
      ∃ a b : ℕ, a + b ≤ t.length ∧ (t.map (fun x => x ^ 4)).sum = 16 * a + b := by
    intro t
    induction t with
    | nil => exact fun _ => ⟨0, 0, by simp, by simp⟩
    | cons x t ih =>
      intro ht
      simp only [List.map_cons, List.sum_cons] at ht ⊢
      obtain ⟨a, b, hab, hs⟩ := ih (by omega)
      have hx : x ≤ 2 := by
        by_contra hx
        have hpow : 81 ≤ x ^ 4 := by
          simpa using pow_le_pow_left' (show 3 ≤ x by omega) 4
        omega
      interval_cases x
      · exact ⟨a, b, by simp_all; omega, by simp_all⟩
      · exact ⟨a, b + 1, by simp_all; omega, by simp_all; omega⟩
      · exact ⟨a + 1, b, by simp_all; omega, by simp_all; omega⟩
  obtain ⟨a, b, hab, hs⟩ := split l h.le
  omega

end LeanLab.Vaughan1979
