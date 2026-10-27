import LeanLab.Ricci1937.TheoremsCD

/-!
A negative transfer check for Ricci 1937, Theorem D, pages 74 and 75.
A larger factor count alone does not imply one of Ricci's smaller counts.
This does not question any existence theorem or the printed case 5 question.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

/-- At threshold one the hierarchy of total factor bounds is strict. -/
theorem almostGT_strict_factor_hierarchy {a b : ℕ} (hab : a < b) :
    ∃ x : ℕ, AlmostGT b 1 x ∧ ¬ AlmostGT a 1 x := by
  refine ⟨2 ^ b, ?_, ?_⟩
  · refine ⟨one_le_pow₀ (by norm_num), ?_, ?_⟩
    · rw [Nat.prime_two.primeFactorsList_pow, List.length_replicate]
    · intro p hp
      rw [Nat.prime_two.primeFactorsList_pow] at hp
      have hp2 : p = 2 := List.eq_of_mem_replicate hp
      subst p
      norm_num
  · intro h
    have hlength := h.2.1
    rw [Nat.prime_two.primeFactorsList_pow, List.length_replicate] at hlength
    omega

/-- The factor count 13000 alone cannot supply the printed bound 366. -/
theorem factor_bound_13000_does_not_imply_366 :
    ∃ x : ℕ, AlmostGT 13000 1 x ∧ ¬ AlmostGT 366 1 x := by
  obtain ⟨x, hx, hnot⟩ := almostGT_strict_factor_hierarchy (a := 366) (b := 367) (by norm_num)
  exact ⟨x, almostGT_mono hx (by norm_num) le_rfl, hnot⟩

end LeanLab.Ricci1937
