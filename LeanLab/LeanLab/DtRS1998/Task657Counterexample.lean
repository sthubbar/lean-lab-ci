/-
AI wrote this Lean code for CODEX task657.
P0037 page 212 Section 5.2 and page 214 Table 2.
This checks a generated fixed list and asserts no error in the paper.
Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper

namespace LeanLab.DtRS1998.Task657Counterexample

/-- The generated fifteen-prime list does not cover all the first eighth offsets. -/
theorem not_leaf_cov_F864 :
    ¬ (∀ j : ℕ, j < 31250001 →
      ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,47] : List ℕ).any (fun q => decide
        (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime)) = true) := by
  intro h
  obtain ⟨q, hq, hp⟩ := List.any_eq_true.mp (h 14 (by decide))
  have hprime := (of_decide_eq_true hp).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.not_prime_of_dvd_of_lt (m := 2) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 5) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 11) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 5) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 10037) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 13) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 29) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 5) (by norm_num) (by decide) (by norm_num) hprime
  · exact Nat.not_prime_of_dvd_of_lt (m := 3) (by norm_num) (by decide) (by norm_num) hprime

end LeanLab.DtRS1998.Task657Counterexample
