/-
Saouter 1998, Table 1, page 865. The generated prefix begins with the printed table.
AI wrote this Lean code for CODEX task73. Binary Goldbach is open.
-/
import LeanLab.Saouter1998.Prefix73.Ladder
import LeanLab.Saouter1998.Table1

namespace LeanLab.Saouter1998.Prefix73

open LeanLab.Saouter1998.PrefixCore

/-- The generated certificate list has exactly one thousand entries. -/
def W : List (ℕ × ℕ) := W1 ++ W2 ++ W3 ++ W4

theorem length_W : W.length = 1000 := by decide +kernel

/-- The first hundred cofactors agree exactly with the paper's printed table. -/
theorem matches_table1 : (W.take 100).map Prod.fst =
    Table1.T1.map (fun k => 10 * k + 3) := by decide +kernel

/-- Every prime in the generated thousand-rung prefix is prime unconditionally. -/
theorem all_prime : ∀ p ∈ primes W, p.Prime := by
  apply primes_of_tests
  simp only [W, List.all_append, c1, c2, c3, c4, Bool.and_self]

/-- The entire prefix has increasing primes with the paper's admissible gaps. -/
theorem chain : Core.chainC 400000000000 3 (primes W) = true := by decide +kernel

end LeanLab.Saouter1998.Prefix73
