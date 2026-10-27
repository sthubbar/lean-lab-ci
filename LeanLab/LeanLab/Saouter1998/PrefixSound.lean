/-
Saouter 1998, Theorem 2 and the ladder method, pages 863 and 864.
AI wrote this Lean code for CODEX task73. Binary Goldbach is open.
-/
import LeanLab.Saouter1998.PrefixCore
import LeanLab.Saouter1998.Theorem2
import LeanLab.Saouter1998.B9.Step

namespace LeanLab.Saouter1998.PrefixCore

open LeanLab.HelfgottPlatt

/-- The core checker computes the existing Theorem 2 test. -/
theorem test_eq (R k : ℕ) : test R k = Thm2.thm2B R k := by
  simp only [test, candidate, Thm2.thm2B, Saouter1998.pm_eq]
  rfl

/-- A checked cofactor gives a prime candidate. -/
theorem prime_of_test {R k : ℕ} (h : test R k = true) : (candidate R).Prime := by
  exact Thm2.prime_of_thm2B ((test_eq R k) ▸ h)

/-- Every candidate in a checked list is prime. -/
theorem primes_of_tests {W : List (ℕ × ℕ)} (h : W.all (fun x => test x.1 x.2) = true) :
    ∀ p ∈ primes W, p.Prime := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact prime_of_test (List.all_eq_true.mp h x hx)

/-- A checked list extends a ternary range. The even range remains a hypothesis. -/
theorem extend {B a last : ℕ} {W : List (ℕ × ℕ)} (hB : EvenGoldbachUpTo B)
    (hT : TernaryGoldbachUpTo (a + B)) (ha : a.Prime) (ha3 : 3 ≤ a)
    (ht : W.all (fun x => test x.1 x.2) = true) (hc : check B a last W = true) :
    TernaryGoldbachUpTo (last + B) ∧ last.Prime ∧ 3 ≤ last := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hchain, hlast⟩, hal⟩ := hc
  have hB4 : 4 ≤ B := by
    cases W with
    | nil => simp [primes] at hlast
    | cons x xs =>
      change ((decide (a < candidate x.1) && decide (candidate x.1 ≤ a + (B - 4))) &&
        Core.chainC B (candidate x.1) (primes xs)) = true at hchain
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchain
      omega
  have hpr := primes_of_tests ht
  have hmem : last ∈ primes W := List.mem_of_getLast? hlast
  have hD : (primes W).getLastD a = last := by
    rw [List.getLastD_eq_getLast?, hlast]; rfl
  refine ⟨?_, hpr last hmem, by omega⟩
  intro n hn h7 hnX
  by_cases hs : n ≤ a + B
  · exact hT n hn h7 hs
  · exact ternary_of_ladder_aux hB (primes W) a ha ha3 hpr
      (B9.chainC_sound B _ a hchain) n hn (by omega) (by rw [hD]; exact hnX)

end LeanLab.Saouter1998.PrefixCore
