/-
AI wrote this Lean code for CODEX task276.
P0004 page 29 Lemma 13, with its proof on page 30.
The lab's unconditional Theorem B supplies the asymptotic used in the paper.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.TheoremBAll

namespace LeanLab.HardyLittlewood1923.Decomp276e

/-- P0004 page 29 Lemma 13. The prime weighted representation count has a positive
lower bound of order n to r minus one on the matching parity class. -/
theorem lemma13 (r : ℕ) (hr : 3 ≤ r) :
    ∃ B : ℝ, 0 < B ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → n % 2 = r % 2 →
      B * (n : ℝ) ^ (r - 1) < nur r n := by
  obtain ⟨c, K, hc, hbr⟩ := Br_bounds r hr
  have hCr := Cr_pos r hr
  let a : ℝ := 2 * Cr r / (Nat.factorial (r - 1) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨n₀, hb⟩ := theoremB r hr (1 / 2) (by norm_num)
  refine ⟨a * c / 4, by positivity, max n₀ 1, fun n hn hpar => ?_⟩
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < a * c * (n : ℝ) ^ (r - 1) := by positivity
  have hm : a * c * (n : ℝ) ^ (r - 1) ≤ Mr r n := by
    calc _ = a * (n : ℝ) ^ (r - 1) * c := by ring
         _ ≤ a * (n : ℝ) ^ (r - 1) * Br r n :=
           mul_le_mul_of_nonneg_left (hbr n).1 (by positivity)
         _ = Mr r n := rfl
  have he := (abs_le.mp (hb n hpar hn₀)).1
  nlinarith only [hm, he, hp]

#print axioms lemma13

end LeanLab.HardyLittlewood1923.Decomp276e
