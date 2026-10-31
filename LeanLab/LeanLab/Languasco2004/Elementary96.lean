/-
Elementary consequences of P0089 pages 223, 225 and 227.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Links

namespace LeanLab.Languasco2004

open Finset Real

attribute [local instance] Classical.propDecidable

/-- Page 223 and page 225: the interval count vanishes exactly when every
eligible even integer in that interval has a Goldbach representation. -/
theorem EXH_eq_zero_iff (X H : ℝ) :
    EXH X H = 0 ↔ ∀ n : ℕ, X ≤ (n : ℝ) → (n : ℝ) ≤ X + H →
      Even n → 2 < n → IsGoldbachSum n := by
  unfold EXH
  rw [Finset.card_filter_eq_zero_iff]
  constructor
  · intro h n hn hn' he h2
    by_contra hg
    exact h n (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn')))
      ⟨hn, hn', he, h2, hg⟩
  · intro h n _ hn
    exact hn.2.2.2.2 (h n hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1)

#print axioms EXH_eq_zero_iff

/-- Page 223: Goldbach is equivalent to emptiness of its exception set. -/
theorem binaryGoldbach_iff_no_exception :
    BinaryGoldbach ↔ ∀ n : ℕ, ¬ InE n := by
  constructor
  · intro h n hn
    have h4 : 4 ≤ n := by
      have hmod := Nat.even_iff.mp hn.1
      have h2 := hn.2.1
      omega
    exact hn.2.2 (h n hn.1 h4)
  · intro h n he hn
    by_contra hg
    exact h n ⟨he, by omega, hg⟩

#print axioms binaryGoldbach_iff_no_exception

/-- Page 223: every global exception count vanishes exactly when Goldbach holds. -/
theorem binaryGoldbach_iff_EX_zero :
    BinaryGoldbach ↔ ∀ X : ℝ, EX X = 0 := by
  constructor
  · intro h X
    apply (EXH_eq_zero_iff 1 (X - 1)).mpr
    intro n _ _ he hn
    have h4 : 4 ≤ n := by
      have := Nat.even_iff.mp he
      omega
    exact h n he h4
  · intro h
    apply binaryGoldbach_iff_no_exception.mpr
    intro n hn
    have hz := (EXH_eq_zero_iff 1 ((n : ℝ) - 1)).mp (h n)
    exact hn.2.2 (hz n (by exact_mod_cast (show 1 ≤ n by have := hn.2.1; omega))
      (by linarith) hn.1 hn.2.1)

#print axioms binaryGoldbach_iff_EX_zero

/-- Page 225: eventual emptiness of all intervals of length two is equivalent
to Goldbach representations for all sufficiently large even integers. -/
theorem eventual_E2_empty_iff_eventual_goldbach :
    (∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → EXH X 2 = 0) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → 4 ≤ n → IsGoldbachSum n := by
  constructor
  · rintro ⟨X₀, h⟩
    refine ⟨⌈X₀⌉₊, fun n hn he h4 => ?_⟩
    exact goldbach_of_E2_empty h n he (by omega)
      ((Nat.le_ceil X₀).trans (by exact_mod_cast hn))
  · rintro ⟨N, hN⟩
    refine ⟨N, fun X hX => (EXH_eq_zero_iff X 2).mpr ?_⟩
    intro n hn _ he h2
    have hnN : N ≤ n := by exact_mod_cast hX.trans hn
    have h4 : 4 ≤ n := by
      have hmod := Nat.even_iff.mp he
      omega
    exact hN n hnN he h4

#print axioms eventual_E2_empty_iff_eventual_goldbach

end LeanLab.Languasco2004
