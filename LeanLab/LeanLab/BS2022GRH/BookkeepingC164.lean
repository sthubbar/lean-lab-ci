/- AI wrote the Lean code for CODEX task164.
Elementary part of journal Lemma 11, p. 1228.
Goldbach is open. -/
import LeanLab.BS2022GRH.U7153Lemma10
namespace LeanLab.BS2022GRH.BookkeepingC164
open Real Finset Classical
/-- Subtracting p from n preserves the number of eligible primes. -/
theorem Aset_card (n : ℕ) :
    (U7153.Aset n).card = ((range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n)).card := by
  unfold U7153.Aset
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  have hp0 : p < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hq0 : q < n + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
  change n - p = n - q at heq
  omega
/-- The excluded primes are exactly the distinct prime divisors of n. -/
theorem divisor_primes (n : ℕ) (hn : 0 < n) :
    ((range (n + 1)).filter Nat.Prime).filter (fun p => p ∣ n) = n.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hdiv⟩
    exact ⟨hprime, hdiv, by omega⟩
  · rintro ⟨hprime, hdiv, hn0⟩
    exact ⟨⟨by have := Nat.le_of_dvd hn hdiv; omega, hprime⟩, hdiv⟩
/-- Exact cardinality accounting behind the first step of Lemma 11. -/
theorem count_identity (n : ℕ) (hn : 0 < n) :
    (U7153.Aset n).card + n.primeFactors.card = ((range (n + 1)).filter Nat.Prime).card := by
  have hc := Finset.card_filter_add_card_filter_not (s := (range (n + 1)).filter Nat.Prime)
    (fun p => p ∣ n)
  rw [divisor_primes n hn] at hc
  simp only [Finset.filter_filter] at hc
  rw [Aset_card]
  omega
/-- The absolute difference from pi of n equals omega of n, so the paper's first bound holds. -/
theorem count_error (n : ℕ) (hn : 0 < n) :
    |((U7153.Aset n).card : ℝ) - (((range (n + 1)).filter Nat.Prime).card : ℝ)| =
      (n.primeFactors.card : ℝ) := by
  have hc : ((U7153.Aset n).card : ℝ) + n.primeFactors.card =
      (((range (n + 1)).filter Nat.Prime).card : ℝ) := by exact_mod_cast count_identity n hn
  rw [show ((U7153.Aset n).card : ℝ) - (((range (n + 1)).filter Nat.Prime).card : ℝ) =
    -(n.primeFactors.card : ℝ) by linarith, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
end LeanLab.BS2022GRH.BookkeepingC164
#print axioms LeanLab.BS2022GRH.BookkeepingC164.Aset_card
#print axioms LeanLab.BS2022GRH.BookkeepingC164.divisor_primes
#print axioms LeanLab.BS2022GRH.BookkeepingC164.count_identity
#print axioms LeanLab.BS2022GRH.BookkeepingC164.count_error
