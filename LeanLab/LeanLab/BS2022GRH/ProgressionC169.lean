/- AI wrote this Lean code for CODEX task169.
Elementary part of Lemma 13, journal pp. 1230 and 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a
import LeanLab.BS2022GRH.BookkeepingC164

namespace LeanLab.BS2022GRH.ProgressionC169
open Real Finset Classical DecompC169a
noncomputable section

/-- Primes p at most n with d dividing n minus p, the progression in Lemma 12. -/
def progressionPrimes (n d : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p => p.Prime ∧ d ∣ n - p)

/-- The progression error relative to pi of n over phi of d, p. 1229. -/
def progressionError (n d : ℕ) : ℝ :=
  ((progressionPrimes n d).card : ℝ) -
    (((range (n + 1)).filter Nat.Prime).card : ℝ) / (d.totient : ℝ)

/-- Excluded primes in that progression, p. 1231 residue comparison. -/
def excludedPrimes (n d : ℕ) : Finset ℕ :=
  (progressionPrimes n d).filter (fun p => p ∣ n)

/-- Subtracting p from n preserves the divisor count in the eligible progression. -/
theorem divisor_card (n d : ℕ) :
    ((U7153.Aset n).filter (fun a => d ∣ a)).card =
      ((progressionPrimes n d).filter (fun p => ¬ p ∣ n)).card := by
  have heq : (U7153.Aset n).filter (fun a => d ∣ a) =
      (((progressionPrimes n d).filter (fun p => ¬ p ∣ n)).image (fun p => n - p)) := by
    ext a
    simp only [U7153.Aset, progressionPrimes, mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨⟨p, ⟨hp, hprime, hpn⟩, rfl⟩, hd⟩
      exact ⟨p, ⟨⟨hp, hprime, hd⟩, hpn⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp, hprime, hd⟩, hpn⟩, rfl⟩
      exact ⟨⟨p, ⟨hp, hprime, hpn⟩, rfl⟩, hd⟩
  rw [heq]
  apply card_image_of_injOn
  intro p hp q hq heq
  have hp' : p < n + 1 := mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
  have hq' : q < n + 1 := mem_range.mp (mem_filter.mp (mem_filter.mp hq).1).1
  change n - p = n - q at heq
  omega

/-- The divisor count plus the excluded count is the full progression count. -/
theorem progression_partition (n d : ℕ) :
    ((U7153.Aset n).filter (fun a => d ∣ a)).card + (excludedPrimes n d).card =
      (progressionPrimes n d).card := by
  rw [divisor_card]
  have h := card_filter_add_card_filter_not (s := progressionPrimes n d) (fun p => p ∣ n)
  unfold excludedPrimes
  omega

/-- At most omega of n primes are excluded from any progression. -/
theorem excluded_le (n d : ℕ) (hn : 0 < n) :
    (excludedPrimes n d).card ≤ n.primeFactors.card := by
  apply card_le_card
  intro p hp
  obtain ⟨hp, hpn⟩ := mem_filter.mp hp
  obtain ⟨_, hprime, _⟩ := mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hprime, hpn, by omega⟩

/-- Exact difference between the two error conventions, p. 1231. -/
theorem residue_identity (n d : ℕ) (hn : 0 < n) :
    residue n d = progressionError n d +
      (n.primeFactors.card : ℝ) / (d.totient : ℝ) - (excludedPrimes n d).card := by
  have htotal : ((U7153.Aset n).card : ℝ) + n.primeFactors.card =
      (((range (n + 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast BookkeepingC164.count_identity n hn
  have hpart : (((U7153.Aset n).filter (fun a => d ∣ a)).card : ℝ) +
      (excludedPrimes n d).card = ((progressionPrimes n d).card : ℝ) := by
    exact_mod_cast progression_partition n d
  unfold residue progressionError
  rw [show (((U7153.Aset n).filter (fun a => d ∣ a)).card : ℝ) =
    ((progressionPrimes n d).card : ℝ) - (excludedPrimes n d).card by linarith]
  rw [show ((U7153.Aset n).card : ℝ) =
    (((range (n + 1)).filter Nat.Prime).card : ℝ) - n.primeFactors.card by linarith]
  ring

/-- The elementary error comparison used by Lemma 13, p. 1231. -/
theorem residue_abs_le (n d : ℕ) (hn : 0 < n) :
    |residue n d| ≤ |progressionError n d| + n.primeFactors.card := by
  have hl : ((excludedPrimes n d).card : ℝ) ≤ n.primeFactors.card := by
    exact_mod_cast excluded_le n d hn
  have hω : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
  have hφ : (0 : ℝ) ≤ d.totient := Nat.cast_nonneg _
  have hdiv0 : 0 ≤ (n.primeFactors.card : ℝ) / (d.totient : ℝ) := div_nonneg hω hφ
  have hdiv : (n.primeFactors.card : ℝ) / (d.totient : ℝ) ≤ n.primeFactors.card := by
    by_cases hd : d.totient = 0
    · simp [hd, hω]
    · apply div_le_self hω
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hcorr : |(n.primeFactors.card : ℝ) / (d.totient : ℝ) - (excludedPrimes n d).card| ≤
      n.primeFactors.card := by
    apply abs_le.mpr
    constructor <;> linarith [(Nat.cast_nonneg (excludedPrimes n d).card : (0 : ℝ) ≤ (excludedPrimes n d).card)]
  rw [residue_identity n d hn]
  calc
    _ = |progressionError n d +
        ((n.primeFactors.card : ℝ) / (d.totient : ℝ) - (excludedPrimes n d).card)| := by congr 1; ring
    _ ≤ |progressionError n d| +
        |(n.primeFactors.card : ℝ) / (d.totient : ℝ) - (excludedPrimes n d).card| := abs_add_le _ _
    _ ≤ |progressionError n d| + n.primeFactors.card := add_le_add_right hcorr _

end
end LeanLab.BS2022GRH.ProgressionC169

#print axioms LeanLab.BS2022GRH.ProgressionC169.divisor_card
#print axioms LeanLab.BS2022GRH.ProgressionC169.progression_partition
#print axioms LeanLab.BS2022GRH.ProgressionC169.excluded_le
#print axioms LeanLab.BS2022GRH.ProgressionC169.residue_identity
#print axioms LeanLab.BS2022GRH.ProgressionC169.residue_abs_le
