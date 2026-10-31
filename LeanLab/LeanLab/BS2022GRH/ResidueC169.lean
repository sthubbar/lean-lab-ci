/- AI wrote this Lean code for CODEX task169.
Residue bookkeeping for Theorem 6, journal pp. 1232 and 1233. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169b

namespace LeanLab.BS2022GRH.ResidueC169
open Real Finset Classical ChenThresholdGRH DecompC169a DecompC169b

/-- Signed residue identity from the definitions on p. 1232 after display 23.
The subtraction sign follows from r at q equal to cardinality of A_q minus cardinality of A over phi q. -/
theorem quotient_residue_identity (n q d : ℕ) (hqd : Nat.Coprime q d) :
    quotientResidue n q d = residue n (q * d) - residue n q / (d.totient : ℝ) := by
  unfold quotientResidue aqCard residue
  rw [Nat.totient_mul hqd, Nat.cast_mul, div_mul_eq_div_div]
  ring

/-- The absolute residue bound used on p. 1233 is independent of the signed identity convention. -/
theorem quotient_residue_abs_le (n q d : ℕ) (hqd : Nat.Coprime q d) :
    |quotientResidue n q d| ≤ |residue n (q * d)| + |residue n q| / (d.totient : ℝ) := by
  rw [quotient_residue_identity n q d hqd]
  simpa only [abs_div, abs_of_nonneg (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)] using
    (abs_sub (residue n (q * d)) (residue n q / (d.totient : ℝ)))

/-- The mass at q has the main term plus r at q, p. 1233 display 24. -/
theorem aq_card_identity (n q : ℕ) :
    aqCard n q = ((U7153.Aset n).card : ℝ) / (q.totient : ℝ) + residue n q := by
  unfold aqCard residue
  ring

/-- A prime q contributes the denominator q minus one in display 24, p. 1233. -/
theorem aq_card_prime (n q : ℕ) (hq : q.Prime) :
    aqCard n q = ((U7153.Aset n).card : ℝ) / ((q : ℝ) - 1) + residue n q := by
  rw [aq_card_identity, Nat.totient_prime hq, Nat.cast_sub hq.one_le]
  norm_num

/-- The qd indexing in the first residue sum is injective, p. 1233.
Distinct primes q and r cannot be exchanged when neither divides the other small factor. -/
theorem product_index_injective (q r d e : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hqe : ¬ q ∣ e) (hrd : ¬ r ∣ d) (hprod : q * d = r * e) : q = r ∧ d = e := by
  have hqr : q ∣ r := by
    have h : q ∣ r * e := by rw [← hprod]; exact dvd_mul_right q d
    exact (hq.dvd_mul.mp h).resolve_right hqe
  have heq : q = r := (Nat.dvd_prime hr).mp hqr |>.resolve_left hq.ne_one
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hq.pos hprod⟩

end LeanLab.BS2022GRH.ResidueC169

#print axioms LeanLab.BS2022GRH.ResidueC169.quotient_residue_identity
#print axioms LeanLab.BS2022GRH.ResidueC169.quotient_residue_abs_le
#print axioms LeanLab.BS2022GRH.ResidueC169.aq_card_identity
#print axioms LeanLab.BS2022GRH.ResidueC169.aq_card_prime
#print axioms LeanLab.BS2022GRH.ResidueC169.product_index_injective
