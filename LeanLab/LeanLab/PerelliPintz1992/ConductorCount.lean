/-
P0070 Section 6, page 367, counting the conductors in equation 37.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.PrimitiveReduction
import LeanLab.PerelliPintz1992.DivisorBound

namespace LeanLab.PerelliPintz1992.Section6
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual conductors of all Dirichlet characters at moduli in Q. -/
def characterConductors (Q : Finset ℕ+) : Finset ℕ :=
  (univ : Finset (Σ q : Q, DirichletCharacter ℂ (q.val : ℕ))).image (fun c => c.2.conductor)

/-- Every occurring conductor divides one of the moduli in Q. -/
theorem characterConductors_card_le (Q : Finset ℕ+) :
    (characterConductors Q).card ≤ ∑ q ∈ Q, (q : ℕ).divisors.card := by
  have hsub : characterConductors Q ⊆ Q.biUnion (fun q => (q : ℕ).divisors) := by
    intro r hr
    obtain ⟨c, _, rfl⟩ := mem_image.mp hr
    exact mem_biUnion.mpr ⟨c.1.val, c.1.property,
      Nat.mem_divisors.mpr ⟨c.2.conductor_dvd_level, Nat.ne_of_gt c.1.val.property⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

#print axioms characterConductors_card_le


/-- The divisor part of equation 37, before applying the Farey window bound. -/
theorem characterConductors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, ∀ Q : Finset ℕ+,
      (∀ q ∈ Q, (q : ℕ) ≤ X) →
      ((characterConductors Q).card : ℝ) ≤ K * Q.card * (X : ℝ) ^ ε := by
  obtain ⟨K, hK, hbound⟩ := divisors_card_le_rpow ε hε
  refine ⟨K, hK, fun X Q hQ => ?_⟩
  have hc : ((characterConductors Q).card : ℝ) ≤
      ∑ q ∈ Q, ((q : ℕ).divisors.card : ℝ) := by
    exact_mod_cast characterConductors_card_le Q
  refine hc.trans ?_
  calc
    (∑ q ∈ Q, ((q : ℕ).divisors.card : ℝ)) ≤ ∑ _q ∈ Q, K * (X : ℝ) ^ ε := by
      apply Finset.sum_le_sum
      intro q hq
      have ht := hbound (q : ℕ) (Nat.ne_of_gt q.property)
      have hp : (q : ℝ) ^ ε ≤ (X : ℝ) ^ ε :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ q hq) hε.le
      exact ht.trans (mul_le_mul_of_nonneg_left hp hK.le)
    _ = K * Q.card * (X : ℝ) ^ ε := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

#print axioms characterConductors_card_le_rpow

end
end LeanLab.PerelliPintz1992.Section6
