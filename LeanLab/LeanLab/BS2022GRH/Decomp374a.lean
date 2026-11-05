/- AI wrote this Lean code for CODEX task374. Goldbach is open.
The two separate large sieve moments behind journal display 15, p. 1225.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.PNTPort.LargeSieve.Bilinear

namespace LeanLab.BS2022GRH.Decomp374a
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The moduli in one dyadic block, journal p. 1225 display 15. -/
def blockModuli (R : ℝ) : Finset ℕ :=
  (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ))

/-- Primitive characters in that block, journal p. 1225 display 15. -/
def blockCharacters (R : ℝ) : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
  (blockModuli R).sigma (fun r =>
    (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive))

/-- One quadratic moment with the standard r over phi r weight, display 15. -/
def blockEnergy (R : ℝ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ blockCharacters R, ((i.1 : ℝ) / i.1.totient) *
    ‖∑ n ∈ S, a n * i.2 n‖ ^ 2

/-- LEAF. Journal p. 1225 display 15, the first large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the coefficients restricted by n coprime to s.
This is one quadratic factor, not the bilinear block estimate. -/
theorem coefficient_energy (c : ℕ → ℂ) (X R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hR : 1 ≤ R) :
    blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c ≤
      (X + 4 * R ^ 2) * X := by
  sorry

/-- LEAF. Journal p. 1225 display 15, the second large sieve moment.
Apply Iwaniec and Kowalski Theorem 7.13 to the prime indicator with p not dividing s.
This factor has no arbitrary coefficient sequence. -/
theorem prime_energy (Y Z R : ℝ) (s : ℕ)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) ≤
      (Y + 4 * R ^ 2) * Y := by
  sorry

/-- Weighted Cauchy Schwarz before the two analytic moments, journal display 15. -/
theorem block_cauchy (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ) (hR : 1 ≤ R) :
    (∑ r ∈ blockModuli R, (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √(blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1)) / R := by
  let f : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * i.2 n‖
  let g : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), i.2 p‖
  let w : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ := fun i =>
    (i.1 : ℝ) / i.1.totient
  have hRp : 0 < R := by linarith
  have hcs := LeanLab.PNTPort.LargeSieve.cs_weighted (blockCharacters R) w f g
    (fun _ _ => by dsimp [w]; positivity)
  have hsq : (∑ i ∈ blockCharacters R, w i * (f i * g i)) ^ 2 ≤
      blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c *
        blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    simpa only [blockEnergy, w, f, g, one_mul] using hcs
  have hroot := Real.le_sqrt_of_sq_le hsq
  apply le_trans _ (div_le_div_of_nonneg_right hroot hRp.le)
  rw [sum_div]
  change _ ≤ ∑ i ∈ (blockModuli R).sigma (fun r =>
      (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive)),
      w i * (f i * g i) / R
  rw [sum_sigma]
  apply sum_le_sum
  intro r hr
  rw [primitiveTerm, mul_sum]
  apply sum_le_sum
  intro χ hχ
  change (r.totient : ℝ)⁻¹ * (_ * _) ≤
    ((r : ℝ) / r.totient) * (_ * _) / R
  have hrr : R ≤ (r : ℝ) := (mem_filter.mp hr).2
  have hφ : (0 : ℝ) ≤ (r.totient : ℝ)⁻¹ := by positivity
  have hweight : (r.totient : ℝ)⁻¹ ≤ ((r : ℝ) / r.totient) / R := by
    apply (le_div_iff₀ hRp).mpr
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hrr hφ
  simpa only [div_mul_eq_mul_div] using
    mul_le_mul_of_nonneg_right hweight (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Exact statement of Decomp148c.dyadic_block, assembled from the two separate moments.
CONDITIONAL ON coefficient_energy and prime_energy. No direct sorry. -/
theorem dyadic_block (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    (∑ r ∈ (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R := by
  apply (block_cauchy c X Y Z R s hR).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Real.sqrt_le_sqrt
  have ha := coefficient_energy c X R s hc hX hR
  have hb := prime_energy Y Z R s hY hZ hZY hR
  have hnon : 0 ≤ blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    unfold blockEnergy
    exact sum_nonneg (fun _ _ => by positivity)
  have hx : 0 ≤ (X + 4 * R ^ 2) * X := by positivity
  convert mul_le_mul ha hb hnon hx using 1 <;> ring

end
end LeanLab.BS2022GRH.Decomp374a

#print axioms LeanLab.BS2022GRH.Decomp374a.coefficient_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.prime_energy
#print axioms LeanLab.BS2022GRH.Decomp374a.block_cauchy
#print axioms LeanLab.BS2022GRH.Decomp374a.dyadic_block
