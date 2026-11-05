/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the finite character cap and the two totient sums in journal display 13.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.BS2022GRH.DecompC164b
import LeanLab.BS2022GRH.Totient374

namespace LeanLab.BS2022GRH.Decomp374d
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The uniform character factor in display 13, journal p. 1224. -/
def smallFactor (Y D D₀ : ℝ) : ℝ :=
  1.3841 * log D / log (log D) + 2 * D₀ + 2 * D₀ * qG Y * √Y * log Y

/-- LEAF. Journal p. 1224 before display 13, the single conductor and cofactor cap.
Use the prime character bound, the contribution of prime divisors of s,
and Robin Theorem 11 through journal Lemma 4. There is no outer modulus sum. -/
theorem primitive_term_cap (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (r s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 5 ≤ D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hr : 3 ≤ r) (hrD : (r : ℝ) ≤ D₀)
    (hs : 1 ≤ s) (hsD : (s : ℝ) < D) :
    primitiveTerm c X Y Z r s ≤ D₀ * X * smallFactor Y D D₀ := by
  sorry

/-- LEAF. Journal p. 1224 display 13, the two reciprocal totient sums.
Apply Ramare Theorem 3.1 through journal Lemma 5 to the squarefree supports.
This estimate has no character, arbitrary coefficient sequence or GRH hypothesis. -/
theorem small_totient_mass (D D₀ : ℝ) (a : ℤ)
    (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀),
      (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹) ≤
      Mphi D₀ * Mphi D * log D ^ 2 := by
  exact Totient374.small_totient_mass_of_phi PublishedInputs232.lemma5_phi D D₀ a hD hD₀ hD₀D

/-- The balance assumptions force D at least five, journal p. 1224. -/
theorem five_le_level (X Y D D₀ : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀) : 5 ≤ D := by
  have hs : (25 : ℝ) ≤ √(X * Y) := by
    have hxy : 25 ^ 2 ≤ X * Y := by nlinarith
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr hxy
  have hm := (div_le_iff₀ (by linarith : 0 < D)).mp hbal
  have hmul := mul_le_mul_of_nonneg_right hD₀D (by linarith : 0 ≤ D)
  nlinarith

/-- The common cap is nonnegative on the source domain, journal display 13. -/
theorem smallFactor_nonneg (Y D D₀ : ℝ) (hY : 25 ≤ Y) (hD : 5 ≤ D)
    (hD₀ : 1 < D₀) : 0 ≤ smallFactor Y D D₀ := by
  have hlog : 1 ≤ log D := by
    rw [le_log_iff_exp_le (by linarith : 0 < D)]
    linarith [exp_one_lt_d9]
  have hq := DecompC164b.qG_positive Y hY
  have hylog : 0 ≤ log Y := log_nonneg (by linarith)
  have hll : 0 ≤ log (log D) := log_nonneg hlog
  unfold smallFactor
  positivity

/-- Exact statement of Decomp148b.small_conductors from the local cap and totient mass.
CONDITIONAL ON primitive_term_cap and small_totient_mass. No direct sorry. -/
theorem small_conductors (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    smallMass c X Y Z D D₀ a ≤ smallBound X Y D D₀ := by
  have hD5 := five_le_level X Y D D₀ hX hY hD hD₀D hbal
  have hfac := smallFactor_nonneg Y D D₀ hY hD5 hD₀
  let B : ℝ := D₀ * X * smallFactor Y D D₀
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum : smallMass c X Y Z D D₀ a ≤
      (∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀),
        (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹) * B := by
    unfold smallMass
    rw [sum_mul]
    apply sum_le_sum
    intro r hr
    obtain ⟨hrmem, hrD⟩ := mem_filter.mp hr
    have hr3 : 3 ≤ r := (mem_Ico.mp (mem_filter.mp hrmem).1).1
    unfold conductorTerm
    rw [mul_assoc, sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro s hs
    have hs1 : 1 ≤ s := (mem_Ico.mp (mem_filter.mp hs).1).1
    have hsquot : (s : ℝ) < D / r := Nat.lt_ceil.mp (mem_Ico.mp (mem_filter.mp hs).1).2
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hsD : (s : ℝ) < D := hsquot.trans_le
      (div_le_self (by linarith : 0 ≤ D) hr1)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact primitive_term_cap hG c X Y Z D D₀ r s hc hX hY hZ hZY hD5 hD₀ hD₀D
      hD₀Z hr3 hrD hs1 hsD
  apply hsum.trans
  have hw := mul_le_mul_of_nonneg_right (small_totient_mass D D₀ a hD hD₀ hD₀D) hB
  convert hw using 1 <;> dsimp [B, smallFactor, smallBound] <;> ring

end
end LeanLab.BS2022GRH.Decomp374d

#print axioms LeanLab.BS2022GRH.Decomp374d.primitive_term_cap
#print axioms LeanLab.BS2022GRH.Decomp374d.small_totient_mass
#print axioms LeanLab.BS2022GRH.Decomp374d.five_le_level
#print axioms LeanLab.BS2022GRH.Decomp374d.smallFactor_nonneg
#print axioms LeanLab.BS2022GRH.Decomp374d.small_conductors
