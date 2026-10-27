import LeanLab.Ricci1937.BetaTail

/-!
Ricci 1937, page 78 formula 1.11 and page 81 formula 2.6.
The beta bar series at theta = 0.50.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- The beta bar formula for b greater than one. Only b at least four is used here. -/
def ricciBetaBarTerm (q : ℝ) (b : ℕ) : ℝ :=
  q ^ b * ((b : ℝ) ^ (2 * b - 1) / ((2 * b).factorial : ℝ) -
    (1 / (2 : ℝ) ^ b) * (1 / (b : ℝ) + (5 : ℝ) / 6 * ((b : ℝ) - 2) +
      (7 : ℝ) / 20 * ((b : ℝ) - 2) * ((b : ℝ) - 3)))

/-- The subtracted correction in formula 1.11. -/
def ricciBetaCorrection (q : ℝ) (b : ℕ) : ℝ :=
  (q / 2) ^ b * (1 / (b : ℝ) + (5 : ℝ) / 6 * ((b : ℝ) - 2) +
    (7 : ℝ) / 20 * ((b : ℝ) - 2) * ((b : ℝ) - 3))

lemma ricciBetaBar_decomp (q : ℝ) (b : ℕ) :
    ricciBetaBarTerm q b = ricciBetaMajorant q b - ricciBetaCorrection q b := by
  unfold ricciBetaBarTerm ricciBetaMajorant ricciBetaCorrection
  rw [div_pow]
  ring

lemma ricciBetaCorrection_bounds {b : ℕ} (hb : 4 ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ ricciBetaCorrection q b ∧
      ricciBetaCorrection q b ≤ 3 * ((b : ℝ) ^ (2 : ℕ) * (q / 2) ^ b) := by
  have hbR : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hb2 : 0 ≤ (b : ℝ) - 2 := by linarith
  have hb3 : 0 ≤ (b : ℝ) - 3 := by linarith
  have hinv : 1 / (b : ℝ) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hpoly : 1 / (b : ℝ) + (5 : ℝ) / 6 * ((b : ℝ) - 2) +
      (7 : ℝ) / 20 * ((b : ℝ) - 2) * ((b : ℝ) - 3) ≤ 3 * (b : ℝ) ^ (2 : ℕ) := by
    nlinarith
  unfold ricciBetaCorrection
  constructor
  · positivity
  · have h := mul_le_mul_of_nonneg_left hpoly (pow_nonneg (by positivity : (0 : ℝ) ≤ q / 2) b)
    nlinarith

/-- The beta bar series converges throughout the required parameter range. -/
theorem ricciBetaBar_summable {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.413) :
    Summable (fun k : ℕ => ricciBetaBarTerm q (4 + k)) := by
  have hdom : Summable (fun k : ℕ => ricciBetaMajorant q 4 * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hmain : Summable (fun k : ℕ => ricciBetaMajorant q (4 + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold ricciBetaMajorant; positivity)
      (ricciBetaMajorant_shift_le (by norm_num) hq0 hq)
  have hr : ‖q / 2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
  have hpoly := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hshift : Summable (fun k : ℕ => ((4 + k : ℕ) : ℝ) ^ (2 : ℕ) * (q / 2) ^ (4 + k)) :=
    hpoly.comp_injective (fun i j h => by omega)
  have hcorr : Summable (fun k : ℕ => ricciBetaCorrection q (4 + k)) :=
    (hshift.mul_left 3).of_nonneg_of_le
      (fun k => (ricciBetaCorrection_bounds (by omega : 4 ≤ 4 + k) hq0).1)
      (fun k => (ricciBetaCorrection_bounds (by omega : 4 ≤ 4 + k) hq0).2)
  convert hmain.sub hcorr using 1
  funext k
  exact ricciBetaBar_decomp q (4 + k)

/-- Monotonicity in q for the nine explicitly retained head terms. -/
lemma ricciBetaBar_head_le {q Q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Q) :
    (∑ k ∈ range 9, ricciBetaBarTerm q (4 + k)) ≤
      ∑ k ∈ range 9, ricciBetaBarTerm Q (4 + k) := by
  apply sum_le_sum
  intro k hk
  have hk9 : k < 9 := mem_range.mp hk
  unfold ricciBetaBarTerm
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq _)
  interval_cases k <;> norm_num [Nat.factorial]

/-- The retained finite head plus the positive majorant tail is below 0.02185. -/
theorem ricciBetaBar_head_tail_lt {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.4121805) :
    (∑ k ∈ range 9, ricciBetaBarTerm q (4 + k)) +
      (∑' k : ℕ, ricciBetaMajorant q (13 + k)) < 0.02185 := by
  have hhead := ricciBetaBar_head_le hq0 hq
  have htail := ricciBetaMajorant_tail_le (B := 13) (by norm_num) hq0
    (show q ≤ 0.413 by linarith)
  have h13 : ricciBetaMajorant q 13 ≤ ricciBetaMajorant (0.4121805 : ℝ) 13 := by
    unfold ricciBetaMajorant
    gcongr
  have hnum : (∑ k ∈ range 9, ricciBetaBarTerm (0.4121805 : ℝ) (4 + k)) +
      ricciBetaMajorant (0.4121805 : ℝ) 13 / (1 - 0.86) < 0.02185 := by
    norm_num [sum_range_succ, ricciBetaBarTerm, ricciBetaMajorant, Nat.factorial]
  have h13div := div_le_div_of_nonneg_right h13 (by norm_num : (0 : ℝ) ≤ 1 - 0.86)
  linarith

lemma ricciBetaBar_le_majorant {b : ℕ} (hb : 4 ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    ricciBetaBarTerm q b ≤ ricciBetaMajorant q b := by
  rw [ricciBetaBar_decomp]
  exact sub_le_self _ (ricciBetaCorrection_bounds hb hq).1

/-- The complete beta bar tail is below 0.02185 on the required interval. -/
theorem ricciBetaBar_tail_lt {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 0.4121805) :
    (∑' k : ℕ, ricciBetaBarTerm q (4 + k)) < 0.02185 := by
  have hq413 : q ≤ 0.413 := by linarith
  have hsum := ricciBetaBar_summable hq0 hq413
  have htail : Summable (fun k : ℕ => ricciBetaBarTerm q (13 + k)) := by
    have hs : Summable (fun k : ℕ => ricciBetaBarTerm q (4 + (9 + k))) :=
      hsum.comp_injective (fun i j h => by omega)
    simpa only [← Nat.add_assoc] using hs
  have hdom : Summable (fun k : ℕ => ricciBetaMajorant q 13 * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hmajor : Summable (fun k : ℕ => ricciBetaMajorant q (13 + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold ricciBetaMajorant; positivity)
      (ricciBetaMajorant_shift_le (by norm_num) hq0 hq413)
  have htaille := htail.tsum_le_tsum
    (fun k => ricciBetaBar_le_majorant (by omega : 4 ≤ 13 + k) hq0) hmajor
  have hsplit : (∑' k : ℕ, ricciBetaBarTerm q (4 + k)) =
      (∑ k ∈ range 9, ricciBetaBarTerm q (4 + k)) +
        ∑' k : ℕ, ricciBetaBarTerm q (13 + k) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hsum.sum_add_tsum_nat_add 9).symm
  rw [hsplit]
  exact lt_of_le_of_lt (add_le_add le_rfl htaille) (ricciBetaBar_head_tail_lt hq0 hq)

/-- The actual lower sieve parameter lies in the verified interval. -/
lemma ricci_beta_parameter_le :
    0 ≤ exp (0.5 : ℝ) / 4 ∧ exp (0.5 : ℝ) / 4 ≤ 0.4121805 := by
  have he : exp (0.5 : ℝ) ≤ 1.648722 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  exact ⟨by positivity, by linarith⟩

/-- Formula 2.6 with a stronger explicit tail bound. -/
theorem ricciBetaBar_lowerParameters_lt :
    (∑' k : ℕ, ricciBetaBarTerm (exp (0.5 : ℝ) / 4) (4 + k)) < 0.02185 :=
  ricciBetaBar_tail_lt ricci_beta_parameter_le.1 ricci_beta_parameter_le.2

example : (∑' k : ℕ, ricciBetaBarTerm (0.4 : ℝ) (4 + k)) < 0.02185 :=
  ricciBetaBar_tail_lt (by norm_num) (by norm_num)

end
end LeanLab.Ricci1937
