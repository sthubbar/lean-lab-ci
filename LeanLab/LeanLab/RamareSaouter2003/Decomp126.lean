import LeanLab.RamareSaouter2003.Lemma1Zeta
import LeanLab.RamareSaouter2003.MuStar55Cert
import LeanLab.RamareSaouter2003.Row58Bounds

/-!
P0099, Theorem 2 at Table 1 row 58, printed pp. 11 and 12.
The written proof uses Theorem 4 on pp. 17 to 21.
AI wrote this Lean code. Binary Goldbach is OPEN.
The assembly is CONDITIONAL ON the remaining LEAF statements.
-/

namespace LeanLab.RamareSaouter2003.Decomp126

open Real LeanLab.RamareSaouter2003.Smooth
  LeanLab.RamareSaouter2003.Row1 LeanLab.RamareSaouter2003.Row59

/-- CITED. Theorem 2, Table 1 row 58, printed pp. 11 and 12. -/
def theorem2_row58_stmt : Prop := ∀ x : ℝ, Real.exp 58 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209026205) < p ∧ (p : ℝ) ≤ x

/-- LEAF. Theorem 4 specialized to the true zero count and the verified height.
Printed pp. 17 to 20. External sources are Wedeniwski for the RH height,
Montgomery and Vaughan for Brun-Titchmarsh, and Schoenfeld for psi minus theta.
The existing Theorem4LiteralZeta assembly records the analytic subinputs. -/
theorem theorem4_cited : Theorem4Fm L1Zeta.NZr 3300000000 := by
  sorry

/-- LEAF. Lemma 1 upper bound for the true zero count. Printed p. 14.
External source: Rosser 1941, Theorem 19. -/
theorem lemma1_cited : Lemma1Upper L1Zeta.NZr := by
  sorry

/-- LEAF. Positivity of alpha3 for Table 1 row 58. Printed p. 11 and
Theorem 4 definition on p. 17. Uses the recurrence of Lemma 6 on p. 21. -/
theorem alpha3_positive : 0 < alpha3inv 55 0.004 2548 (25 / 40) 0.44522 := by
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ fm 55 t := by
    intro t ht
    unfold fm
    have : 0 ≤ 4 * t * (1 - t) := by nlinarith [ht.1, ht.2]
    positivity
  have hleft : (∫ t in (0 : ℝ)..0.44522, fm 55 t) ≤ ∫ t in (0 : ℝ)..0.44529, fm 55 t := by
    apply intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hf t ⟨ht.1.le, by linarith [ht.2]⟩
    · exact (continuous_fm 55).intervalIntegrable _ _
  have hright : (∫ t in (1 - 0.44522 : ℝ)..1, fm 55 t) ≤
      ∫ t in (1 - 0.44529 : ℝ)..1, fm 55 t := by
    apply intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hf t ⟨by linarith [ht.1], ht.2⟩
    · exact (continuous_fm 55).intervalIntegrable _ _
  have hnorm : 0 ≤ ∫ t in (0 : ℝ)..1, fm 55 t := by rw [norm_fm]; positivity
  have hw : w 55 0.44522 ≤ w 55 (44529 / 100000) := by
    unfold w v
    norm_num at hleft hright ⊢
    exact div_le_div_of_nonneg_right (add_le_add hleft hright) hnorm
  have hwb := hw.trans w55_bounds.2
  unfold alpha3inv
  norm_num
  norm_num at hwb
  linarith

/-- LEAF. The lower threshold meets Theorem 4's size assumption.
Theorem 2, printed p. 12, with Table 1 row 58 on p. 11. -/
theorem threshold {Y : ℝ} (hY : Real.exp 58 ≤ Y) : 2 * 10 ^ 12 ≤ Y := by
  have he := (exp_pow_bounds 58 (by norm_num)).1
  have hn : (2 * 10 ^ 12 : ℝ) < (2.7182818283 : ℝ) ^ 58 := by norm_num
  linarith

/-- LEAF. The zero count condition for Table 1 row 58 from Lemma 1.
Printed pp. 11, 14 and 18. CONDITIONAL ON the counting bound. -/
theorem count_condition {NT : ℝ → ℝ} (hN : Lemma1Upper NT) {Y : ℝ}
    (hY : Real.exp 58 ≤ Y) : 2 * NT 2607000000 ≤ 0.004 * √Y := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, e2⟩ := exp_pow_bounds 19 (by norm_num)
  have hx : (0 : ℝ) < 2607000000 / (2 * π) := by positivity
  have hrlo : (1 : ℝ) ≤ (2607000000 / (2 * π)) / (2 * Real.exp 19) := by
    rw [le_div_iff₀ (by positivity)]
    have hd : (2607000000 : ℝ) / (2 * 3.141593) ≤ 2607000000 / (2 * π) := by gcongr
    have hn : (2 : ℝ) * 2.7182818286 ^ 19 ≤ 2607000000 / (2 * 3.141593) := by norm_num
    linarith
  have hrhi : (2607000000 / (2 * π)) / (2 * Real.exp 19) ≤ (1.166 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hd : (2607000000 : ℝ) / (2 * π) ≤ 2607000000 / (2 * 3.141592) := by gcongr
    have hn : (2607000000 : ℝ) / (2 * 3.141592) ≤ 1.166 * (2 * 2.7182818283 ^ 19) := by norm_num
    linarith
  have hlogs := log_two_exp_bounds (2607000000 / (2 * π)) hx 19 (by norm_num)
    1 1.166 (by norm_num) hrlo hrhi
  have hlog : Real.log (2607000000 / (2 * π)) ≤ 19.86 := by linarith [hlogs.2]
  have hs : (2.7182818283 : ℝ) ^ 29 ≤ √Y := by
    have hroot := Real.sqrt_le_sqrt hY
    rw [← Real.exp_half] at hroot
    norm_num at hroot
    exact (exp_pow_bounds 29 (by norm_num)).1.le.trans hroot
  have hmain : (2607000000 : ℝ) / (2 * π) * Real.log (2607000000 / (2 * π)) -
      2607000000 / (2 * π) ≤ 2607000000 / (2 * 3.141592) * (19.86 - 1) := by
    have hd : (2607000000 : ℝ) / (2 * π) ≤ 2607000000 / (2 * 3.141592) := by gcongr
    nlinarith [mul_le_mul hd (show Real.log (2607000000 / (2 * π)) - 1 ≤ 19.86 - 1 by linarith)
      (by linarith [hlogs.1]) (by norm_num : (0 : ℝ) ≤ 2607000000 / (2 * 3.141592))]
  have hn := hN 2607000000 (by norm_num)
  have hnum : 2 * ((2607000000 : ℝ) / (2 * 3.141592) * (19.86 - 1) + 7 / 8 + 0.67 * 19.86) ≤
      0.004 * 2.7182818283 ^ 29 := by norm_num
  nlinarith

/-- LEAF. The upper bounds on u for Table 1 row 58 from Lemma 6.
Printed pp. 11, 18 and 21. The two conclusions are the small smoothing
condition and the interval width. -/
theorem upper_conditions (hμ : MuStar55Bounds) {Y : ℝ} (hY : Real.exp 58 ≤ Y) :
    55 * uRS 55 0.004 2548 (25 / 40) 0.44522 Y 2607000000 3300000000 ≤ 0.0001 ∧
      uRS 55 0.004 2548 (25 / 40) 0.44522 Y 2607000000 3300000000 *
        (1 + (1 - 2 * 0.44522) * 55) ≤ 1 / 209026205 := by
  have h := Row58Bounds.parameters hμ Y hY
  simp only [show (44522 / 100000 : ℝ) = 0.44522 by norm_num] at h
  exact ⟨h.1, h.2.2.2⟩

/-- LEAF. The lower bounds on u for Table 1 row 58 from Lemma 6.
Printed pp. 11, 18 and 21. These are the two growth conditions in Theorem 4. -/
theorem lower_conditions (hμ : MuStar55Bounds) {Y : ℝ} (hY : Real.exp 58 ≤ Y) :
    2548 ≤ uRS 55 0.004 2548 (25 / 40) 0.44522 Y 2607000000 3300000000 * √Y ∧
      Y ^ ((25 : ℝ) / 40) ≤
        uRS 55 0.004 2548 (25 / 40) 0.44522 Y 2607000000 3300000000 * Y := by
  have h := Row58Bounds.parameters hμ Y hY
  simp only [show (44522 / 100000 : ℝ) = 0.44522 by norm_num] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- Theorem 2 row 58 assembled from its analytic and numerical leaves.
CONDITIONAL ON all remaining LEAF statements. No sorry occurs in this assembly. -/
theorem theorem2_row58 : theorem2_row58_stmt := by
  intro Y hY
  have hμ := MuStar55Cert.muStar55Bounds
  obtain ⟨hsmall, hwidth⟩ := upper_conditions hμ hY
  obtain ⟨hroot, hpower⟩ := lower_conditions hμ hY
  exact prime_of_theorem4 theorem4_cited (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) alpha3_positive
    (threshold hY) (by norm_num) (count_condition lemma1_cited hY) hsmall hroot hpower
    (by norm_num) hwidth

end LeanLab.RamareSaouter2003.Decomp126
