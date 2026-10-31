import LeanLab.LanguascoPerelli1996.Mass108

/-!
P0071 Lemma 2, pages 354 and 355. Decomposition by CODEX task108.
The original cited statement remains sealed.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp108
open Real

/-- The function G on page 354, expressed using the existing zero band sum. -/
noncomputable def energy (X U T : ℝ) (q : ℕ) [NeZero q] (a : ℕ) (v : ℝ) : ℝ :=
  ‖zSum (X * Real.exp v) U T q a‖ ^ 2

/-- LEAF. Page 354 display 11 and page 355 display 12.
The local mass of the difference of the two zero sums is controlled by
the sum of their two full weighted correlation integrals. -/
theorem local_mass_control :
    GRH → ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        (∫ v in (-1 : ℝ)..1, energy X U T q a v) ≤ A * (‖F X T q a‖ + ‖F X U q a‖) := by
  intro _
  have he : 1 ≤ Real.exp 2 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  refine ⟨2 * Real.exp 2, by linarith, ?_⟩
  intro X hX U T hU hUT q inst a ha
  exact Mass108.band_local_mass hX U T hUT.le q a


/-- LEAF. Page 355, display 12. Sobolev Gallagher and identity 11 control the
endpoint. The Sobolev input is Montgomery 1971, Lemma 1.1, reference 13. -/
theorem endpoint_control :
    GRH → ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q →
        ‖zSum X U T q a‖ ^ 2 ≤ A * (‖F X T q a‖ + ‖F X U q a‖ +
          ∫ v in (-1 : ℝ)..1, |deriv (energy X U T q a) v|) := by
  intro hGRH
  obtain ⟨A, hA, hm⟩ := local_mass_control hGRH
  refine ⟨A, by linarith, ?_⟩
  intro X hX U T hU hUT q inst a ha
  have hs := Band108.band_sobolev hX U T q a
  have hb := hm X hX U T hU hUT q a ha
  have hv0 : 0 ≤ ∫ v in (-1 : ℝ)..1, |deriv (energy X U T q a) v| :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => abs_nonneg _)
  have hv := mul_le_mul_of_nonneg_right hA hv0
  simp only [one_mul] at hv
  change ‖zSum X U T q a‖ ^ 2 ≤
    (∫ v in (-1 : ℝ)..1, energy X U T q a v) +
      (∫ v in (-1 : ℝ)..1, |deriv (energy X U T q a) v|) at hs
  nlinarith


/-- LEAF. Page 355, display 13 in the large height range T at least one.
Cauchy Schwarz and partial summation bound the total variation by a constant
times T times a uniform correlation bound. No small height assertion is made. -/
theorem variation_control :
    GRH → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          (∫ v in (-1 : ℝ)..1, |deriv (energy X U T q a) v|) ≤ B * T * M := by
  sorry

/-- LEAF. Page 355, assembly of displays 12 and 13 for T at least one. -/
theorem large_height_square {z : ℂ} {A B T M E FT FU : ℝ}
    (hA : 0 ≤ A) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hFT : FT ≤ M) (hFU : FU ≤ M)
    (he : ‖z‖ ^ 2 ≤ A * (FT + FU + E)) (hv : E ≤ B * T * M) :
    ‖z‖ ^ 2 ≤ A * (2 + B) * T * M := by
  have hbase : FT + FU + E ≤ (2 + B) * T * M := by
    have hMT : M ≤ T * M := by nlinarith
    nlinarith
  calc
    ‖z‖ ^ 2 ≤ A * (FT + FU + E) := he
    _ ≤ A * ((2 + B) * T * M) := mul_le_mul_of_nonneg_left hbase hA
    _ = A * (2 + B) * T * M := by ring

/-- LEAF. Page 355, displays 12 and 13 in the large height range T at least one.
The historical name is retained for the reviewer correction. This theorem
makes no assertion for T below one. It is CONDITIONAL ON variation_control. -/
theorem small_height_control :
    GRH → ∃ D : ℝ, 0 ≤ D ∧ ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          ‖zSum X U T q a‖ ^ 2 ≤ D * T * M := by
  intro hGRH
  obtain ⟨A, hA, he⟩ := endpoint_control hGRH
  obtain ⟨B, hB, hv⟩ := variation_control hGRH
  refine ⟨A * (2 + B), by positivity, ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM U le_rfl hUT.le)
  exact large_height_square hA hT hM0 (hM T hUT.le le_rfl)
    (hM U le_rfl hUT.le) (he X hX U T hU hUT q a ha)
    (hv X hX U T hU hUT hT q a ha M hM)

/-- LEAF. Page 355, final square root step after displays 12 and 13. -/
theorem square_to_rpow {z : ℂ} {C T M : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (h : ‖z‖ ^ 2 ≤ C * T * M) :
    ‖z‖ ≤ Real.sqrt C * T ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
  have hs : ‖z‖ ≤ Real.sqrt (C * T * M) :=
    (Real.le_sqrt (norm_nonneg z) (by positivity)).mpr h
  simpa only [Real.sqrt_mul (mul_nonneg hC hT), Real.sqrt_mul hC,
    Real.sqrt_eq_rpow] using hs

/-- Lemma 2 in the large height range T at least one supported by the
absorption of display 12 into display 13 on page 355.
CONDITIONAL ON variation_control. This is a range restricted result, not
an assembly of the unrestricted sealed Lemma2 Prop. -/
theorem lemma2_decomposed :
    GRH → ∃ K : ℝ, ∀ X : ℝ, 0 < X → ∀ U T : ℝ, 0 ≤ U → U < T → 1 ≤ T →
      ∀ (q : ℕ) [NeZero q] (a : ℕ), Nat.Coprime a q → ∀ M : ℝ,
        (∀ u, U ≤ u → u ≤ T → ‖F X u q a‖ ≤ M) →
          ‖zSum X U T q a‖ ≤ K * T ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
  intro hGRH
  obtain ⟨D, hD, hd⟩ := small_height_control hGRH
  refine ⟨Real.sqrt D, ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM U le_rfl hUT.le)
  exact square_to_rpow hD (le_trans (by norm_num) hT) hM0
    (hd X hX U T hU hUT hT q a ha M hM)

/-- Link to the amended sealed `Lemma2`, which carries `1 ≤ T` since unit U-1566.
P0071 p. 354 and p. 355, displays 12 and 13. CONDITIONAL ON `variation_control`,
the one remaining LEAF sorry of this module. -/
theorem lemma2_of_decomposed : Lemma2 := lemma2_decomposed

end LeanLab.LanguascoPerelli1996.Decomp108

#print axioms LeanLab.LanguascoPerelli1996.Decomp108.lemma2_of_decomposed
#print axioms LeanLab.LanguascoPerelli1996.Decomp108.lemma2_decomposed
#print axioms LeanLab.LanguascoPerelli1996.Decomp108.small_height_control
