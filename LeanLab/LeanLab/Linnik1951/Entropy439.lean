/-
P0093 pages 164 and 165 equations 7.15 through 7.19.
Finish the entropy parameter and bounded period steps using the proved word count.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.EntropyBridge412
import LeanLab.Linnik1951.EntropyChoice439

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- P0093 page 165 after equation 7.19. Periodicity extends the unit
period binary concentration measure to three periods, with no loss except
the factor three. The remaining endpoint is a singleton of measure zero. -/
theorem binary_three_period_measure439 (M r : ℕ) (ε : ℝ) :
    volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
        3 * volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
          (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} := by
  let U := {α : ℝ | α ∈ Set.Ico 0 1 ∧
    (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card}
  let T : ℤ → Set ℝ := fun z => (fun α : ℝ => α + (z : ℝ)) ⁻¹' U
  have hshift (z : ℤ) : volume (T z) = volume U := measure_preimage_add_right volume _ _
  have hcover : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ⊆
        T 1 ∪ (T 0 ∪ (T (-1) ∪ {2})) := by
    intro α hα
    have hgood (z : ℤ) : (1 - ε) * (M : ℝ) ≤
        (nearIntegerIndices412 M r (α + (z : ℝ))).card := by
      rw [near_indices_int_shift412]
      exact hα.2
    by_cases hneg : α < 0
    · left
      exact ⟨⟨by norm_num; linarith [hα.1.1], by norm_num; linarith⟩, hgood 1⟩
    · right
      by_cases hone : α < 1
      · left
        exact ⟨⟨by norm_num; linarith, by norm_num; linarith⟩, hgood 0⟩
      · right
        by_cases htwo : α < 2
        · left
          exact ⟨⟨by norm_num; linarith, by norm_num; linarith⟩, hgood (-1)⟩
        · right
          simp only [Set.mem_singleton_iff]
          linarith [hα.1.2]
  calc
    _ ≤ volume (T 1 ∪ (T 0 ∪ (T (-1) ∪ {2}))) := measure_mono hcover
    _ ≤ volume (T 1) + volume (T 0 ∪ (T (-1) ∪ {2})) := measure_union_le _ _
    _ ≤ volume (T 1) + (volume (T 0) + (volume (T (-1)) + volume ({2} : Set ℝ))) :=
      add_le_add le_rfl ((measure_union_le (T 0) (T (-1) ∪ {2})).trans
        (add_le_add le_rfl (measure_union_le (T (-1)) {2})))
    _ = _ := by
      simp only [hshift, measure_singleton, add_zero]
      change volume U + (volume U + volume U) = 3 * volume U
      ring

/-- P0093 pages 164 and 165 equations 7.15 through 7.19. The explicit
binomial expression has the desired exponential rate once its entropy
coefficient is small. This step contains no binary word counting. -/
theorem binary_unit_entropy_bound439 (M : ℕ) (hM : 2 ≤ M) (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hentropy : ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2) :
    volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M 4 α).card} ≤
        ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hsub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  have hsmall : ε * (M : ℝ) ≤ (M - 1 : ℕ) := by rw [hsub]; nlinarith
  have hpositive : 0 < ε * (M : ℝ) := mul_pos hε hMp
  apply (binary_unit_measure_explicit412 M 4 le_rfl ε hpositive hsmall).trans
  apply ENNReal.ofReal_le_ofReal
  have hbase : Real.exp 1 * (M - 1 : ℕ) / (ε * M) ≤ Real.exp 1 / ε := by
    rw [div_le_div_iff₀ hpositive hε, hsub]
    nlinarith [Real.exp_pos 1]
  have hpow : (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) ≤
      (2 : ℝ) ^ ((M : ℝ) * δ) := by
    apply (Real.rpow_le_rpow (by positivity) hbase hpositive.le).trans
    rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos 1) hε),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hentropy hMp.le]
  have hden : (2 : ℝ) ^ M ≤ 2 ^ (M + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ 4 * (2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ M := by
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpow (by norm_num))
        (by positivity) hden
    _ = 4 * ((2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ (M : ℝ)) := by
      rw [Real.rpow_natCast]
      ring
    _ = _ := by rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]; congr 2; ring

/-- P0093 pages 163 through 165 binary expansion 7.12 through 7.19.
Exact binary_entropy_measure412 statement, supplied by the existing finite
word count, continuity of x log x and the three period measure extension. -/
theorem binary_entropy_measure_proved439 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∃ r : ℕ, 4 ≤ r ∧
      ∃ C : ℝ, 0 < C ∧ ∃ M0 : ℕ, ∀ M : ℕ, M0 < M →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
            C * (2 : ℝ) ^ ((M : ℝ) * (δ - 1)) := by
  obtain ⟨ε, hε, hεhalf, hentropy⟩ := entropy_fraction439 δ hδ
  refine ⟨ε, hε, hεhalf, 4, le_rfl, 12, by norm_num, 1, ?_⟩
  intro M hM
  have hunit := binary_unit_entropy_bound439 M (by omega) ε δ hε hεhalf hentropy
  have hthree := binary_three_period_measure439 M 4 ε
  have hbound : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M 4 α).card} ≤
        ENNReal.ofReal (12 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
    apply hthree.trans
    calc
      _ ≤ 3 * ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by gcongr
      _ = _ := ?_
    rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact hr.trans_eq (ENNReal.toReal_ofReal (by positivity))

end LeanLab.Linnik1951
