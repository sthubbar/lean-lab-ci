/-
P0093 pages 164 and 165. Finish the entropy fraction and measure estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.EntropyBridge412

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 page 164 equation 7.18 and page 165 equation 7.19.
The entropy cost tends to zero with the exceptional fraction.
This is the parameter choice after the binary word count. -/
theorem entropy_fraction435 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2 := by
  have hcont : Continuous (fun x : ℝ => x - x * Real.log x) :=
    continuous_id.sub Real.continuous_mul_log
  have hbudget : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos (by norm_num))
  have hevent : ∀ᶠ x : ℝ in nhds 0, x - x * Real.log x < δ * Real.log 2 := by
    have ht : Tendsto (fun x : ℝ => x - x * Real.log x) (nhds 0) (nhds 0) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    exact ht.eventually (gt_mem_nhds hbudget)
  obtain ⟨a, ha, haall⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε : ℝ := min (a / 2) (1 / 4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεa : ε < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  refine ⟨ε, hε, by linarith, ?_⟩
  have hb := haall (show dist ε 0 < a by simpa [Real.dist_eq, abs_of_pos hε] using hεa)
  rw [Real.log_div (Real.exp_ne_zero _) hε.ne', Real.log_exp]
  nlinarith

/-- P0093 page 165 after equation 7.19. The explicit finite word
bound is at most four times the prescribed dyadic measure scale once
the entropy cost is below delta log two. -/
theorem entropy_unit_bound435 (M r : ℕ) (hM : 2 ≤ M) (hr : 4 ≤ r)
    (ε δ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hcost : ε * Real.log (Real.exp 1 / ε) ≤ δ * Real.log 2) :
    volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
        ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  have hsmall : ε * (M : ℝ) ≤ (M - 1 : ℕ) := by
    rw [hcast]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hbase : Real.exp 1 * (M - 1 : ℕ) / (ε * M) ≤ Real.exp 1 / ε := by
    rw [div_le_div_iff₀ (mul_pos hε hMp) hε]
    have hm : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
    calc
      Real.exp 1 * (M - 1 : ℕ) * ε = (Real.exp 1 * ε) * (M - 1 : ℕ) := by ring
      _ ≤ (Real.exp 1 * ε) * M := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Real.exp 1 * (ε * M) := by ring
  have hp : (Real.exp 1 * (M - 1 : ℕ) / (ε * M)) ^ (ε * M) ≤
      (2 : ℝ) ^ ((M : ℝ) * δ) := by
    calc
      _ ≤ (Real.exp 1 / ε) ^ (ε * M) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ ≤ (2 : ℝ) ^ ((M : ℝ) * δ) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by norm_num)]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hcost hMp.le]
  refine (binary_unit_measure_explicit412 M r hr ε (mul_pos hε hMp) hsmall).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ 4 * (2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ (M + 1) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ ≤ 4 * (2 : ℝ) ^ ((M : ℝ) * δ) / (2 : ℝ) ^ M := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M]
    _ = _ := by
      rw [← Real.rpow_natCast, mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

/-- P0093 page 165 measure conclusion after equation 7.19.
Three consecutive periods cost at most three unit period measures.
Integer translation preserves the concentration predicate. -/
theorem entropy_three_periods435 (M r : ℕ) (ε : ℝ) :
    volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
      3 * volume {α : ℝ | α ∈ Set.Ico 0 1 ∧
        (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} := by
  let s : Set ℝ := {α | α ∈ Set.Ico 0 1 ∧
    (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card}
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ⊆
      ((fun α : ℝ => α + 1) ⁻¹' s) ∪ s ∪
        ((fun α : ℝ => α + (-1)) ⁻¹' s) ∪ {2} := by
    intro α hα
    by_cases h0 : α < 0
    · apply Set.mem_union_left
      apply Set.mem_union_left
      apply Set.mem_union_left
      refine ⟨⟨by linarith [hα.1.1], by linarith⟩, ?_⟩
      simpa only [show (1 : ℝ) = (1 : ℤ) by norm_num,
        near_indices_int_shift412] using hα.2
    · by_cases h1 : α < 1
      · exact Or.inl (Or.inl (Or.inr ⟨⟨by linarith, h1⟩, hα.2⟩))
      · by_cases h2 : α < 2
        · apply Set.mem_union_left
          apply Set.mem_union_right
          refine ⟨⟨by linarith, by linarith⟩, ?_⟩
          simpa only [show (-1 : ℝ) = (-1 : ℤ) by norm_num,
            near_indices_int_shift412] using hα.2
        · exact Or.inr (by simpa only [Set.mem_singleton_iff] using
            (show α = 2 by linarith [hα.1.2]))
  calc
    _ ≤ volume ((((fun α : ℝ => α + 1) ⁻¹' s) ∪ s) ∪
        ((fun α : ℝ => α + (-1)) ⁻¹' s) ∪ {2}) := measure_mono hsub
    _ ≤ ((volume ((fun α : ℝ => α + 1) ⁻¹' s) + volume s) +
        volume ((fun α : ℝ => α + (-1)) ⁻¹' s)) + volume ({2} : Set ℝ) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ = 3 * volume s := by
      rw [measure_preimage_add_right, measure_preimage_add_right]
      simp [show (3 : ENNReal) = 1 + 1 + 1 by norm_num, add_mul]

/-- P0093 pages 164 and 165 binary word count and measure conclusion.
The exact binary_entropy_measure412 statement has a clean proof from
the proved Gallagher word count. No cited entropy input is used. -/
theorem binary_entropy_measure_proved435 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∃ r : ℕ, 4 ≤ r ∧
      ∃ C : ℝ, 0 < C ∧ ∃ M0 : ℕ, ∀ M : ℕ, M0 < M →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
            C * (2 : ℝ) ^ ((M : ℝ) * (δ - 1)) := by
  obtain ⟨ε, hε, hεhalf, hc⟩ := entropy_fraction435 δ hδ
  refine ⟨ε, hε, hεhalf, 4, le_rfl, 12, by norm_num, 1, ?_⟩
  intro M hM
  have hu := entropy_unit_bound435 M 4 (by omega) le_rfl ε δ hε hεhalf hc
  have ht := (entropy_three_periods435 M 4 ε).trans (mul_le_mul' le_rfl hu)
  have he : (3 : ENNReal) * ENNReal.ofReal (4 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) =
      ENNReal.ofReal (12 * (2 : ℝ) ^ ((M : ℝ) * (δ - 1))) := by
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [he] at ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal

end LeanLab.Linnik1951
