/-
P0093 pages 162 to 165. Separate phase concentration from binary entropy.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Truncation412

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- P0093 page 163 equation 7.11. Indices of the first M positive
powers whose phase lies within two to negative r of an integer. -/
noncomputable def nearIntegerIndices412 (M r : ℕ) (α : ℝ) : Finset ℕ := by
  classical
  exact (range M).filter fun m => ∃ z : ℤ,
    |α * (2 : ℝ) ^ (m + 1) - z| ≤ (1 / 2 : ℝ) ^ r

/-- P0093 page 163 equation 7.11. At phase zero every index qualifies.
This certifies that the binary concentration set is nonempty. -/
theorem near_indices_zero412 (M r : ℕ) : nearIntegerIndices412 M r 0 = range M := by
  classical
  apply Finset.filter_eq_self.mpr
  intro m hm
  exact ⟨0, by simp⟩

/-- LEAF. P0093 page 162 equations 7.8 and 7.9 and page 163 through
7.11. Choosing a small large value margin forces any prescribed fraction
of the dyadic phases within any prescribed fixed binary radius of an
integer. This is only phase concentration. It has no measure estimate
and no binary word count. Parameters replace the printed intermediate
constants, since the proof lets eta tend to zero. -/
theorem finite_phase_concentration412 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (r : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, α ∈ Set.Icc (-1) 2 →
        (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖ →
          (1 - ε) * (Nat.log 2 N : ℝ) ≤
            (nearIntegerIndices412 (Nat.log 2 N) r α).card := by
  sorry

/-- LEAF. P0093 page 163 binary expansion 7.12 through page 165
7.19. For any positive entropy exponent choose a small exceptional
fraction and a long binary run radius so that the corresponding set
of phases has measure at most C times two to M times delta minus one.
This contains only the binary dynamics and their measure, without any
Fourier sum or damping parameter N. -/
theorem binary_entropy_measure412 (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∃ r : ℕ, 4 ≤ r ∧
      ∃ C : ℝ, 0 < C ∧ ∃ M0 : ℕ, ∀ M : ℕ, M0 < M →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - ε) * (M : ℝ) ≤ (nearIntegerIndices412 M r α).card} ≤
            C * (2 : ℝ) ^ ((M : ℝ) * (δ - 1)) := by
  sorry

/-- P0093 page 165 conversion from binary length to N after 7.19.
For a negative exponent a between negative one and zero, using the
integer logarithm costs at most a factor two. -/
theorem dyadic_measure_scale412 (N : ℕ) (hN : 1 ≤ N) (a : ℝ)
    (ha : -1 ≤ a) (ha0 : a ≤ 0) :
    (2 : ℝ) ^ ((Nat.log 2 N : ℝ) * a) ≤ 2 * (N : ℝ) ^ a := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut : (N : ℝ) / 2 ≤ (2 : ℝ) ^ Nat.log 2 N := by
    have hh : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N).le
    rw [pow_succ] at hh
    linarith
  have hpow : (2 : ℝ) ^ (-a) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := Real.rpow_one _
  calc
    _ = ((2 : ℝ) ^ Nat.log 2 N) ^ a := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    _ ≤ ((N : ℝ) / 2) ^ a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcut ha0
    _ = (N : ℝ) ^ a * (2 : ℝ) ^ (-a) := by
      rw [Real.div_rpow hNp.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ (N : ℝ) ^ a * 2 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- P0093 pages 162 to 165 proof of Lemma 4 after truncation.
Exact finite_large_value_measure412 statement, assembled from the
strictly smaller phase concentration and binary entropy leaves.
CONDITIONAL only on those two inputs. -/
theorem finite_large_value_measure_decomposed412 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  obtain ⟨ε, hε, hεhalf, r, hr, C, hC, M0, hm⟩ :=
    binary_entropy_measure412 (1 / 200) (by norm_num)
  obtain ⟨η, hη, hηhalf, Na, ha⟩ := finite_phase_concentration412 ε hε hεhalf r
  refine ⟨η, hη, hηhalf, 2 * C, by positivity, max 1 (max Na (2 ^ (M0 + 1))), ?_⟩
  intro N hN
  have h1 : 1 ≤ N := by have := le_max_left 1 (max Na (2 ^ (M0 + 1))); omega
  have hNa : Na < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hpow : 2 ^ (M0 + 1) ≤ N := by
    have := le_trans (le_max_right Na (2 ^ (M0 + 1))) (le_max_right 1 (max Na (2 ^ (M0 + 1))))
    omega
  have hM : M0 < Nat.log 2 N := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hpow
    omega
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} ⊆
      {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412 (Nat.log 2 N) r α).card} :=
    fun α hα => ⟨hα.1, ha N hNa α hα.1 hα.2⟩
  have hfinite : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412 (Nat.log 2 N) r α).card} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  calc
    _ ≤ volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - ε) * (Nat.log 2 N : ℝ) ≤ (nearIntegerIndices412 (Nat.log 2 N) r α).card} :=
      measureReal_mono hsub hfinite
    _ ≤ C * (2 : ℝ) ^ ((Nat.log 2 N : ℝ) * ((1 / 200 : ℝ) - 1)) := hm _ hM
    _ ≤ C * (2 * (N : ℝ) ^ ((1 / 200 : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (dyadic_measure_scale412 N h1 _ (by norm_num) (by norm_num)) hC.le
    _ = _ := by ring

end LeanLab.Linnik1951
