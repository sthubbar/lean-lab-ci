/-
P0093 pages 162 to 165. The finite binary entropy estimate after truncation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp412c

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. P0093 page 162 equation 7.7 through page 165 equation 7.19.
The alignment, binary run count and entropy estimate bound the large
value set of the finite polynomial. The damping tail and passage back
to the infinite series are excluded from this leaf. The printed exponent
tends to zero, so choose the fixed saving one two hundredth here. -/
theorem finite_large_value_measure412 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  exact finite_large_value_measure_decomposed412

/-- P0093 page 162 equation 7.7 and page 165 conclusion of Lemma 4.
Exact large_value_measure412 statement. The infinite series truncation
has a proved bounded error. CONDITIONAL only on the finite binary
entropy estimate, not on an additional analytic tail assertion. -/
theorem large_value_measure_proved412 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  obtain ⟨η, hη, hηhalf, C, hC, Nm, hm⟩ := finite_large_value_measure412
  obtain ⟨Nt, ht⟩ := large_value_to_trunc412 η hη (by linarith)
  refine ⟨η / 4, by positivity, by linarith, C, hC, max Nm Nt, ?_⟩
  intro N hN
  have hmN : Nm < N := lt_of_le_of_lt (le_max_left _ _) hN
  have htN : Nt < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hsub : {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - 2 * (η / 4)) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ⊆
      {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
        (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} := by
    intro α hα
    refine ⟨hα.1, ht N htN α ?_⟩
    convert hα.2 using 1 <;> ring
  have hfinite : volume {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
      (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  exact (measureReal_mono hsub hfinite).trans (hm N hmN)

end LeanLab.Linnik1951
