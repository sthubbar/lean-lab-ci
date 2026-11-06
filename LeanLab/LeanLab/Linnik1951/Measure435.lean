/-
P0093 pages 162 through 165. Exact measure and interval bridges.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Entropy435
import LeanLab.Linnik1951.Decomp435a
import LeanLab.Linnik1951.Decomp412a

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 pages 162 through 165 Lemma 4. Exact finite measure statement from the refined phase input and the proved binary entropy bound. -/
theorem finite_large_value_measure435 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  obtain ⟨ε, hε, hεhalf, r, hr, C, hC, M0, hm⟩ :=
    binary_entropy_measure_proved435 (1 / 200) (by norm_num)
  obtain ⟨η, hη, hηhalf, Na, ha⟩ := finite_phase_concentration_decomposed435 ε hε hεhalf r
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

/-- P0093 page 162 passage to 7.7 and page 165 conclusion. Exact full series measure statement through proved truncation transfer. -/
theorem large_value_measure435 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  obtain ⟨η, hη, hηhalf, C, hC, Nm, hm⟩ := finite_large_value_measure435
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

/-- P0093 page 165 Lemma 5. Exact interval cover statement through measure, local stability and packing. -/
theorem large_value_intervals435 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ I : Finset (ℝ × ℝ),
        (I.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ p ∈ I, p.2 - p.1 ≤ 1 / ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2) ∧
        {α : ℝ | α ∈ Set.Icc 0 1 ∧
          (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ⊆
          ⋃ p ∈ I, Set.Icc p.1 p.2 := by
  obtain ⟨η, hη, hηhalf, C, hC, Nm, hm⟩ := large_value_measure435
  obtain ⟨Ns, hs⟩ := large_value_stability412 η hη
  obtain ⟨Np, hp⟩ := log_le_small_power412
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨η, hη, by linarith, C, hC, max 2 (max Nm (max Ns (max Np L))), ?_⟩
  intro N hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hmN : Nm < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hsN : Ns < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hpN : Np < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hLN : L < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by positivity
  have hlog : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
  let δ := 1 / ((N : ℝ) * Real.log N)
  let s := {α : ℝ | α ∈ Set.Icc 0 1 ∧
    (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖}
  let t := {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
    (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖}
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) * Real.log N)).mpr
    nlinarith
  have ht : volume t ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc] : volume (Set.Icc (-1 : ℝ) 2) ≠ ⊤)
      (measure_mono (fun α hα => hα.1))
  obtain ⟨I, hcard, hlen, hcover⟩ := interval_packing412 s t (fun α hα => hα.1)
    ht δ hδ (by
      intro x hx y hy
      refine ⟨?_, ?_⟩
      · constructor <;> linarith [hx.1.1, hx.1.2, hy.1, hy.2]
      · have hdist : |y - x| ≤ δ := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
        simpa only [add_sub_cancel] using hs N hsN x (y - x) hdist hx.2)
  refine ⟨I, ?_, ?_, hcover⟩
  · have hbound : (I.card : ℝ) ≤ (C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1)) *
        ((N : ℝ) * Real.log N) := by
      have h := hcard.trans (hm N hmN)
      dsimp [δ] at h
      exact (div_le_iff₀ (by positivity : 0 < (N : ℝ) * Real.log N)).mp
        (by simpa only [mul_one_div] using h)
    calc
      _ ≤ (C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1)) * ((N : ℝ) * Real.log N) := hbound
      _ = C * (N : ℝ) ^ (1 / 200 : ℝ) * Real.log N := by
        have he : (N : ℝ) ^ ((1 / 200 : ℝ) - 1) * N = (N : ℝ) ^ (1 / 200 : ℝ) := by
          conv_lhs => rhs; rw [← Real.rpow_one (N : ℝ)]
          rw [← Real.rpow_add hNp]
          congr 1
          ring
        calc
          _ = C * ((N : ℝ) ^ ((1 / 200 : ℝ) - 1) * N) * Real.log N := by ring
          _ = _ := by rw [he]
      _ ≤ C * (N : ℝ) ^ (1 / 200 : ℝ) * (N : ℝ) ^ (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_left (hp N hpN) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hNp]; norm_num
  · intro p hpI
    apply (hlen p hpI).trans
    have hden : ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 ≤ (N : ℝ) * Real.log N := by
      calc
        _ = (N : ℝ) ^ (2 / 7 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; norm_num
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by norm_num)
        _ = N := Real.rpow_one _
        _ ≤ _ := le_mul_of_one_le_right hNp.le hlog
    exact one_div_le_one_div_of_le (by positivity) hden

end LeanLab.Linnik1951
