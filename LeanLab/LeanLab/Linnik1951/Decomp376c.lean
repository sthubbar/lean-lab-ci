/-
P0093 page 166 Lemmas 6 and 7. Separate the exceptional cover from local prime mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357c
import LeanLab.Linnik1951.Decomp111b
import LeanLab.Linnik1951.Decomp376e

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. P0093 page 165 Lemma 5 and page 166 Lemma 6. Choose eta so
that the large T minor set is covered by at most A N to one hundredth
systems of doubled rational arcs. This is a geometric statement without
GRH and without an integral of the prime series. -/
theorem exceptional_system_cover376 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ S : Finset ℕ,
        (S.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ q ∈ S, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        exceptionalArcs280 N η ⊆
          ⋃ q ∈ S, arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1 := by
  exact exceptional_system_cover_proved376

/-- LEAF. P0093 page 166 equation 9.1 and its use in equation 9.3.
For one doubled system with denominator between Q and tau, the prime
square integral has a fixed power saving. Exponent ninety eight
hundredths weakens the displayed local estimates after logarithmic
absorption. This leaf has no exceptional set or covering count. -/
theorem doubled_system_mass376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
          (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
            ‖primeFourier111 N α‖ ^ 2) ≤ C * (N : ℝ) ^ (98 / 100 : ℝ) := by
  sorry

/-- P0093 page 166 proof of Lemma 7. A finite cover bounds the integral
of a nonnegative function by the sum of its integrals on the covering
sets. The sets need not be disjoint. -/
theorem finite_cover_integral376 (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (S : Finset ℕ) (t : ℕ → Set ℝ)
    (hi : ∀ q ∈ S, IntegrableOn f (t q))
    (hcover : s ⊆ ⋃ q ∈ S, t q) :
    (∫ x in s, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
  classical
  have hUnion : (∫ x in ⋃ q ∈ S, t q, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
    clear hcover
    induction S using Finset.induction_on with
    | empty => simp
    | @insert q S hq ih =>
      have hiq := hi q (Finset.mem_insert_self q S)
      have hiS : ∀ i ∈ S, IntegrableOn f (t i) := fun i hi' => hi i (Finset.mem_insert_of_mem hi')
      have hiU : IntegrableOn f (⋃ i ∈ S, t i) := integrableOn_finset_iUnion.mpr hiS
      have hle := integral_mono_measure (Measure.restrict_union_le (μ := volume) (t q) (⋃ i ∈ S, t i))
        (ae_of_all _ hf) (integrable_add_measure.mpr ⟨hiq, hiU⟩)
      rw [integral_add_measure hiq hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert hq]
      exact hle.trans (add_le_add le_rfl (ih hiS))
  have hiU : IntegrableOn f (⋃ q ∈ S, t q) := integrableOn_finset_iUnion.mpr hi
  exact (setIntegral_mono_set hiU (ae_of_all _ hf) (ae_of_all _ hcover)).trans hUnion

/-- P0093 page 166 equation 9.3 before the T bound. Exact
exceptional_prime_mass357 statement. CONDITIONAL on the geometric cover
and the local doubled system prime mass estimate. -/
theorem exceptional_prime_mass_decomposed376 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨η, hη, hη1, A, hA, Na, ha⟩ := exceptional_system_cover376
  obtain ⟨C, hC, Nc, hc⟩ := doubled_system_mass376 hG
  refine ⟨η, hη, hη1, A * C, mul_pos hA hC, max 1 (max Na Nc), ?_⟩
  intro N hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨S, hS, hq, hcover⟩ := ha N hNa
  have hInt : IntegrableOn (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    ((continuous_prime_fourier111 N (by omega)).norm.pow 2).integrableOn_Icc
  have hb := finite_cover_integral376 (fun α => ‖primeFourier111 N α‖ ^ 2)
    (fun α => sq_nonneg _) (exceptionalArcs280 N η) S
    (fun q => arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1)
    (fun q _ => hInt.mono_set Set.inter_subset_right) hcover
  calc
    _ ≤ ∑ q ∈ S, ∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
        ‖primeFourier111 N α‖ ^ 2 := hb
    _ ≤ ∑ _q ∈ S, C * (N : ℝ) ^ (98 / 100 : ℝ) :=
      Finset.sum_le_sum (fun q hmem => hc N hNc q (hq q hmem).1 (hq q hmem).2)
    _ = (S.card : ℝ) * (C * (N : ℝ) ^ (98 / 100 : ℝ)) := by simp
    _ ≤ (A * (N : ℝ) ^ (1 / 100 : ℝ)) * (C * (N : ℝ) ^ (98 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = A * C * ((N : ℝ) ^ (1 / 100 : ℝ) * (N : ℝ) ^ (98 / 100 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; norm_num

end LeanLab.Linnik1951
