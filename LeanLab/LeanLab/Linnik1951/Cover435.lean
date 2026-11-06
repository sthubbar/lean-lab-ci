/-
P0093 pages 165 and 166. Reconnect the refined entropy supply to prime mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Measure435
import LeanLab.Linnik1951.Decomp435b
import LeanLab.Linnik1951.Decomp376c

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 166 Lemma 6 applied to the interval cover from Lemma 5.
Exact exceptional_system_cover376 statement from the proved interval cover.
The finite image cannot increase the cover count. -/
theorem exceptional_system_cover435 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ S : Finset ℕ,
        (S.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ q ∈ S, (N : ℝ) ^ (1 / 10 : ℝ) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) ∧
        exceptionalArcs280 N η ⊆
          ⋃ q ∈ S, arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1 := by
  classical
  obtain ⟨η, hη, hη1, A, hA, N0, hI⟩ := large_value_intervals435
  refine ⟨η, hη, hη1, A, hA, max 1 N0, ?_⟩
  intro N hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hτ : 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  obtain ⟨I, hcard, hlen, hcover⟩ := hI N hN0
  let Q := (N : ℝ) ^ (1 / 10 : ℝ)
  let τ := (N : ℝ) ^ (1 / 7 : ℝ)
  let J := I.filter fun p => (Set.Icc p.1 p.2 ∩ minorArcs111 Q τ).Nonempty
  have hex (p : {p // p ∈ J}) : ∃ q : ℕ, Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      Set.Icc p.val.1 p.val.2 ∩ minorArcs111 Q τ ⊆ arcSystem111 q τ := by
    have hp := Finset.mem_filter.mp p.property
    exact interval_system_bounded376 Q τ p.val.1 p.val.2 hτ (hlen _ hp.1) hp.2
  choose q hq using hex
  let S : Finset ℕ := Finset.univ.image q
  refine ⟨S, ?_, ?_, ?_⟩
  · have hSJ : S.card ≤ J.card := by
      calc
        _ ≤ (Finset.univ : Finset {p // p ∈ J}).card := Finset.card_image_le
        _ = J.card := by simp
    have hJI : J.card ≤ I.card := Finset.card_filter_le _ _
    have hS := hSJ.trans hJI
    exact (show (S.card : ℝ) ≤ I.card by exact_mod_cast hS).trans hcard
  · intro d hd
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨(hq p).1, (hq p).2.1⟩
  · intro α hα
    have hlarge : α ∈ {α : ℝ | α ∈ Set.Icc 0 1 ∧
        (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} := ⟨hα.1, hα.2.2⟩
    obtain ⟨p, hp, hαp⟩ := Set.mem_iUnion₂.mp (hcover hlarge)
    have hm := exceptional_subset_minor376 N η hα
    have hpJ : p ∈ J := Finset.mem_filter.mpr ⟨hp, α, hαp, hm⟩
    let pJ : {p // p ∈ J} := ⟨p, hpJ⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨q pJ, Finset.mem_image.mpr ⟨pJ, Finset.mem_univ _, rfl⟩, ?_⟩
    exact ⟨(hq pJ).2.2 ⟨hαp, hm⟩, hα.1⟩


/-- P0093 page 166 equation 9.3 before the T bound. Exact
exceptional_prime_mass357 statement. CONDITIONAL on the refined geometric cover
and the explicit local doubled system expansion. -/
theorem exceptional_prime_mass435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨η, hη, hη1, A, hA, Na, ha⟩ := exceptional_system_cover435
  obtain ⟨C, hC, Nc, hc⟩ := doubled_system_mass_decomposed435 hG
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
