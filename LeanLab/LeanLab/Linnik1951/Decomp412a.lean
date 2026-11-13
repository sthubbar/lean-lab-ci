/-
P0093 pages 162 to 165. Measure and local stability before interval packing.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Packing412
import LeanLab.Linnik1951.Shift412
import LeanLab.Linnik1951.Decomp412b

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- LEAF. P0093 page 162 Lemma 4 equation 7.6 and page 165 after
7.19. Choose eta small enough for exponent one two hundredth at level
two eta. Periodicity extends the unit interval bound to minus one through
two. This is only a measure estimate and contains no covering statement. -/
theorem large_value_measure412 :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        volume.real {α : ℝ | α ∈ Set.Icc (-1) 2 ∧
          (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ≤
            C * (N : ℝ) ^ ((1 / 200 : ℝ) - 1) := by
  exact large_value_measure_proved412

/-- LEAF. P0093 page 165 proof of Lemma 5, the two displays involving
xi and Delta. For a fixed positive eta, a shift of at most one over
N log N sends the eta large value set into the two eta large value set.
This is local stability only, without measure or cardinality estimates. -/
theorem large_value_stability412 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ α ξ : ℝ,
      |ξ| ≤ 1 / ((N : ℝ) * Real.log N) →
      (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖ →
      (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N (α + ξ)‖ := by
  exact large_value_stability_proved412 η hη

/-- P0093 page 165 proof of Lemma 5. A positive power absorbs log N.
This is the special case needed after dividing the measure by Delta. -/
theorem log_le_small_power412 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      Real.log N ≤ (N : ℝ) ^ (1 / 200 : ℝ) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 200)).def (by norm_num : (0 : ℝ) < 1)
  have hn := tendsto_natCast_atTop_atTop.eventually hh
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hn
  refine ⟨max 1 N0, ?_⟩
  intro N hN
  have h1 : 1 ≤ N := by have := le_max_left 1 N0; omega
  have hNN : N0 ≤ N := by have := le_max_right 1 N0; omega
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h1)
  simpa only [Real.rpow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hN0 N hNN

/-- P0093 page 165 Lemma 5 followed by the fixed eta choice in Section
8. Exact large_value_intervals376 statement, assembled from the smaller
measure and stability leaves and the finite grid packing theorem.
CONDITIONAL on large_value_measure412 and large_value_stability412. -/
theorem large_value_intervals_decomposed412 :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N → ∃ I : Finset (ℝ × ℝ),
        (I.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 100 : ℝ) ∧
        (∀ p ∈ I, p.2 - p.1 ≤ 1 / ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2) ∧
        {α : ℝ | α ∈ Set.Icc 0 1 ∧
          (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖} ⊆
          ⋃ p ∈ I, Set.Icc p.1 p.2 := by
  obtain ⟨η, hη, hηhalf, C, hC, Nm, hm⟩ := large_value_measure412
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
