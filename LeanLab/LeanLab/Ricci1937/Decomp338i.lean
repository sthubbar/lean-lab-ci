import LeanLab.Ricci1937.Decomp338g

/-!
Ricci 1937, greedy endpoint support preparation.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The printed lower masses are all at least one half, first memoir page 89. -/
lemma decomp338_head_mass_ge_half (i : ℕ) : (1 / 2 : ℝ) ≤ (decomp305HeadMass i : ℝ) / 100 := by
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  · norm_num [decomp305HeadMass]

/-- Auxiliary strict greedy descent for second memoir pages 109 to 111.
Above a residual endpoint at least four, the next greedy endpoint strictly decreases. -/
lemma decomp338_greedy_step_lt (h Y w i : ℕ) (hY : 4 ≤ Y) (hYw : Y < w) :
    decomp338GreedyStep h Y w i < w := by
  have hw0 : 0 < w := by omega
  have hset : Ioc (w - 1) w = ({w} : Finset ℕ) := by
    ext p
    simp only [mem_Ioc, mem_singleton]
    omega
  have hmass : (∑ p ∈ (Ioc (w - 1) w).filter Nat.Prime, nuN h p) ≤
      (decomp305HeadMass i : ℝ) / 100 := by
    apply le_trans _ (decomp338_head_mass_ge_half i)
    rw [hset]
    by_cases hp : w.Prime
    · simp only [filter_singleton, hp, ite_true, sum_singleton]
      rw [nuN_prime hp]
      have hwR : (4 : ℝ) ≤ w := by exact_mod_cast (by omega : 4 ≤ w)
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < w)]
      linarith [wt_le_two h w]
    · simp [filter_singleton, hp]
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, by omega, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  have hh := Nat.find_min' hex (show Y ≤ w - 1 ∧ w - 1 ≤ w ∧
      (∑ p ∈ (Ioc (w - 1) w).filter Nat.Prime, nuN h p) ≤
        (decomp305HeadMass i : ℝ) / 100 from ⟨by omega, by omega, hmass⟩)
  omega

/-- Auxiliary termination of the canonical greedy cutoffs for second memoir pages 109 to 111.
Depth t has reached the fixed residual endpoint when the top is t. -/
lemma decomp338_greedy_stops (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t) :
    decomp338GreedyCutoff h Y t t = Y := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  have hbound (i : ℕ) : c i ≤ max Y (t - i) := by
    induction i with
    | zero => exact hw.trans (le_max_right _ _)
    | succ i ih =>
      by_cases hci : c i ≤ Y
      · exact (hc (by omega : i ≤ i + 1)).trans (hci.trans (le_max_left _ _))
      · have hnext : c (i + 1) < c i := decomp338_greedy_step_lt h Y (c i) (i + 1) hY (by omega)
        have hprev : c i ≤ t - i := by omega
        have hh : c (i + 1) ≤ t - (i + 1) := by omega
        exact hh.trans (le_max_right _ _)
  have hh := hbound t
  simp only [Nat.sub_self, max_eq_left (Nat.zero_le Y)] at hh
  exact Nat.le_antisymm hh (hlo t)

/-- Auxiliary uniform endpoint error threshold for second memoir page 109.
Both the greedy mass deficit and the logarithmic endpoint loss are arbitrarily small above one threshold. -/
lemma decomp338_endpoint_error_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℕ, 4 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε := by
  have hcast : Tendsto (fun y : ℕ => (y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun y : ℕ => (y : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
  have h2 : Tendsto (fun y : ℕ => 2 / (y : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 2
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hloginv : Tendsto (fun y : ℕ => (Real.log (y : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h28 : Tendsto (fun y : ℕ => 28 / Real.log y) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hloginv.const_mul 28
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (((h2.eventually (eventually_lt_nhds hε)).and
      (h28.eventually (eventually_lt_nhds hε))).and (eventually_ge_atTop 4))
  exact ⟨Y, (hY Y le_rfl).2, fun y hy => ⟨(hY y hy).1.1.le, (hY y hy).1.2.le⟩⟩

/-- Auxiliary endpoint power bound for second memoir page 109 and pages 113 to 114.
Each greedy step lies below the larger of the residual endpoint and its prescribed cutoff power. -/
lemma decomp338_greedy_step_power_max (h Y w i : ℕ) (hY : 4 ≤ Y) (hYw : Y ≤ w)
    (ε : ℝ) (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε) :
    (decomp338GreedyStep h Y w i : ℝ) ≤
      max (Y : ℝ) ((w : ℝ) ^ exp (-(decomp305HeadMass i : ℝ) / 100 / 2 + ε)) := by
  let y := decomp338GreedyStep h Y w i
  obtain ⟨hyY, hyw, hmass⟩ := decomp338_greedy_step_bounds h Y w i hYw
  by_cases heq : y = Y
  · rw [show decomp338GreedyStep h Y w i = Y from heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by dsimp [y] at *; omega
    have hm := decomp338_greedy_step_mass_lower h Y w i hYw hyY'
    have herrors := hsmall y hyY
    have hlow : (decomp305HeadMass i : ℝ) / 100 - ε ≤
        ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by
      change (decomp305HeadMass i : ℝ) / 100 - 2 / (y : ℝ) < _ at hm
      linarith
    have hp := decompJ365_pair_block_cutoff_upper h y w
      ((decomp305HeadMass i : ℝ) / 100) ε (by omega) hyw hlow herrors.2
    have he : -((decomp305HeadMass i : ℝ) / 100) / 2 + ε =
        -(decomp305HeadMass i : ℝ) / 100 / 2 + ε := by ring
    rw [he] at hp
    exact hp.trans (le_max_right _ _)

end
end LeanLab.Ricci1937
