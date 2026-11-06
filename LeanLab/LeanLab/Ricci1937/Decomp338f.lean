import LeanLab.Ricci1937.Decomp338h
import LeanLab.Ricci1937.Decomp338e

/-!
Ricci 1937, canonical greedy block limits.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary endpoint limit for second memoir pages 109 to 111.
For any varying gaps, a bounded mass greedy endpoint tends to infinity with its top endpoint. -/
lemma decomp338_greedy_step_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop) (Y i : ℕ) :
    Tendsto (fun q => decomp338GreedyStep (h q) Y (w q) i) atTop atTop := by
  apply tendsto_atTop.2
  intro Z
  obtain ⟨W, hW, hmass⟩ := decompJ365_pair_block_mass_unbounded (max Y Z)
    ((decomp305HeadMass i : ℝ) / 100 + 1)
  filter_upwards [hw.eventually (eventually_ge_atTop W)] with q hq
  have hYw : Y ≤ w q := (le_max_left Y Z).trans (hW.trans hq)
  obtain ⟨hlo, hhi, hsmall⟩ := decomp338_greedy_step_bounds (h q) Y (w q) i hYw
  by_contra hbad
  have hZ : decomp338GreedyStep (h q) Y (w q) i ≤ max Y Z := by omega
  have hsub : (Ioc (max Y Z) (w q)).filter Nat.Prime ⊆
      (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hZ.trans_lt (mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2⟩, hpP⟩
  have hle := sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => nuN_nonneg (h q) p)
  have hbig := hmass (h q) (w q) hq
  linarith

/-- Auxiliary canonical cutoff limits for second memoir pages 109 to 111.
Every fixed greedy cutoff depth tends to infinity with the top endpoint, uniformly in varying gaps. -/
lemma decomp338_greedy_cutoff_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) : Tendsto (fun q => decomp338GreedyCutoff (h q) Y (w q) i) atTop atTop := by
  induction i with
  | zero => exact decomp338_greedy_step_tendsto h w hw Y 0
  | succ i ih =>
    exact decomp338_greedy_step_tendsto h
      (fun q => decomp338GreedyCutoff (h q) Y (w q) i) ih Y (i + 1)

/-- Auxiliary sharp greedy mass deficit for second memoir pages 109 to 111.
At an endpoint strictly above the residual cutoff, the missing mass is less than two over that endpoint. -/
lemma decomp338_greedy_step_mass_lower (h Y w i : ℕ) (hYw : Y ≤ w)
    (hstop : Y < decomp338GreedyStep h Y w i) :
    (decomp305HeadMass i : ℝ) / 100 - 2 / (decomp338GreedyStep h Y w i : ℝ) <
      ∑ p ∈ (Ioc (decomp338GreedyStep h Y w i) w).filter Nat.Prime, nuN h p := by
  let y := decomp338GreedyStep h Y w i
  have hex : ∃ z : ℕ, Y ≤ z ∧ z ≤ w ∧
      (∑ p ∈ (Ioc z w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, hYw, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  have hy : y = Nat.find hex := by simp only [y, decomp338GreedyStep, dif_pos hex]
  have hyw : y ≤ w := (decomp338_greedy_step_bounds h Y w i hYw).2.1
  have hy0 : 0 < y := by dsimp [y]; omega
  have hprev : (decomp305HeadMass i : ℝ) / 100 <
      ∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p := by
    have hmin := Nat.find_min hex (show y - 1 < Nat.find hex by rw [← hy]; omega)
    apply lt_of_not_ge
    intro hle
    exact hmin ⟨by dsimp [y] at *; omega, by omega, hle⟩
  have hsets : Ioc (y - 1) w = insert y (Ioc y w) := by
    ext p
    simp only [mem_Ioc, mem_insert]
    omega
  have hstep : (∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p) ≤
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) + 2 / (y : ℝ) := by
    rw [hsets, filter_insert]
    by_cases hp : y.Prime
    · rw [ite_eq_left hp, sum_insert (by simp)]
      rw [nuN_prime hp]
      have hh := div_le_div_of_nonneg_right (wt_le_two h y) (by positivity : (0 : ℝ) ≤ y)
      linarith
    · rw [ite_eq_right hp]
      exact le_add_of_nonneg_right (by positivity)
  change (decomp305HeadMass i : ℝ) / 100 - 2 / (y : ℝ) < _
  linarith


/-- Auxiliary total endpoint monotonicity for second memoir pages 109 to 111.
The fallback also stays below the supplied top endpoint. -/
lemma decomp338_greedy_step_le (h Y w i : ℕ) : decomp338GreedyStep h Y w i ≤ w := by
  unfold decomp338GreedyStep
  split_ifs with H
  · exact (Nat.find_spec H).2.1
  · rfl

/-- Auxiliary canonical greedy block mass limit for second memoir page 111 formula 28.8.
The exact endpoint deficit tends to zero with the greedy endpoint. -/
lemma decomp338_greedy_step_mass_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime,
      nuN (h q) p) atTop (nhds ((decomp305HeadMass i : ℝ) / 100)) := by
  let y := fun q => decomp338GreedyStep (h q) Y (w q) i
  have hy : Tendsto y atTop atTop := decomp338_greedy_step_tendsto h w hw Y i
  have hyR : Tendsto (fun q => (y q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hy
  have hinv : Tendsto (fun q => (y q : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hyR
  have herr : Tendsto (fun q => 2 / (y q : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub herr) tendsto_const_nhds
  · filter_upwards [hw.eventually (eventually_ge_atTop Y),
      hy.eventually (eventually_ge_atTop (Y + 1))] with q hwq hyq
    change Y + 1 ≤ decomp338GreedyStep (h q) Y (w q) i at hyq
    exact (decomp338_greedy_step_mass_lower (h q) Y (w q) i hwq (by omega)).le
  · filter_upwards [hw.eventually (eventually_ge_atTop Y)] with q hwq
    exact (decomp338_greedy_step_bounds (h q) Y (w q) i hwq).2.2

/-- Auxiliary canonical greedy square mass limit for second memoir page 111 formula 28.9.
A vanishing maximal density and bounded total mass force the square mass to vanish. -/
lemma decomp338_greedy_step_square_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime,
      (nuN (h q) p) ^ 2) atTop (nhds 0) := by
  let y := fun q => decomp338GreedyStep (h q) Y (w q) i
  have hy : Tendsto y atTop atTop := decomp338_greedy_step_tendsto h w hw Y i
  have hyR : Tendsto (fun q => (y q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hy
  have hinv : Tendsto (fun q => (y q : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hyR
  have hbound : Tendsto (fun q => 2 / (y q : ℝ) * ((decomp305HeadMass i : ℝ) / 100))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hinv.const_mul 2).mul_const ((decomp305HeadMass i : ℝ) / 100)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall fun q => sum_nonneg (fun p _ => sq_nonneg _)
  · filter_upwards [hw.eventually (eventually_ge_atTop Y),
      hy.eventually (eventually_ge_atTop 1)] with q hwq hyq
    have hupper := decompJ365_pair_block_square_upper (h q) (y q) (w q) (by omega)
    exact hupper.trans (mul_le_mul_of_nonneg_left
      (decomp338_greedy_step_bounds (h q) Y (w q) i hwq).2.2 (by positivity))

/-- Auxiliary canonical greedy moments for second memoir page 111 formulas 28.8 and 28.9.
At every fixed depth the actual greedy blocks have the printed mass and zero square mass in the limit. -/
lemma decomp338_greedy_block_moments (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop) (Y : ℕ) :
    (∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (decomp338GreedyCutoff (h q) Y (w q)) i,
        nuN (h q) p) atTop (nhds ((decomp305HeadMass i : ℝ) / 100))) ∧
    (∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (decomp338GreedyCutoff (h q) Y (w q)) i,
        (nuN (h q) p) ^ 2) atTop (nhds 0)) := by
  constructor
  · intro i
    cases i with
    | zero => exact decomp338_greedy_step_mass_tendsto h w hw Y 0
    | succ i =>
      exact decomp338_greedy_step_mass_tendsto h
        (fun q => decomp338GreedyCutoff (h q) Y (w q) i)
        (decomp338_greedy_cutoff_tendsto h w hw Y i) Y (i + 1)
  · intro i
    cases i with
    | zero => exact decomp338_greedy_step_square_tendsto h w hw Y 0
    | succ i =>
      exact decomp338_greedy_step_square_tendsto h
        (fun q => decomp338GreedyCutoff (h q) Y (w q) i)
        (decomp338_greedy_cutoff_tendsto h w hw Y i) Y (i + 1)


/-- Auxiliary canonical normalized head for second memoir pages 99 and 111.
For every varying even gap and every top endpoint tending to infinity, the actual
greedy twenty block head divided by its density product is eventually above 0.04. -/
lemma decomp338_greedy_normalized_head (h w : ℕ → ℕ) (heven : ∀ q, Even (h q))
    (hw : Tendsto w atTop atTop) (Y : ℕ) :
    ∀ᶠ q : ℕ in atTop, (0.04 : ℝ) <
      (∑ S ∈ decomp305PrimeFamily (w q) (decomp338GreedyCutoff (h q) Y (w q)) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) /
      (∏ p ∈ (Ioc (decomp338GreedyCutoff (h q) Y (w q) 19) (w q)).filter Nat.Prime,
        (1 - nuN (h q) p)) := by
  let c := fun q => decomp338GreedyCutoff (h q) Y (w q)
  have hc : ∀ q, Antitone (c q) := by
    intro q
    apply antitone_nat_of_succ_le
    intro i
    exact decomp338_greedy_step_le (h q) Y (c q i) (i + 1)
  have hcw : ∀ q, c q 0 ≤ w q := fun q => decomp338_greedy_step_le (h q) Y (w q) 0
  obtain ⟨ht, hsq⟩ := decomp338_greedy_block_moments h w hw Y
  exact decomp338_normalized_head_of_moments h w c heven hc hcw ht hsq

end
end LeanLab.Ricci1937
