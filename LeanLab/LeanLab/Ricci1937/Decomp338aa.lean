import LeanLab.Ricci1937.Decomp338w

/-!
Ricci 1937, the distinct first two mixed blocks for three and fifteen.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary two block greedy mass deficit for first memoir page 89 case four.
Second memoir page 115, the mixed variant of formulas 31.3 and 31.4.
The two actual endpoint deficits total at most four over the lower endpoint. -/
lemma decomp338_greedy_two_mass_lower (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (hstop : Y < decomp338GreedyCutoff h Y t 1) :
    1.46 - 4 / (decomp338GreedyCutoff h Y t 1 : ℝ) <
      ∑ p ∈ (Ioc (decomp338GreedyCutoff h Y t 1) t).filter Nat.Prime, nuN h p := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, htop⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  change Y < c 1 at hstop
  change ∀ i, Y ≤ c i at hlo
  change c 0 ≤ t at htop
  have h10 : c 1 ≤ c 0 := hc (by omega)
  have hfirst := decomp338_greedy_step_mass_lower h Y t 0 hYt (by change Y < c 0; omega)
  have hsecond := decomp338_greedy_step_mass_lower h Y (c 0) 1 (hlo 0) hstop
  have hsplit := sum_Ioc_consecutive (fun p => if p.Prime then nuN h p else 0) h10 htop
  rw [← sum_filter, ← sum_filter, ← sum_filter] at hsplit
  have hpos : (0 : ℝ) < c 1 := by exact_mod_cast (by have := hlo 1; omega : 0 < c 1)
  have hdiv : 2 / (c 0 : ℝ) ≤ 2 / (c 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hpos (by exact_mod_cast h10)
  norm_num only [decomp305HeadMass, Nat.cast_ofNat] at hfirst hsecond
  change (9 / 10 : ℝ) - 2 / (c 0 : ℝ) <
    ∑ p ∈ (Ioc (c 0) t).filter Nat.Prime, nuN h p at hfirst
  change (14 / 25 : ℝ) - 2 / (c 1 : ℝ) <
    ∑ p ∈ (Ioc (c 1) (c 0)).filter Nat.Prime, nuN h p at hsecond
  change 1.46 - 4 / (c 1 : ℝ) <
    ∑ p ∈ (Ioc (c 1) t).filter Nat.Prime, nuN h p
  have he : 4 / (c 1 : ℝ) = 2 / (c 1 : ℝ) + 2 / (c 1 : ℝ) := by ring
  rw [he]
  linarith

/-- Auxiliary second endpoint location for first memoir page 89 case four.
A high mass at most 1.40 cannot contain the first two target masses 1.46 above a residual cutoff one hundred.
Second memoir page 115 after formulas 31.3 and 31.4. -/
lemma decomp338_mixed_second_cutoff_le (h Y v t : ℕ) (hY : 100 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40) :
    decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 1 ≤ v := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 1
  change y ≤ v
  by_contra hnot
  have hvy : v < y := by omega
  have hyY : Y < y := hYv.trans_lt hvy
  have hlow := decomp338_greedy_two_mass_lower H Y t (by omega) (hYv.trans hvt) hyY
  have hupper : (∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p) ≤ 1.40 := by
    rw [decomp338_mixed_high_block h y t v t hvy.le le_rfl]
    apply le_trans _ hhigh
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hvy.trans (mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2⟩, hpprime⟩
    · intro p hp _
      positivity
  have hy100 : (100 : ℝ) ≤ y := by exact_mod_cast (by omega : 100 ≤ y)
  have hdiv : 4 / (y : ℝ) ≤ 0.04 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < y)).mpr
    linarith
  change 1.46 - 4 / (y : ℝ) < _ at hlow
  linarith

/-- Auxiliary actual shifted second endpoint power for first memoir page 89 case four.
Second memoir page 115 after formulas 31.3 and 31.4.
The cumulative lower mass is 1.46 and the logarithmic shift is retained. -/
lemma decomp338_mixed_second_power_max (h Y v t : ℕ) (hY : 100 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (ε ω : ℝ)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40)
    (hsmall : ∀ y : ℕ, Y ≤ y → 4 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε)
    (hshift : ω ≤ Real.log (Real.log t / Real.log v)) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 1 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-(1.46 + ω) / 2 + ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 1
  have hyY := (decomp338_greedy_cutoff_bounds H Y t (hYv.trans hvt)).2.1 1
  have hyv : y ≤ v := decomp338_mixed_second_cutoff_le h Y v t hY hYv hvt hhigh
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-(1.46 + ω) / 2 + ε))
  by_cases heq : y = Y
  · rw [heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by omega
    have hm := decomp338_greedy_two_mass_lower H Y t (by omega) (hYv.trans hvt) hyY'
    obtain ⟨herr1, herr2⟩ := hsmall y hyY
    have hlo : 1.46 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p := by linarith
    have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hlog : Real.log y ≤ Real.log v :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hyv)
    have hdiv : 14 / Real.log v ≤ 14 / Real.log y :=
      div_le_div_of_nonneg_left (by norm_num) hly hlog
    have hend : 28 / Real.log y + 14 / Real.log v ≤ ε := by
      have he : 28 / Real.log y + 14 / Real.log y = 42 / Real.log y := by ring
      linarith
    exact (decomp338_mixed_block_cutoff_upper h y v t t 1.46 ε ω
      (by omega) hyv hvt le_rfl hlo hend hshift).trans (le_max_right _ _)

end
end LeanLab.Ricci1937
