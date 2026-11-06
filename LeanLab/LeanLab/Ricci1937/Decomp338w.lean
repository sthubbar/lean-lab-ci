import LeanLab.Ricci1937.Decomp338v
import LeanLab.Ricci1937.Decomp338m

/-!
Ricci 1937, high mass control for the first two mixed pairs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary numerical margin for the high prime mass.
First memoir page 89 cases two and three. -/
lemma decomp338_log_twenty_ninths : Real.log (20 / 9 : ℝ) ≤ 0.8 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 20 / 9)).mpr
  exact ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])

/-- Auxiliary eventual high mass and exact logarithmic shift for a floored mixed cutoff.
First memoir page 89 cases two and three and second memoir page 115 after 31.3 and 31.4.
Ratios above 0.45 put the entire high mass strictly below the first target 0.90. -/
lemma decomp338_mixed_high_mass_eventually (r : ℝ) (hr : 0.45 < r) (hr1 : r ≤ 1) :
    ∀ᶠ t : ℕ in atTop,
      let v := ⌊(t : ℝ) ^ r⌋₊
      2 ≤ v ∧ v ≤ t ∧
        (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.85 ∧
        -Real.log r ≤ Real.log (Real.log t / Real.log v) := by
  have hloggrowth : Tendsto (fun v : ℕ => Real.log (v : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hloggrowth.eventually (eventually_ge_atTop (280 : ℝ)))
  have hfloor := decomp338_nested_floor_cutoff 1 r 0.45 (by norm_num) le_rfl
    (by linarith) hr1 (by norm_num) (by simpa using hr) (max K 2)
  filter_upwards [hfloor, eventually_ge_atTop 2] with t ht ht2
  simp only [Real.rpow_one, Nat.floor_natCast] at ht
  dsimp only
  let v := ⌊(t : ℝ) ^ r⌋₊
  obtain ⟨hKv, hvt, _, hroot⟩ := ht
  have hv2 : 2 ≤ v := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlow : 0.45 * Real.log t ≤ Real.log v := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hroot.le
    rwa [Real.log_rpow ht0] at hh
  have hquot : Real.log t / Real.log v ≤ (20 / 9 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    linarith
  have hratio := Real.log_le_log (div_pos hlt hlv) hquot
  have herr : 14 / Real.log v ≤ (0.05 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    have hh := hK v (by omega)
    linarith
  have hmass := decompJ365_prime_block_upper v t hv2 hvt
  have hmass' : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.85 := by
    linarith [decomp338_log_twenty_ninths]
  have hvfloor : (v : ℝ) ≤ (t : ℝ) ^ r := Nat.floor_le (by positivity)
  have hlogupper := Real.log_le_log (by exact_mod_cast (by omega : 0 < v)) hvfloor
  rw [Real.log_rpow ht0] at hlogupper
  have hr0 : 0 < r := by linarith
  have hquotlow : 1 / r ≤ Real.log t / Real.log v := by
    apply (le_div_iff₀ hlv).mpr
    have hh : Real.log v / r ≤ Real.log t := (div_le_iff₀ hr0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  have hshift := Real.log_le_log (by positivity : (0 : ℝ) < 1 / r) hquotlow
  rw [Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub] at hshift
  exact ⟨hv2, hvt, hmass', hshift⟩

/-- Auxiliary eventual first endpoint location for the first two mixed pairs.
First memoir page 89 cases two and three, second memoir page 115 after 31.3 and 31.4. -/
lemma decomp338_mixed_first_cutoff_eventually (r : ℝ) (hr : 0.45 < r) (hr1 : r ≤ 1) :
    ∀ᶠ t : ℕ in atTop, ∀ h Y : ℕ,
      Y ≤ ⌊(t : ℝ) ^ r⌋₊ →
        decomp338GreedyCutoff (decomp338EncodedGap h ⌊(t : ℝ) ^ r⌋₊ t) Y t 0 ≤
          ⌊(t : ℝ) ^ r⌋₊ := by
  filter_upwards [decomp338_mixed_high_mass_eventually r hr hr1] with t ht
  intro h Y hYv
  exact decomp338_mixed_first_cutoff_le h Y _ t hYv ht.2.1 (by linarith [ht.2.2.1])

end
end LeanLab.Ricci1937
