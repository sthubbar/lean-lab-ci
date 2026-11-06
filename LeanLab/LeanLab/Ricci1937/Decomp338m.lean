import LeanLab.Ricci1937.Decomp338l

/-!
Ricci 1937, nested floor cutoff thresholds.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary nested floor cutoff choice for first memoir page 89.
A strict exponent margin survives both natural floor operations. -/
lemma decomp338_nested_floor_cutoff (δ r γ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hγ : 0 < γ) (hgap : γ < δ * r) (K : ℕ) :
    ∀ᶠ ξ : ℕ in atTop,
      let t := ⌊(ξ : ℝ) ^ δ⌋₊
      let v := ⌊(t : ℝ) ^ r⌋₊
      K ≤ v ∧ v ≤ t ∧ t ≤ ξ ∧ (ξ : ℝ) ^ γ < v := by
  have hc : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop hδ).comp hc
  have hg := (tendsto_rpow_atTop hγ).comp hc
  have hd := (tendsto_rpow_atTop (show 0 < δ * r - γ by linarith)).comp hc
  filter_upwards [ht.eventually (eventually_ge_atTop (4 : ℝ)),
    hg.eventually (eventually_ge_atTop (K : ℝ)),
    hd.eventually (eventually_ge_atTop (8 : ℝ)), eventually_ge_atTop 2] with ξ ht4 hK hratio hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have ht4N : 4 ≤ t := Nat.le_floor ht4
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have htlower : (ξ : ℝ) ^ δ / 2 ≤ (t : ℝ) := by
    have hh := Nat.sub_one_lt_floor ((ξ : ℝ) ^ δ)
    change (ξ : ℝ) ^ δ - 1 < (t : ℝ) at hh
    linarith
  have htwo : (2 : ℝ) ^ r ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr1
  have hrpow := Real.rpow_le_rpow (show 0 ≤ (ξ : ℝ) ^ δ / 2 by positivity) htlower hr.le
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hξ0.le] at hrpow
  have hhalf : (ξ : ℝ) ^ (δ * r) / 2 ≤ (t : ℝ) ^ r := by
    apply le_trans _ hrpow
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
  have hroot1 : (1 : ℝ) ≤ (ξ : ℝ) ^ γ := Real.one_le_rpow hξ1 hγ.le
  have hprod : (ξ : ℝ) ^ (δ * r) = (ξ : ℝ) ^ (δ * r - γ) * (ξ : ℝ) ^ γ := by
    rw [← Real.rpow_add hξ0]
    congr 1
    ring
  have hmul : 8 * (ξ : ℝ) ^ γ ≤ (ξ : ℝ) ^ (δ * r) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right hratio (by positivity)
  have hvfloor := Nat.sub_one_lt_floor ((t : ℝ) ^ r)
  change (t : ℝ) ^ r - 1 < (v : ℝ) at hvfloor
  have hroot : (ξ : ℝ) ^ γ < (v : ℝ) := by nlinarith
  have hvtR : (v : ℝ) ≤ t := by
    calc
      _ ≤ (t : ℝ) ^ r := Nat.floor_le (by positivity)
      _ ≤ (t : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hr1
      _ = _ := Real.rpow_one _
  have htξR : (t : ℝ) ≤ ξ := by
    calc
      _ ≤ (ξ : ℝ) ^ δ := Nat.floor_le (by positivity)
      _ ≤ (ξ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hξ1 hδ1
      _ = _ := Real.rpow_one _
  exact ⟨by exact_mod_cast hK.trans hroot.le, by exact_mod_cast hvtR,
    by exact_mod_cast htξR, hroot⟩

/-- Auxiliary factor count size margin for first memoir page 89.
A strict prime threshold bound gives the exact next integer power bound. -/
lemma decomp338_size_of_root_lt (a ξ t : ℕ)
    (hr : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) < t) :
    (ξ : ℝ) < (t : ℝ) ^ (a + 1) := by
  have hh := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg ξ) (Nat.cast_nonneg t)
    (show 0 < (a : ℝ) + 1 by positivity)).mp (by simpa only [one_div] using hr)
  rw [show (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at hh
  exact hh

end
end LeanLab.Ricci1937
