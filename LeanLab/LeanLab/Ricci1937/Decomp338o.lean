import LeanLab.Ricci1937.Decomp338c

/-!
Ricci 1937, complete first pair supply.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact W six and six leaf from first memoir pages 88 and 89.
The uniform greedy main sum and saved support are both supplied with clean proofs. -/
theorem decomp338_W_6_6 : TheoremDW 6 6 := by
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := decomp338_greedy_support_proved
  let Y := max Y₁ Y₂
  obtain ⟨a, ha, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδ, hδhalf, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a * exp (-52 : ℝ) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ᶠ N : ℕ in atTop, Even N →
      B * N / Real.log N ^ 2 - A * (N : ℝ) ^ (1 - κ / 2) ≤ wCount 6 6 N := by
    filter_upwards [decomp338_floor_power_cutoff δ hδ hδhalf T,
      decomp338_level_error_upper κ hκ, eventually_ge_atTop X, eventually_ge_atTop 3]
      with N hcut herr hX hN
    intro heven
    let t := ⌊(N : ℝ) ^ δ⌋₊
    let L := (N : ℝ) ^ (1 - κ)
    let c := decomp338GreedyCutoff N Y t
    let U := (Nat.primesLE t).powerset.filter (fun S =>
      ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
    let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN N p
    have ht3 : 3 ≤ t := hcut.1
    have hNR : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hL : 1 ≤ L := by
      have hh := hsupp N N hX ∅ (empty_subset _) (by simp)
      simpa [L] using hh
    have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
        (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
      hsupp N N hX
    have hth : (N : ℝ) ^ (1 / ((6 : ℝ) + 1)) ≤ t := by
      convert hcut.2.2.2.2 using 1 <;> norm_num
    have hraw := decomp305_wCount_finite_lower 6 6 N t (by omega) hth hth
      (range (t + 1)) c id L hL hlevel
    change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ wCount 6 6 N at hraw
    have hprod := decomp338_full_pair_product_lower N t heven ht3
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have hlogN : 0 < Real.log N := Real.log_pos hNR
    have hlogle : Real.log t ≤ Real.log N := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
      (by exact_mod_cast hcut.2.2.1)
    have hprod' : exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤
        ∏ p ∈ Nat.primesLE t, (1 - nuN N p) := by
      apply le_trans _ hprod
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hE : a * exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤ E := by
      have hh := hmain N t heven hcut.2.1
      change a * (∏ p ∈ Nat.primesLE t, (1 - nuN N p)) ≤ E at hh
      calc
        _ = a * (exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by ring
        _ ≤ a * (∏ p ∈ Nat.primesLE t, (1 - nuN N p)) := mul_le_mul_of_nonneg_left hprod' ha.le
        _ ≤ E := hh
    have hmainterm : B * N / Real.log N ^ 2 ≤ (N : ℝ) * E := by
      calc
        _ = (N : ℝ) * (a * exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by dsimp [B]; ring
        _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    change L * (1 + Real.log L) ^ 2 ≤ A * (N : ℝ) ^ (1 - κ / 2) at herr
    linarith
  have hfinal : ∀ᶠ N : ℕ in atTop, Even N → (B / 2) * N / Real.log N ^ 2 ≤ wCount 6 6 N := by
    filter_upwards [hbound, decompJ365_power_error_absorb (show 0 < κ / 2 by positivity) hB A]
      with N hN herr
    intro heven
    have hh := hN heven
    have heq : B * N / Real.log N ^ 2 = 2 * ((B / 2) * N / Real.log N ^ 2) := by ring
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfinal
  exact ⟨B / 2, by positivity, N₀, fun N hN heven => hN₀ N hN heven⟩

/-- The exact Z six and six half of first memoir page 75.
This combines the supplied lower leaf with the existing proved upper count. -/
theorem decomp338_Z_6_6 : TheoremDZ 6 6 := by
  exact decompJ365_Z_of_lower decomp338_Z_lower_6_6

/-- The full six and six pair of first memoir Theorem D, page 75.
The other four printed pairs are separate targets. -/
theorem decomp338_D_6_6 : TheoremD 6 6 := by
  exact ⟨decomp338_Z_6_6, decomp338_W_6_6⟩

end
end LeanLab.Ricci1937
