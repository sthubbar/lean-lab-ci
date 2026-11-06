import LeanLab.Ricci1937.Decomp338k

/-!
Ricci 1937, supply split for the first Z lower leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real Asymptotics
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Second memoir page 99 formula 18.3, page 111 formula 28.11
and page 112 formula 30.2, auxiliary positive main sum at the printed lower masses.
This concerns only finite density coefficients and contains no integer count. -/
theorem decomp338_greedy_main :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ a : ℝ, 0 < a ∧ ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t →
        a * (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) ≤
          ∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
            ∀ j ∈ range (t + 1),
              (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1),
            (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  exact decomp338_greedy_main_proved

/-- LEAF. Second memoir pages 113 and 114 formulas 31.3 to 31.5,
auxiliary saved support for the first pair on first memoir page 89.
This bounds only retained prime products and contains no integer count. -/
theorem decomp338_greedy_support :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / 7 < δ ∧ δ ≤ 1 / 2 ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_greedy_support_proved


/-- Auxiliary full pair density lower bound for first memoir page 88.
The exceptional prime two contributes exactly one half for an even gap. -/
lemma decomp338_full_pair_product_lower (h t : ℕ) (hh : Even h) (ht : 3 ≤ t) :
    exp (-52 : ℝ) / (2 * Real.log t ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN h p) := by
  let P := (Nat.primesLE t).erase 2
  have h2 : 2 ∈ Nat.primesLE t := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
  have hS : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ p ≤ t := by
    intro p hp
    obtain ⟨hp2, hp⟩ := mem_erase.mp hp
    obtain ⟨hpt, hprime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hprime, by have := hprime.two_le; omega, hpt⟩
  have hl := decompJ365_prime_product_lower t ht P hS
  have hprod : (∏ p ∈ P, (1 - (2 : ℝ) / p)) ≤ ∏ p ∈ P, (1 - nuN h p) := by
    apply prod_le_prod₀
    · intro p hp
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
      have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) < 3) hpR
      linarith
    · intro p hp
      rw [nuN_prime (hS p hp).1]
      have hpR : (0 : ℝ) ≤ p := by positivity
      have hi := div_le_div_of_nonneg_right (wt_le_two h p) hpR
      linarith
  have hnu2 : nuN h 2 = 1 / 2 := by
    rw [nuN_prime Nat.prime_two, wt]
    simp [even_iff_two_dvd.mp hh]
  rw [← mul_prod_erase (Nat.primesLE t) (fun p => 1 - nuN h p) h2, hnu2]
  change _ ≤ (1 - 1 / 2 : ℝ) * ∏ p ∈ P, (1 - nuN h p)
  have hm := mul_le_mul_of_nonneg_left (hl.trans hprod) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hm using 1 <;> ring

/-- Auxiliary saved level error bound for first memoir page 89.
The logarithmic factor spends only half of any supplied positive power saving. -/
lemma decomp338_level_error_upper (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ ξ : ℕ in atTop,
      (ξ : ℝ) ^ (1 - κ) * (1 + Real.log ((ξ : ℝ) ^ (1 - κ))) ^ 2 ≤
        (1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (1 - κ / 2) := by
  have hl : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x => x ^ (κ / 2)) := by
    simpa only [Real.rpow_two] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < κ / 2 by positivity)
  have hg : Tendsto (fun ξ : ℕ => Real.log (ξ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.natCast_atTop.def (by norm_num : (0 : ℝ) < 1),
    hg.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop 2] with ξ hlog hlarge hξ
  have hξR : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hlog0 : 0 ≤ Real.log ξ := by linarith
  have hlog' : Real.log ξ ^ 2 ≤ (ξ : ℝ) ^ (κ / 2) := by
    have hh : |Real.log ξ ^ 2| ≤ (ξ : ℝ) ^ (κ / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξR _), one_mul] using hlog
    exact (le_abs_self _).trans hh
  have hab : |1 + (1 - κ) * Real.log ξ| ≤ (1 + |1 - κ|) * Real.log ξ := by
    calc
      _ ≤ |(1 : ℝ)| + |(1 - κ) * Real.log ξ| := abs_add_le _ _
      _ = 1 + |1 - κ| * Real.log ξ := by rw [abs_mul, abs_one, abs_of_nonneg hlog0]
      _ ≤ _ := by nlinarith
  have hs : (1 + (1 - κ) * Real.log ξ) ^ 2 ≤
      (1 + |1 - κ|) ^ 2 * Real.log ξ ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hab
    nlinarith [sq_abs (1 + (1 - κ) * Real.log ξ)]
  rw [Real.log_rpow hξR]
  calc
    _ ≤ (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * Real.log ξ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hξR.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (κ / 2)) := by gcongr
    _ = _ := by
      rw [show (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (κ / 2)) =
        (1 + |1 - κ|) ^ 2 * ((ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2)) by ring,
        ← Real.rpow_add hξR]
      congr 2
      ring


/-- Auxiliary floor cutoff choice for the first pair on first memoir page 89.
An exponent strictly above one seventh gives both exact factor thresholds eventually. -/
lemma decomp338_floor_power_cutoff (δ : ℝ) (hδ : 1 / 7 < δ) (hδhalf : δ ≤ 1 / 2)
    (T : ℕ) :
    ∀ᶠ ξ : ℕ in atTop,
      let t := ⌊(ξ : ℝ) ^ δ⌋₊
      3 ≤ t ∧ T ≤ t ∧ t ≤ ξ ∧ (ξ : ℝ) < (t : ℝ) ^ (7 : ℕ) ∧
        (ξ : ℝ) ^ (1 / (7 : ℝ)) ≤ t := by
  have hd : 0 < δ := by linarith
  have hg := (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hb := (tendsto_rpow_atTop (show 0 < δ - 1 / 7 by linarith)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually (eventually_ge_atTop ((max T 3 : ℕ) : ℝ)),
    hb.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop 2] with ξ hbig hratio hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have htm : max T 3 ≤ t := Nat.le_floor hbig
  have hpow : (ξ : ℝ) ^ δ ≤ ξ := by
    calc _ ≤ (ξ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hξ1 (by linarith)
         _ = _ := Real.rpow_one _
  have htξR : (t : ℝ) ≤ ξ := (Nat.floor_le (by positivity)).trans hpow
  have hr1 : (1 : ℝ) ≤ (ξ : ℝ) ^ (1 / (7 : ℝ)) := Real.one_le_rpow hξ1 (by norm_num)
  have hprod : (ξ : ℝ) ^ δ = (ξ : ℝ) ^ (δ - 1 / 7) * (ξ : ℝ) ^ (1 / (7 : ℝ)) := by
    rw [← Real.rpow_add hξ0]
    congr 1
    ring
  have hfloor := Nat.sub_one_lt_floor ((ξ : ℝ) ^ δ)
  have hroot : (ξ : ℝ) ^ (1 / (7 : ℝ)) < t := by
    have hmul : 4 * (ξ : ℝ) ^ (1 / (7 : ℝ)) ≤ (ξ : ℝ) ^ δ := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    dsimp only [t]
    nlinarith
  have hroot7 : ((ξ : ℝ) ^ (1 / (7 : ℝ))) ^ (7 : ℕ) = ξ := by
    rw [← Real.rpow_mul_natCast hξ0.le]
    norm_num
  have hpower := pow_lt_pow_left₀ hroot (by positivity : (0 : ℝ) ≤ (ξ : ℝ) ^ (1 / (7 : ℝ)))
    (by norm_num : (7 : ℕ) ≠ 0)
  rw [hroot7] at hpower
  exact ⟨by omega, by omega, by exact_mod_cast htξR, hpower, hroot.le⟩

/-- The exact first Z lower leaf from its two proved supply pieces.
First memoir pages 75, 88 and 89. -/
theorem decomp338_Z_lower_6_6 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 6 6 m ξ := by
  intro m hm
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main
  obtain ⟨Y₂, hY₂, hsupp⟩ := decomp338_greedy_support
  let Y := max Y₁ Y₂
  obtain ⟨a, ha, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδ, hδhalf, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let b : ℝ := a * exp (-52 : ℝ) / 4
  have hb : 0 < b := by dsimp [b]; positivity
  apply decompJ365_lower_of_main_error hb (show 0 < κ / 2 by positivity) A
  have heven : Even (2 * m.natAbs) := ⟨m.natAbs, by omega⟩
  filter_upwards [decomp338_floor_power_cutoff δ hδ hδhalf T,
    decomp338_level_error_upper κ hκ, eventually_ge_atTop X,
    eventually_ge_atTop (max 3 (4 * m.natAbs))] with ξ hcut herr hX hξ
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let N := ξ + 1 - 2 * m.natAbs
  let L := (ξ : ℝ) ^ (1 - κ)
  let c := decomp338GreedyCutoff (2 * m.natAbs) Y t
  let U := (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1)
  let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (2 * m.natAbs) p
  have ht3 : 3 ≤ t := hcut.1
  have hξ3 : 3 ≤ ξ := by omega
  have hξR : (1 : ℝ) < ξ := by exact_mod_cast (by omega : 1 < ξ)
  have hL : 1 ≤ L := by
    have hh := hsupp ξ (2 * m.natAbs) hX ∅ (empty_subset _) (by simp)
    simpa [L] using hh
  have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L := by
    exact hsupp ξ (2 * m.natAbs) hX
  have hth : (ξ : ℝ) ^ (1 / ((6 : ℝ) + 1)) ≤ t := by
    convert hcut.2.2.2.2 using 1 <;> norm_num
  have hraw := decomp305_zCount_finite_lower 6 6 ξ N t m (by omega) (by dsimp [N]; omega)
    hcut.2.2.2.1 hcut.2.2.2.1 hth hth
    (range (t + 1)) c id L hL hlevel
  change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ zCount 6 6 m ξ at hraw
  have hprod := decomp338_full_pair_product_lower (2 * m.natAbs) t heven ht3
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξR
  have hlogle : Real.log t ≤ Real.log ξ := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
    (by exact_mod_cast hcut.2.2.1)
  have hprod' : exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p) := by
    apply le_trans _ hprod
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hE : a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤ E := by
    have hh := hmain (2 * m.natAbs) t heven hcut.2.1
    change a * (∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p)) ≤ E at hh
    calc
      _ = a * (exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by ring
      _ ≤ a * (∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p)) :=
        mul_le_mul_of_nonneg_left hprod' ha.le
      _ ≤ E := hh
  have hN : (ξ : ℝ) / 2 ≤ N := by
    have hn : ξ ≤ 2 * N := by dsimp [N]; omega
    have hnR : (ξ : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn
    linarith
  have hmainterm : b * ξ / Real.log ξ ^ 2 ≤ (N : ℝ) * E := by
    calc
      _ = ((ξ : ℝ) / 2) * (a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by dsimp [b]; ring
      _ ≤ (N : ℝ) * (a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by gcongr
      _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  change L * (1 + Real.log L) ^ 2 ≤ A * (ξ : ℝ) ^ (1 - κ / 2) at herr
  linarith

end
end LeanLab.Ricci1937
