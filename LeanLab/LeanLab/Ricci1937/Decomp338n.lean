import LeanLab.Ricci1937.Decomp338m
import LeanLab.Ricci1937.Decomp338t
import LeanLab.Ricci1937.Decomp338z
import LeanLab.Ricci1937.Decomp338ag

/-!
Ricci 1937, mixed pair supply pieces and assemblies.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. First memoir pages 75, 88 and 89, second memoir pages 106, 107 and 115.
Auxiliary finite mixed CRT Brun inequality for Z, with its actual count and explicit level error.
The density encoding is used only in the main coefficients. -/
theorem decomp338_mixed_z_finite (a b ξ N t v : ℕ) (m : ℤ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1)) (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap (2 * m.natAbs) v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by
  exact decomp338_mixed_z_finite_proved a b ξ N t v m hv hvt hN hsizeA hsizeB hthA hthB
    J cutoff level L hL hlevel

/-- LEAF. First memoir pages 88 and 89, second memoir pages 106, 107 and 115.
Auxiliary finite mixed CRT Brun inequality for W, with its actual count and explicit level error.
The density encoding is used only in the main coefficients. -/
theorem decomp338_mixed_w_finite (a b N t v : ℕ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap N v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  exact decomp338_mixed_w_finite_proved a b N t v hv hvt hthA hthB J cutoff level L hL hlevel

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case two, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 5 and 7 at omega equal to log of four thirds.
This bounds only retained prime products and contains no integer count. -/
theorem decomp338_mixed_support_5_7 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((5 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((7 : ℝ) + 1) < δ * (3 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (3 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_5_7_proved

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case three, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 4 and 9 at omega equal to log of two.
This bounds only retained prime products and contains no integer count. -/
theorem decomp338_mixed_support_4_9 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((4 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((9 : ℝ) + 1) < δ * (1 / 2 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 2 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_4_9_proved

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case four, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 3 and 15 at omega equal to log of four.
This bounds only retained prime products and contains no integer count. -/
theorem decomp338_mixed_support_3_15 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((3 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((15 : ℝ) + 1) < δ * (1 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_3_15_proved

/-- CONDITIONAL ON the supplied mixed saved support. The finite Z sieve is proved.
Auxiliary complete assembly of a mixed lower Z count, first memoir pages 75, 88 and 89. -/
lemma decomp338_mixed_Z_of_support (a b : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((a : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((b : ℝ) + 1) < δ * r ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ r⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ)) :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount a b m ξ := by
  intro m hm
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := hsupport
  let Y := max Y₁ Y₂
  obtain ⟨a₀, ha₀, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδA, hδhalf, hδB, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  have hδ : 0 < δ := lt_trans (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1)) hδA
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a₀ * exp (-52 : ℝ) / 4
  have hB : 0 < B := by dsimp [B]; positivity
  apply decompJ365_lower_of_main_error hB (show 0 < κ / 2 by positivity) A
  have hcutA := decomp338_nested_floor_cutoff δ 1 (1 / ((a : ℝ) + 1)) hδ (by linarith)
    (by norm_num) (by norm_num) (by positivity) (by simpa using hδA) (max T 3)
  have hcutB := decomp338_nested_floor_cutoff δ r (1 / ((b : ℝ) + 1)) hδ (by linarith)
    hr hr1 (by positivity) hδB 3
  filter_upwards [hcutA, hcutB, decomp338_level_error_upper κ hκ, eventually_ge_atTop X,
    eventually_ge_atTop (max 3 (4 * m.natAbs))] with ξ hA hBb herr hX hξ
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  let H := decomp338EncodedGap (2 * m.natAbs) v t
  let N := ξ + 1 - 2 * m.natAbs
  let L := (ξ : ℝ) ^ (1 - κ)
  let c := decomp338GreedyCutoff H Y t
  let U := (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
  let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p
  have htm : max T 3 ≤ t := by simpa only [Real.rpow_one, Nat.floor_natCast] using hA.1
  have hrootA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) < t := by
    simpa only [Real.rpow_one, Nat.floor_natCast] using hA.2.2.2
  have hrootB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) < v := hBb.2.2.2
  have hvt : v ≤ t := hBb.2.1
  have hv3 : 3 ≤ v := hBb.1
  have ht3 : 3 ≤ t := by omega
  have htξ : t ≤ ξ := hA.2.2.1
  have hξR : (1 : ℝ) < ξ := by exact_mod_cast (by omega : 1 < ξ)
  have heven : Even H := decomp338_encoded_gap_even (2 * m.natAbs) v t ⟨m.natAbs, by omega⟩
  have hL : 1 ≤ L := by
    have hh := hsupp ξ (2 * m.natAbs) hX ∅ (empty_subset _) (by simp)
    simpa [L] using hh
  have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
      (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
    hsupp ξ (2 * m.natAbs) hX
  have hraw := decomp338_mixed_z_finite a b ξ N t v m (by omega) hvt (by dsimp [N]; omega)
    (decomp338_size_of_root_lt a ξ t hrootA) (decomp338_size_of_root_lt b ξ v hrootB)
    hrootA.le hrootB.le (range (t + 1)) c id L hL hlevel
  change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ at hraw
  have hprod := decomp338_full_pair_product_lower H t heven ht3
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξR
  have hlogle : Real.log t ≤ Real.log ξ := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
    (by exact_mod_cast htξ)
  have hprod' : exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN H p) := by
    apply le_trans _ hprod
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hE : a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤ E := by
    have hh := hmain H t heven (by omega)
    change a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) ≤ E at hh
    calc
      _ = a₀ * (exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by ring
      _ ≤ a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) := mul_le_mul_of_nonneg_left hprod' ha₀.le
      _ ≤ E := hh
  have hN : (ξ : ℝ) / 2 ≤ N := by
    have hn : ξ ≤ 2 * N := by dsimp [N]; omega
    have hnR : (ξ : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn
    linarith
  have hmainterm : B * ξ / Real.log ξ ^ 2 ≤ (N : ℝ) * E := by
    calc
      _ = ((ξ : ℝ) / 2) * (a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by dsimp [B]; ring
      _ ≤ (N : ℝ) * (a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by gcongr
      _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  change L * (1 + Real.log L) ^ 2 ≤ A * (ξ : ℝ) ^ (1 - κ / 2) at herr
  linarith

/-- CONDITIONAL ON the supplied mixed saved support.
Auxiliary complete assembly of a mixed lower W count, first memoir pages 88 and 89. -/
lemma decomp338_mixed_W_of_support (a b : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((a : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((b : ℝ) + 1) < δ * r ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ r⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ)) :
    TheoremDW a b := by
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := hsupport
  let Y := max Y₁ Y₂
  obtain ⟨a₀, ha₀, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδA, hδhalf, hδB, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  have hδ : 0 < δ := lt_trans (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1)) hδA
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a₀ * exp (-52 : ℝ) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hcutA := decomp338_nested_floor_cutoff δ 1 (1 / ((a : ℝ) + 1)) hδ (by linarith)
    (by norm_num) (by norm_num) (by positivity) (by simpa using hδA) (max T 3)
  have hcutB := decomp338_nested_floor_cutoff δ r (1 / ((b : ℝ) + 1)) hδ (by linarith)
    hr hr1 (by positivity) hδB 3
  have hbound : ∀ᶠ N : ℕ in atTop, Even N →
      B * N / Real.log N ^ 2 - A * (N : ℝ) ^ (1 - κ / 2) ≤ wCount a b N := by
    filter_upwards [hcutA, hcutB, decomp338_level_error_upper κ hκ,
      eventually_ge_atTop X, eventually_ge_atTop 3] with N hA hBb herr hX hN
    intro hevenN
    let t := ⌊(N : ℝ) ^ δ⌋₊
    let v := ⌊(t : ℝ) ^ r⌋₊
    let H := decomp338EncodedGap N v t
    let L := (N : ℝ) ^ (1 - κ)
    let c := decomp338GreedyCutoff H Y t
    let U := (Nat.primesLE t).powerset.filter (fun S =>
      ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
    let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p
    have htm : max T 3 ≤ t := by simpa only [Real.rpow_one, Nat.floor_natCast] using hA.1
    have hrootA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) < t := by
      simpa only [Real.rpow_one, Nat.floor_natCast] using hA.2.2.2
    have hrootB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) < v := hBb.2.2.2
    have hvt : v ≤ t := hBb.2.1
    have hv3 : 3 ≤ v := hBb.1
    have ht3 : 3 ≤ t := by omega
    have htN : t ≤ N := hA.2.2.1
    have hNR : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have heven : Even H := decomp338_encoded_gap_even N v t hevenN
    have hL : 1 ≤ L := by
      have hh := hsupp N N hX ∅ (empty_subset _) (by simp)
      simpa [L] using hh
    have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
        (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
      hsupp N N hX
    have hraw := decomp338_mixed_w_finite a b N t v (by omega) hvt hrootA.le hrootB.le
      (range (t + 1)) c id L hL hlevel
    change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ wCount a b N at hraw
    have hprod := decomp338_full_pair_product_lower H t heven ht3
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have hlogN : 0 < Real.log N := Real.log_pos hNR
    have hlogle : Real.log t ≤ Real.log N := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
      (by exact_mod_cast htN)
    have hprod' : exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤
        ∏ p ∈ Nat.primesLE t, (1 - nuN H p) := by
      apply le_trans _ hprod
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hE : a₀ * exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤ E := by
      have hh := hmain H t heven (by omega)
      change a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) ≤ E at hh
      calc
        _ = a₀ * (exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by ring
        _ ≤ a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) := mul_le_mul_of_nonneg_left hprod' ha₀.le
        _ ≤ E := hh
    have hmainterm : B * N / Real.log N ^ 2 ≤ (N : ℝ) * E := by
      calc
        _ = (N : ℝ) * (a₀ * exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by dsimp [B]; ring
        _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    change L * (1 + Real.log L) ^ 2 ≤ A * (N : ℝ) ^ (1 - κ / 2) at herr
    linarith
  have hfinal : ∀ᶠ N : ℕ in atTop, Even N → (B / 2) * N / Real.log N ^ 2 ≤ wCount a b N := by
    filter_upwards [hbound, decompJ365_power_error_absorb (show 0 < κ / 2 by positivity) hB A]
      with N hN herr
    intro heven
    have hh := hN heven
    have heq : B * N / Real.log N ^ 2 = 2 * ((B / 2) * N / Real.log N ^ 2) := by ring
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfinal
  exact ⟨B / 2, by positivity, N₀, fun N hN heven => hN₀ N hN heven⟩

/-- Clean supplier from the proved finite Z sieve and shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/
theorem decomp338_Z_lower_5_7 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 5 7 m ξ := by
  exact decomp338_mixed_Z_of_support 5 7 (3 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_5_7

/-- Clean supplier from the proved finite W sieve and shifted support.
Exact W leaf assembly from first memoir page 89. -/
theorem decomp338_W_5_7 : TheoremDW 5 7 := by
  exact decomp338_mixed_W_of_support 5 7 (3 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_5_7

/-- Clean supplier from the proved finite Z sieve and shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/
theorem decomp338_Z_lower_4_9 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 4 9 m ξ := by
  exact decomp338_mixed_Z_of_support 4 9 (1 / 2 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_4_9

/-- Clean supplier from the proved finite W sieve and shifted support.
Exact W leaf assembly from first memoir page 89. -/
theorem decomp338_W_4_9 : TheoremDW 4 9 := by
  exact decomp338_mixed_W_of_support 4 9 (1 / 2 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_4_9

/-- Clean supplier from the proved finite sieve and distinct shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/
theorem decomp338_Z_lower_3_15 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 3 15 m ξ := by
  exact decomp338_mixed_Z_of_support 3 15 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_3_15

/-- Clean supplier from the proved finite sieve and distinct shifted support.
Exact W leaf assembly from first memoir page 89. -/
theorem decomp338_W_3_15 : TheoremDW 3 15 := by
  exact decomp338_mixed_W_of_support 3 15 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_3_15

end
end LeanLab.Ricci1937
