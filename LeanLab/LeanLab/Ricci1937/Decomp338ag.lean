import LeanLab.Ricci1937.Decomp338af

/-!
Ricci 1937, saved support supplier for the three and fifteen pair.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Clean supplier of the distinct shifted support for three and fifteen.
First memoir page 89 case four, the tau bar display, and second memoir page 115 after 31.3 and 31.4. -/
theorem decomp338_mixed_support_3_15_proved :
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
  let r : ℝ := 1 / 4
  let τ := exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) *
    (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))
  obtain ⟨ε, α, hε0, hε, hα0, hαpos, hαmono, hαsum, hα1, hα2, htail⟩ :=
    decomp338_case_four_support_profile 0.001 (by norm_num)
  have hrec := decomp338_case_four_profile_recurrence ε α hα2 htail
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ₀, κ, hδ₀, hκ, hδA₀, hδB₀, hsave₀⟩ := hm.2.2.2
  let δ := min δ₀ (1 / 2)
  have hδA : (1 / 4 : ℝ) < δ := lt_min hδA₀ (by norm_num)
  have hδ0 : 0 < δ := by linarith
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδB : (1 / 16 : ℝ) < δ * r := by dsimp [r]; nlinarith
  have hden : 0 < 1 - exp (-0.50 / 2 : ℝ) := sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num))
  have hτ0 : 0 ≤ τ := by dsimp [τ]; positivity
  have hsave : δ * (1 + 2 * (τ + 0.001)) ≤ 1 - κ := by
    apply (mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 / 2)) (by positivity)).trans
    convert hsave₀ using 1 <;> ring
  obtain ⟨Z, hZ, hsmall₀⟩ := decomp338_endpoint_error_threshold (ε / 2) (by positivity)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (decomp338_case_four_high_mass_eventually r (by norm_num [r]) (by norm_num [r]))
  let Y₀ := max Z 100
  refine ⟨Y₀, by dsimp [Y₀]; omega, ?_⟩
  intro Y hY
  have hZY : Z ≤ Y := by dsimp [Y₀] at hY; omega
  have hY100 : 100 ≤ Y := by dsimp [Y₀] at hY; omega
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (decomp338_nested_floor_cutoff 1 r 0.249 (by norm_num) le_rfl
      (by norm_num [r]) (by norm_num [r]) (by norm_num) (by norm_num [r]) Y)
  let T := max T₁ T₂
  refine ⟨δ, κ / 2, by convert hδA using 1 <;> norm_num, hδhalf, by convert hδB using 1 <;> norm_num [r], by positivity, ?_⟩
  let C : ℕ := ∏ p ∈ Nat.primesLE Y, p
  have hCpos : 0 < C := by
    apply prod_pos
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  have hcast : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hδ0).comp hcast).eventually
      (eventually_ge_atTop ((max (max Y 2) T : ℕ) : ℝ)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < κ / 2 by positivity)).comp hcast).eventually
      (eventually_ge_atTop (C : ℝ)))
  refine ⟨max 2 (max X₁ X₂), ?_⟩
  intro ξ h hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  let H := decomp338EncodedGap h v t
  intro S hS hcaps
  change S ⊆ Nat.primesLE t at hS
  change ∀ j ∈ range (t + 1),
    (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1 at hcaps
  have hξ2 : 2 ≤ ξ := by omega
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have htm : max (max Y 2) T ≤ t := Nat.le_floor (hX₁ ξ (by omega))
  have hYt : Y ≤ t := by omega
  have hY4 : 4 ≤ Y := by omega
  have ht2 : 2 ≤ t := by omega
  have hsmall42 : ∀ y : ℕ, Y ≤ y → 4 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    have he1 : 4 / (y : ℝ) = 2 * (2 / (y : ℝ)) := by ring
    have he2 : 42 / Real.log y = (3 / 2 : ℝ) * (28 / Real.log y) := by ring
    constructor <;> nlinarith
  have hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    constructor <;> linarith
  have hsmall14 : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 14 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    have he : 14 / Real.log y = (1 / 2 : ℝ) * (28 / Real.log y) := by ring
    constructor <;> nlinarith
  have hhigh := hT₁ t (by dsimp [T] at htm; omega)
  have hvlarge := hT₂ t (by dsimp [T] at htm; omega)
  simp only [Real.rpow_one, Nat.floor_natCast] at hvlarge
  have hYv : Y ≤ v := hvlarge.1
  have hvt : v ≤ t := hhigh.2.1
  have hshift : Real.log 4 ≤ Real.log (Real.log t / Real.log v) := by
    have hh := hhigh.2.2.2
    dsimp [r] at hh
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg] at hh
    simpa only [v, r, one_div] using hh
  have hfirst : (decomp338GreedyCutoff H Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)) := by
    rw [hα1]
    exact decomp338_case_four_first_power h Y v t hY4 hYv hvt
      (Nat.floor_le (by positivity)) ε hε0.le hsmall14
  have hsecond : (decomp338GreedyCutoff H Y t 1 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 2)) := by
    rw [hα2]
    apply decomp338_mixed_second_power_max h Y v t hY100 hYv hvt (2 * ε) (Real.log 4) hhigh.2.2.1
    · intro y hy
      obtain ⟨h1, h2⟩ := hsmall42 y hy
      constructor <;> linarith
    · exact hshift
  have hprofile := decomp338_profile_from_two H Y t hY4 hYt ε α hsmall hfirst hsecond hrec
  have hstop := decomp338_greedy_stops H Y t hY4 hYt
  let A := S.filter (fun p => Y < p)
  let B := S.filter (fun p => p ≤ Y)
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hy : Y < p
      · exact Or.inl ⟨hp, hy⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpY := (mem_filter.mp hp).2
    have hqY := (mem_filter.mp hq).2
    omega
  have hBsub : B ⊆ Nat.primesLE Y := by
    intro p hp
    obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpY, (Nat.mem_primesLE.mp (hS hpS)).2⟩
  have hBbound : (∏ p ∈ B, p) ≤ C :=
    Nat.le_of_dvd hCpos (prod_dvd_prod_of_subset B (Nat.primesLE Y) id hBsub)
  have hcard : A.card ≤ 2 * t + 1 := by
    have hh := hcaps t (mem_range.mpr (by omega : t < t + 1))
    simpa only [hstop] using hh
  have hAcaps : ∀ i ∈ range t,
      (A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1 := by
    intro i hi
    have hsub : A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ)) ⊆
        S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t i < p) := by
      intro p hp
      obtain ⟨hpA, hpow⟩ := mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hpA
      have hpYR : (Y : ℝ) < p := by exact_mod_cast hpY
      have hmax : max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) < p := max_lt_iff.mpr ⟨hpYR, hpow⟩
      have hcR := (hprofile i).trans_lt hmax
      exact mem_filter.mpr ⟨hpS, by exact_mod_cast hcR⟩
    exact (card_le_card hsub).trans (hcaps i (mem_range.mpr (by have := mem_range.mp hi; omega)))
  have htop : (t : ℝ) ≤ (ξ : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hApos : ∀ p ∈ A, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).2.pos
  have hAmax : ∀ p ∈ A, (p : ℝ) ≤ t := by
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
  have hτ : 0 ≤ τ + 0.001 := by
    simpa using hαsum 0
  have hlarge := decompJ365_nested_saved_support A ξ t δ
    (τ + 0.001) κ hξ1
    (by exact_mod_cast (by omega : 1 < t)) htop hτ hκ α hαmono hα0 t
    (hαpos t).le (hαsum t) hApos hAmax hcard hAcaps hsave
  have hsmallprod : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ C := by exact_mod_cast hBbound
  have hCbound : (C : ℝ) ≤ (ξ : ℝ) ^ (κ / 2) := hX₂ ξ (by omega)
  have hsplit : ((∏ p ∈ S, p : ℕ) : ℝ) =
      ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
    rw [hAB, prod_union hdisj, Nat.cast_mul]
  calc
    _ = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := hsplit
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (C : ℝ) :=
      mul_le_mul hlarge hsmallprod (Nat.cast_nonneg _) (Real.rpow_nonneg hξ0.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2) :=
      mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg hξ0.le _)
    _ = (ξ : ℝ) ^ (1 - κ / 2) := by
      rw [← Real.rpow_add hξ0]
      congr 1
      ring

end
end LeanLab.Ricci1937
