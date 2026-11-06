import LeanLab.Ricci1937.Decomp338j

/-!
Ricci 1937, saved support supplier for the first pair.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Supply proof of the saved support piece for the first pair.
First memoir page 89 and second memoir pages 113 and 114 formulas 31.3 to 31.5.
The fixed residual prime product is absorbed by half the positive power saving. -/
theorem decomp338_greedy_support_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / 7 < δ ∧ δ ≤ 1 / 2 ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  obtain ⟨ε, α, δ, κ, hε0, hε, hδ0, hκ, hδ7, hα1, hα2, htail, hsave⟩ :=
    decompJ365_first_case_support_parameters
  obtain ⟨Y₀, hY₀, hsmall₀⟩ := decomp338_endpoint_error_threshold ε hε0
  obtain ⟨hfirst, hrec⟩ := decomp338_support_profile_recurrence ε α hα1 hα2 htail
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY
  let δ' := min δ (1 / 2)
  have hδ' : 1 / 7 < δ' := lt_min hδ7 (by norm_num)
  have hδ'0 : 0 < δ' := by linarith
  refine ⟨δ', κ / 2, hδ', min_le_right _ _, by positivity, ?_⟩
  let C : ℕ := ∏ p ∈ Nat.primesLE Y, p
  have hCpos : 0 < C := by
    apply prod_pos
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  have hcast : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hδ'0).comp hcast).eventually
      (eventually_ge_atTop ((max Y 2 : ℕ) : ℝ)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < κ / 2 by positivity)).comp hcast).eventually
      (eventually_ge_atTop (C : ℝ)))
  refine ⟨max 2 (max X₁ X₂), ?_⟩
  intro ξ h hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ'⌋₊
  intro S hS hcaps
  change S ⊆ Nat.primesLE t at hS
  change ∀ j ∈ range (t + 1),
    (S.filter (fun p : ℕ => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1 at hcaps
  have hξ2 : 2 ≤ ξ := by omega
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have htm : max Y 2 ≤ t := Nat.le_floor (hX₁ ξ (by omega))
  have hYt : Y ≤ t := by omega
  have hY4 : 4 ≤ Y := hY₀.trans hY
  have ht2 : 2 ≤ t := by omega
  have hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε :=
    fun y hy => hsmall₀ y (hY.trans hy)
  have hprofile := decomp338_greedy_profile_bound h Y t hY4 hYt ε α hsmall hfirst hrec
  have hstop := decomp338_greedy_stops h Y t hY4 hYt
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
        S.filter (fun p : ℕ => decomp338GreedyCutoff h Y t i < p) := by
      intro p hp
      obtain ⟨hpA, hpow⟩ := mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hpA
      have hpYR : (Y : ℝ) < p := by exact_mod_cast hpY
      have hmax : max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) < p := max_lt_iff.mpr ⟨hpYR, hpow⟩
      have hcR := (hprofile i).trans_lt hmax
      exact mem_filter.mpr ⟨hpS, by exact_mod_cast hcR⟩
    exact (card_le_card hsub).trans (hcaps i (mem_range.mpr (by have := mem_range.mp hi; omega)))
  have htop : (t : ℝ) ≤ (ξ : ℝ) ^ δ := by
    calc
      _ ≤ (ξ : ℝ) ^ δ' := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hξ1 (min_le_left _ _)
  have hApos : ∀ p ∈ A, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).2.pos
  have hAmax : ∀ p ∈ A, (p : ℝ) ≤ t := by
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
  have hlarge := hsave t A ξ t hξ1 (by exact_mod_cast (by omega : 1 < t))
    htop hApos hAmax hcard hAcaps
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
