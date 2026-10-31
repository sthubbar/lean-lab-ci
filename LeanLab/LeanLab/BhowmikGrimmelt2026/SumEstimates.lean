/-
Summing the weight estimates over reduced pairs in Lemma 7.2, page 26.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.WeightedGap
import LeanLab.BhowmikGrimmelt2026.FiniteSum
import LeanLab.BhowmikGrimmelt2026.ScaledBounds

namespace LeanLab.BhowmikGrimmelt2026

/-- The reduced pair sum with scales K times R times q. -/
noncomputable def scaledPairSum (G : ℝ → ℝ) (R K α : ℝ) : ℂ :=
  ∑ p ∈ reducedPairs ⌊R⌋₊, GThat G (K * R * p.1) (α - p.2 / p.1)

/-- Uniform reduced pair bounds with one close pair for the central approximation. -/
theorem scaledPairSum_estimates {G : ℝ → ℝ} (hG : IsMajorWeight G) {A : ℝ} (hA : 0 < A) :
    ∃ H : ℝ, 0 < H ∧ ∀ R K η : ℝ, 1 ≤ R → 1 ≤ K → 0 ≤ η → ∀ α : ℝ,
      ((∃ p ∈ reducedPairs ⌊R⌋₊,
          K * R * (p.1 : ℝ) * intDist (α - p.2 / p.1) ≤ η) →
        ‖scaledPairSum G R K α - 1‖ ≤ H * (η ^ 2 + R ^ 2 * K ^ (-A))) ∧
      ‖scaledPairSum G R K α‖ ≤ H * (1 + R ^ 2 * K ^ (-A)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := scaled_GThat_bounds hG hA
  obtain ⟨D, hD, hcentral⟩ := GThat_central hG A
  let B : ℝ := C * (2 ^ A + 1)
  let H : ℝ := 8 * Real.pi ^ 2 + C + D + B
  have hB : 0 < B := by dsimp [B]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H, hH, fun R K η hR hK hη α => ?_⟩
  let s := reducedPairs ⌊R⌋₊
  let f : (Σ _ : ℕ, ℕ) → ℂ := fun p => GThat G (K * R * p.1) (α - p.2 / p.1)
  have hR0 : 0 < R := by linarith
  have hK0 : 0 < K := by linarith
  have hM : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hR)
  have hMR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0.le
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hP : 0 ≤ K ^ (-A) := Real.rpow_nonneg hK0.le _
  have hE : 0 ≤ B * K ^ (-A) := mul_nonneg hB.le hP
  have hcard : (s.card : ℝ) ≤ R ^ 2 := by
    have hc : ((reducedPairs ⌊R⌋₊).card : ℝ) ≤ (⌊R⌋₊ : ℝ) ^ 2 := by
      exact_mod_cast reducedPairs_card_le ⌊R⌋₊
    have hM0 : (0 : ℝ) ≤ ⌊R⌋₊ := by positivity
    dsimp [s]
    exact hc.trans (pow_le_pow_left₀ hM0 hMR 2)
  obtain ⟨p₀, hp₀, hmin⟩ := reducedPairs_min hM α
  have hq₀ : (1 : ℝ) ≤ p₀.1 := by exact_mod_cast ((mem_reducedPairs _ _).mp hp₀).1
  have hothers : ∀ p ∈ s, p ≠ p₀ → ‖f p‖ ≤ B * K ^ (-A) := by
    intro p hp hne
    have hq : (1 : ℝ) ≤ p.1 := by exact_mod_cast ((mem_reducedPairs _ _).mp hp).1
    exact (hbound K R p.1 (α - p.2 / p.1) hK hR hq).2
      (reduced_pair_gap hMR hp₀ hp hne (hmin p hp))
  have hc := mul_le_mul_of_nonneg_right hcard hE
  have hCP := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 hP) hC.le
  have hDP := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 hP) hD.le
  have hHC : C ≤ H := by dsimp [H]; nlinarith [sq_nonneg Real.pi]
  have hHCB : C + B ≤ H := by dsimp [H]; nlinarith [sq_nonneg Real.pi]
  have hHQ : 8 * Real.pi ^ 2 ≤ H := by dsimp [H]; linarith
  have hHDB : D + B ≤ H := by dsimp [H]; nlinarith [sq_nonneg Real.pi]
  constructor
  · rintro ⟨p, hp, hclose⟩
    have hRq : 1 ≤ R * (p₀.1 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hq₀ hR0.le
      nlinarith only [h, hR]
    have hKT : K ≤ K * R * p₀.1 := by
      have h := mul_le_mul_of_nonneg_left hRq hK0.le
      nlinarith only [h]
    have hT : 1 ≤ K * R * p₀.1 := hK.trans hKT
    have hsmall : K * R * (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ η := by
      have h := mul_le_mul_of_nonneg_left (hmin p hp) (mul_nonneg hK0.le hR0.le)
      nlinarith only [h, hclose]
    have hnonneg : 0 ≤ K * R * (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) :=
      mul_nonneg (by positivity) (intDist_nonneg _)
    have hsquare := pow_le_pow_left₀ hnonneg hsmall 2
    have hpower := Real.rpow_le_rpow_of_nonpos hK0 hKT (neg_nonpos.mpr hA.le)
    have hmain : ‖f p₀ - 1‖ ≤ 8 * Real.pi ^ 2 * η ^ 2 + D * K ^ (-A) := by
      exact (hcentral (K * R * p₀.1) (α - p₀.2 / p₀.1) hT).trans
        (add_le_add (mul_le_mul_of_nonneg_left hsquare (by positivity))
          (mul_le_mul_of_nonneg_left hpower hD.le))
    have hsum := norm_sum_sub_one_le s f hp₀ hE hmain hothers
    have h1 := mul_le_mul_of_nonneg_right hHQ (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_right hHDB (mul_nonneg (sq_nonneg R) hP)
    change ‖(∑ p ∈ s, f p) - 1‖ ≤ _
    nlinarith only [hsum, hc, hDP, h1, h2]
  · have hmain := (hbound K R p₀.1 (α - p₀.2 / p₀.1) hK hR hq₀).1
    have hsum := norm_sum_le_one_term s f hp₀ hE hmain hothers
    have h2 := mul_le_mul_of_nonneg_right hHCB (mul_nonneg (sq_nonneg R) hP)
    change ‖∑ p ∈ s, f p‖ ≤ _
    nlinarith only [hsum, hc, hCP, hHC, h2]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.scaledPairSum_estimates
