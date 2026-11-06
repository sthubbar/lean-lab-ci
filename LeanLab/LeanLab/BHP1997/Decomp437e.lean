/-
P0069, pages 12 and 13, the dominant square moment for Case 1.
The cited mean square, cited large values and energy estimates remain premises.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437d

namespace LeanLab.BHP1997.Decomp437e
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c Decomp437d
open scoped BigOperators

/-- Pages 12 and 13, displays 3.11 and 3.12, summed on the dominant values.
The low character-time range uses the mean square estimate directly.
The other range uses the actual dyadic cells and their logarithmic count.
CONDITIONAL on the three explicit analytic premises. No cited sorry is called. -/
theorem dominant_square_moment (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 →
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, CoeffBound a B →
    2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
    (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      C * F * Real.log x ^ D := by
  intro B c1 c2 hc1 hc2
  obtain ⟨Cm, hCm, hm⟩ := hmean B c1 c2 hc1 hc2
  obtain ⟨Cl, hCl, hcell⟩ := dominant_dyadic_square_bound hlarge B c1 c2 hc1 hc2
  obtain ⟨Ce, K, hCe, hK, he⟩ := energy_log_uniform henergy B c1 c2 hc1 hc2
  obtain ⟨Cn, hCn, hpoly⟩ := dirPoly_norm_uniform B c1 c2 hc1 (hc1.trans hc2)
  let J := (Real.log (Cn + 1) + 2) / Real.log 2 + 2
  have hJ : 0 < J := by
    have hh : 0 ≤ Real.log (Cn + 1) := Real.log_nonneg (by linarith)
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [J]
    positivity
  let C := 2 * Cm * Ce + 4 * Cl * J * (Ce + 16 * Ce ^ 3)
  let D := 3 * K + 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, D, hC, by dsimp [D]; linarith, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes hdom
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
  have henergyF := he a ha x F hlx hF hFx
  have hClo : 2 * Cm * Ce ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 4 * Cl * J * (Ce + 16 * Ce ^ 3) := by positivity
    linarith
  have hChi : 4 * Cl * J * (Ce + 16 * Ce ^ 3) ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 2 * Cm * Ce := by positivity
    linarith
  by_cases hQ : (q : ℝ) * T ≤ F
  · have hs := hm x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
    have hpow : Real.log x * Real.log x ^ K ≤ Real.log x ^ D := by
      have heq : Real.log x * Real.log x ^ K = Real.log x ^ (1 + K) := by
        rw [Real.rpow_add hlx0, Real.rpow_one]
      rw [heq]
      exact Real.rpow_le_rpow_of_exponent_le hlx (by dsimp [D]; linarith)
    calc
      _ ≤ Cm * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hs
      _ ≤ Cm * Real.log x * (2 * F) * (Ce * Real.log x ^ K) := by gcongr <;> linarith
      _ = (2 * Cm * Ce) * F * (Real.log x * Real.log x ^ K) := by ring
      _ ≤ C * F * Real.log x ^ D := mul_le_mul
        (mul_le_mul_of_nonneg_right hClo hF0) hpow (by positivity) (by positivity)
  have hQ' : F < (q : ℝ) * T := lt_of_not_ge hQ
  let f : (ℝ × DirichletCharacter ℂ q) → ℂ := fun p => dirPoly a c1 c2 F p.2 (half p.1)
  let U : ℝ := (Cn + 1) * x ^ 2
  have hvalues : ∀ p ∈ S, 1 ≤ ‖f p‖ ∧ ‖f p‖ ≤ U := by
    intro p hp
    have hfour := dominant_value_fourth (by linarith : 1 < F) hQ' (hdom p hp)
    have hn1 : 1 ≤ ‖f p‖ := by
      by_contra! hn
      have hh := pow_lt_pow_left₀ hn (norm_nonneg (f p)) (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at hh
      change (q : ℝ) * T ≤ ‖f p‖ ^ 4 at hfour
      linarith
    refine ⟨hn1, ?_⟩
    calc
      _ ≤ Cn * F ^ 2 := hpoly a ha F (by linarith) q p.2 p.1
      _ ≤ (Cn + 1) * x ^ 2 := mul_le_mul (by linarith) (pow_le_pow_left₀ hF0 hFx 2)
        (sq_nonneg _) (by linarith)
  have hcount : ((dyadicLevels 1 U).card : ℝ) ≤ J * Real.log x :=
    quadratic_level_count (by linarith) (by linarith) hlx
  have hEcube := energy_cubic_log_bound hE hCe.le hK hlx henergyF
  have hsum := square_sum_of_dyadic_cells S f hvalues
    (fun k hk => hcell x F T q S a ha hx hF hFx hT hTx hq hqx hQ' hspace htimes hdom k)
  have hlogeq : Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x = Real.log x ^ D := by
    calc
      _ = Real.log x ^ (3 * K) * Real.log x ^ (2 : ℝ) * Real.log x ^ (1 : ℝ) := by simp
      _ = Real.log x ^ (3 * K + 2 + 1) := by rw [← Real.rpow_add hlx0, ← Real.rpow_add hlx0]
      _ = _ := by congr 1; dsimp [D]; ring
  calc
    _ ≤ (dyadicLevels 1 U).card *
        (4 * Cl * Real.log x ^ 2 * F * (energy a c1 c2 F + 16 * energy a c1 c2 F ^ 3)) := hsum
    _ ≤ (J * Real.log x) *
        (4 * Cl * Real.log x ^ 2 * F * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K))) :=
      mul_le_mul hcount (mul_le_mul_of_nonneg_left hEcube (by positivity)) (by positivity) (by positivity)
    _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F *
        (Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x) := by ring
    _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F * Real.log x ^ D := by rw [hlogeq]
    _ ≤ C * F * Real.log x ^ D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hChi hF0) (by positivity)

end LeanLab.BHP1997.Decomp437e
