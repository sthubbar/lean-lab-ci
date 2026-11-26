/-
Burst 2026-11-22 S129 wave 13, BHP1997, a split of
`DQLeaf518SplitFeed1122.leaf_perron_window`, P0069 Baker Harman Pintz 1997, Lemma 29 on
page 43, first step of the proof, case `χ ≠ χ0`.

The paper states the Perron step pointwise: for each `y` in the window range the window sum is
the truncated Perron integral at height `Y` plus `O(Y^ε)`, by [30] Titchmarsh Lemma 3.19. The
parent leaf is its mean square over `y ∈ [Y/2, 3Y]`. This file isolates the pointwise statement
as the new LEAF `leaf_perron_pointwise`, with `δχ = 0` already used, and PROVES
`leaf_perron_window_split`, with exactly the type of the parent leaf, from it. No
integrability is needed: if the squared error is not integrable its interval integral is zero.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.DQLeaf518SplitFeed1122Lemma29

namespace LeanLab.BHP1997.DQLeaf518PerronWindowS129
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43, first display of the proof of Lemma 29, class HARD, CITED [30] Titchmarsh
1986 Lemma 3.19 p. 70, the truncated Perron formula on the line `σ = 1/2` at height `T = Y`.
P0069 Baker Harman Pintz 1997: for `χ ≠ χ0` and each `y ∈ [Y/2, 3Y]`, with `Y = x^(11/20+ε)`
and `m` running over `J = (Y, 2Y]`, the window sum `Σ_{y ≤ m ≤ y+yz} b(m) χ(m)` equals
`(1/2π) ∫_{-Y}^{Y} G(1/2+it, χ) ((y+yz)^s - y^s)/s dt + O(Y^ε)`, here with `ε = 1/100`;
the divisor bound on `b` and the endpoint terms `m = y`, `m = y+yz` go into the `O`. -/
theorem leaf_perron_pointwise (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y → y ≤ 3 * x ^ (11 / 20 + ε) →
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) - (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ≤
            K * (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := by
  sorry

/-- A pointwise bound `F y ≤ M` on `[a, b]` gives `∫ F ≤ (b - a) M`, also when `F` is not
interval integrable. PROVED. -/
theorem integral_le_of_pointwise {F : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hF : ∀ y, a ≤ y → y ≤ b → F y ≤ M) :
    ∫ y in a..b, F y ≤ (b - a) * M := by
  by_cases hi : IntervalIntegrable F volume a b
  · have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      (fun y hy => hF y hy.1 hy.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using h
  · rw [intervalIntegral.integral_undef hi]
    exact mul_nonneg (by linarith) hM

/-- P0069 page 43, PROVED from `leaf_perron_pointwise`: exactly the statement of
`DQLeaf518SplitFeed1122.leaf_perron_window`. Uses `Thm2.delta χ = 0` for `χ ≠ 1`. -/
theorem leaf_perron_window_split (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) - (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  obtain ⟨K, hK, C, hC⟩ := leaf_perron_pointwise b hε hb
  refine ⟨3 * K ^ 2, by positivity, max C 1, ?_⟩
  intro x hx q hq1 hqQ z hz1 hz2 χ hχ
  have hx1 : C ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
  have hsq : ((x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ)) ^ 2 = (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
  have hP : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := Real.rpow_nonneg hY.le _
  simp only [hd, zero_mul, sub_zero]
  refine (integral_le_of_pointwise (M := (K * (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ)) ^ 2)
    (by linarith) (by positivity) ?_).trans ?_
  · intro y hy1 hy2
    have h := hC x hx1 q hq1 hqQ z hz1 hz2 χ hχ y hy1 hy2
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  · rw [mul_pow, hsq]
    have hE : 0 ≤ K ^ 2 * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by positivity
    nlinarith [mul_nonneg hY.le hE]

end LeanLab.BHP1997.DQLeaf518PerronWindowS129
