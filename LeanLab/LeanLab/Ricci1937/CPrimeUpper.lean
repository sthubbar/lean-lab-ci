import LeanLab.Ricci1937.CPrimeSums

/-!
Elementary prime count bounds for the identity case of Ricci 1937, page 74.
These are auxiliary estimates, not additional printed statements of the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Filter Asymptotics
noncomputable section

/-- A uniform elementary prime count upper bound, with no cited input. -/
theorem ricci_primeCounting_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * x / Real.log x := by
  refine ⟨2 * Real.log 4 + 1, by positivity, ?_⟩
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_gt_atTop 1] with x h hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsquare := Real.sq_sqrt hxpos.le
  simp only [Real.norm_eq_abs, abs_of_pos hlog,
    abs_of_pos (Real.rpow_pos_of_pos hxpos _), one_mul] at h
  rw [← Real.sqrt_eq_rpow] at h
  have hroot : Real.sqrt x ≤ x / Real.log x := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  have hpi := Chebyshev.pi_le_log4_mul_div hx
  rw [Real.log_sqrt hxpos.le] at hpi
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by
      convert hpi using 1
      ring
    _ ≤ 2 * Real.log 4 * x / Real.log x + x / Real.log x := add_le_add le_rfl hroot
    _ = (2 * Real.log 4 + 1) * x / Real.log x := by ring

/-- The complementary factor is above the reciprocal block threshold. -/
lemma ricci_complementary_power {N p α : ℝ} (hN : 0 < N) (hp : 0 < p)
    (hpmax : p ≤ N ^ (1 - α)) : N ^ α ≤ N / p := by
  have hprod : N ^ α * N ^ (1 - α) = N := by
    rw [← Real.rpow_add hN]
    norm_num
  apply (le_div_iff₀ hp).mpr
  calc
    N ^ α * p ≤ N ^ α * N ^ (1 - α) :=
      mul_le_mul_of_nonneg_left hpmax (Real.rpow_nonneg hN.le _)
    _ = N := hprod

/-- A large complementary factor gives a uniform logarithmic denominator. -/
lemma ricci_complementary_log {N p α : ℝ} (hN : 1 < N) (hp : 0 < p) (_hα : 0 < α)
    (hpmax : p ≤ N ^ (1 - α)) : α * Real.log N ≤ Real.log (N / p) := by
  have hNpos : 0 < N := by linarith
  have h := Real.log_le_log (Real.rpow_pos_of_pos hNpos α)
    (ricci_complementary_power hNpos hp hpmax)
  rw [Real.log_rpow hNpos] at h
  exact h

/-- The prime count bound at N/p in a large factor block. -/
lemma ricci_primeCounting_div_le {n p : ℕ} {K α : ℝ} (hn : 2 ≤ n) (hp : p.Prime)
    (hK : 0 ≤ K) (hα : 0 < α) (hpmax : (p : ℝ) ≤ (n : ℝ) ^ (1 - α))
    (hpi : (Nat.primeCounting ⌊(n : ℝ) / p⌋₊ : ℝ) ≤
      K * ((n : ℝ) / p) / Real.log ((n : ℝ) / p)) :
    (Nat.primeCounting (n / p) : ℝ) ≤ (K / α) * ((n : ℝ) / Real.log n) * (1 / p) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := ricci_complementary_log hnR hpR hα hpmax
  have hlow : 0 < α * Real.log n := mul_pos hα (Real.log_pos hnR)
  rw [Nat.floor_div_eq_div] at hpi
  calc
    (Nat.primeCounting (n / p) : ℝ) ≤
        K * ((n : ℝ) / p) / Real.log ((n : ℝ) / p) := hpi
    _ ≤ K * ((n : ℝ) / p) / (α * Real.log n) :=
      div_le_div_of_nonneg_left (by positivity) hlow hlog
    _ = (K / α) * ((n : ℝ) / Real.log n) * (1 / p) := by ring

example : (16 : ℝ) ^ ((1 : ℝ) / 2) ≤ 16 / 4 := by
  apply ricci_complementary_power (by norm_num) (by norm_num)
  norm_num [show (1 - (1 : ℝ) / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

end
end LeanLab.Ricci1937
