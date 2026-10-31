import LeanLab.GoldbachAverage.State1558

/-!
P0050 real endpoint transfer, arXiv 0806.3295v3 pages 1 and 2.
This proves the named floor step input and the real upper half of Theorem 1.1 under RH.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.FloorStep124
open LeanLab.PNTPort.ExplicitPsi1 LeanLab.LZCesaroShort
open State1558 OmegaTransfer82

/-- For x at least two, replacing the logarithm at max of six and x costs a fixed factor.
Source context: the real endpoint step in P0050 Theorem 1.1, pages 1 and 2. -/
theorem cutoff_log_bound {x : ℝ} (hx : 2 ≤ x) :
    Real.log (max 6 x) + 1 ≤ 7 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hl : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hm : max 6 x ≤ 3 * x := max_le (by linarith) (by linarith)
  have hml := Real.log_le_log (show (0 : ℝ) < max 6 x by positivity) hm
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne'] at hml
  have h3 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  linarith

/-- A unit zero sum step at an arbitrary real endpoint has a linear bound with two logarithms.
Source: P0050 Theorem 1.1, pages 1 and 2, the endpoint correction.
This coarse consequence of the proved RH zero sum difference estimate is sufficient here. -/
theorem zero_sum_floor_log_two (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖Z1 x - Z1 (⌊x⌋₊ : ℝ)‖ ≤ C * x * Real.log x ^ 2 := by
  obtain ⟨D1, D2, hD1, hD2, hb⟩ := dW_bound hRH
  refine ⟨294 * D1 + 336 * D2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set t : ℝ := max 6 x with ht
  have ht6 : 6 ≤ t := le_max_left _ _
  have hxt : x ≤ t := le_max_right _ _
  have ht0 : 0 < t := by linarith
  have ht3x : t ≤ 3 * x := max_le (by linarith) (by linarith)
  have hn0 : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hgap : x - (⌊x⌋₊ : ℝ) ≤ 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have he := hb t ht6 (⌊x⌋₊ : ℝ) x hn0 hnx (by linarith)
  rw [Wf_eq_Z1, Wf_eq_Z1] at he
  have hp : (2 * t) ^ ((1 : ℝ) / 2) ≤ 6 * x := by
    calc (2 * t) ^ ((1 : ℝ) / 2) ≤ (2 * t) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 * t := Real.rpow_one _
      _ ≤ 6 * x := by linarith
  have hP0 : 0 ≤ (2 * t) ^ ((1 : ℝ) / 2) := by positivity
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hlogt : 0 ≤ Real.log t + 1 := by
    have := Real.log_nonneg (by linarith : 1 ≤ t)
    linarith
  have hlt := cutoff_log_bound hx
  change Real.log t + 1 ≤ 7 * Real.log x at hlt
  have hlt2 : (Real.log t + 1) ^ 2 ≤ (7 * Real.log x) ^ 2 :=
    pow_le_pow_left₀ hlogt hlt 2
  have hpow : (2 * t) ^ ((3 : ℝ) / 2) =
      (2 * t) * (2 * t) ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by ring,
      Real.rpow_add (by positivity), Real.rpow_one]
  rw [hpow] at he
  have htail : (2 * t) * (2 * t) ^ ((1 : ℝ) / 2) *
      (2 * D2 * (Real.log t + 1) / t) =
      4 * D2 * (2 * t) ^ ((1 : ℝ) / 2) * (Real.log t + 1) := by
    field_simp [ht0.ne'] <;> ring
  rw [htail] at he
  have hfirst : (x - (⌊x⌋₊ : ℝ)) * (2 * t) ^ ((1 : ℝ) / 2) *
      (D1 * (Real.log t + 1) ^ 2) ≤ 294 * D1 * x * Real.log x ^ 2 := by
    calc _ ≤ 1 * (6 * x) * (D1 * (7 * Real.log x) ^ 2) := by gcongr
      _ = _ := by ring
  have hsecond : 4 * D2 * (2 * t) ^ ((1 : ℝ) / 2) * (Real.log t + 1) ≤
      336 * D2 * x * Real.log x ^ 2 := by
    have hl2 : Real.log x ≤ 2 * Real.log x ^ 2 := by
      nlinarith [sq_nonneg (Real.log x - 1 / 2)]
    calc _ ≤ 4 * D2 * (6 * x) * (7 * Real.log x) := by gcongr
      _ ≤ 336 * D2 * x * Real.log x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 168 * D2 * x by positivity)]
  nlinarith

/-- The named floor step input from State1558 now follows under RH only.
Source: P0050 Theorem 1.1, pages 1 and 2. -/
theorem zero_sum_floor_step : ZeroSumFloorStepStatement := by
  intro hRH
  obtain ⟨C, hC, hb⟩ := zero_sum_floor_log_two hRH
  refine ⟨8 * C, by positivity, fun x hx => ?_⟩
  have hl : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hl 3
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (Real.log x))
  have hs : Real.log x ^ 2 ≤ 8 * Real.log x ^ 5 := by nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hb' := mul_le_mul_of_nonneg_left hs (show 0 ≤ C * x by positivity)
  exact (hb x hx).trans (by nlinarith)

/-- P0050 Theorem 1.1 upper bound over real x. RH is the only unproved premise.
The older integer upper bound and the now proved floor step supply the result. -/
theorem upper_real_under_RH : Thm1_1UpperRealStatement :=
  upper_real_of_floor_step zero_sum_floor_step

end LeanLab.GoldbachAverage.FloorStep124
