/- AI wrote this Lean code for CODEX task224. Goldbach is open.
Lower-bound calculation in journal pp. 1220 and 1221, displays 4 and 5.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.ThetaMertens224

namespace LeanLab.BS2022GRH.LowerMertens224
open Real Finset Filter MeasureTheory Topology ThetaMertens224
noncomputable section

/-- A Mathlib logarithm bound sufficient for both printed roundings. -/
theorem log_ten_lower : (2.3025850926 : ℝ) < log 10 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  linarith [log_two_gt_d9, log_five_gt_d9]

/-- The lower cutoff in display 5 gives this explicit logarithm bound. -/
theorem log_lower_cutoff {x : ℝ} (hx : 1e12 ≤ x) :
    (27.6310211112 : ℝ) ≤ log x := by
  have hbase : log (1e12 : ℝ) = 12 * log 10 := by
    rw [show (1e12 : ℝ) = 10 ^ (12 : ℕ) by norm_num, log_pow]
    norm_num
  have h := log_le_log (by norm_num : (0 : ℝ) < 1e12) hx
  rw [hbase] at h
  linarith [log_ten_lower]

/-- The splitting point gives this explicit logarithm bound. -/
theorem log_split_lower : (43.7491167594 : ℝ) ≤ log (1e19 : ℝ) := by
  rw [show (1e19 : ℝ) = 10 ^ (19 : ℕ) by norm_num, log_pow]
  norm_num
  linarith [log_ten_lower]

/-- The first decimal rounding in journal p. 1220 display 5. -/
theorem endpoint_rounding {L : ℝ} (hL : 27.6310211112 ≤ L) :
    (6.9322e-5 : ℝ) / L ^ 2 ≤ 9.07982e-8 := by
  have hpos : 0 < L := by linarith
  rw [div_le_iff₀ (sq_pos_of_pos hpos)]
  nlinarith [sq_nonneg (L - 27.6310211112)]

/-- The second decimal rounding in journal p. 1220. -/
theorem tail_rounding {L : ℝ} (hL : 43.7491167594 ≤ L) :
    (8.6315e-7 : ℝ) * (1 / L + 1 / (2 * L ^ 2)) ≤ 1.99551e-8 := by
  have hpos : 0 < L := by linarith
  have h1 : (1 : ℝ) / L ≤ 1 / 43.7491167594 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have hsq : (43.7491167594 : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith
  have h2 : (1 : ℝ) / (2 * L ^ 2) ≤ 1 / (2 * 43.7491167594 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  nlinarith

/-- The signed finite part of display 4 is nonnegative when theta t is at most t. -/
theorem finite_error_nonneg {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y)
    (hθ : ∀ t : ℝ, x ≤ t → t ≤ y → Chebyshev.theta t ≤ t) :
    0 ≤ ∫ t in x..y, thetaError t := by
  apply intervalIntegral.integral_nonneg hxy
  intro t ht
  have htpos : 0 < t := lt_trans zero_lt_one (hx.trans_le ht.1)
  have hlpos : 0 < log t := log_pos (hx.trans_le ht.1)
  dsimp [thetaError]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (hθ t ht.1 ht.2)) (by positivity))
    (by positivity)

/-- Split at 10^19 to obtain the lower bound for the signed tail. -/
theorem signed_tail_lower {x : ℝ} (hx : 1e12 < x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ 6.9322e-5 * t / log t)
    (hθbig : ∀ t : ℝ, 1e19 ≤ t →
      |Chebyshev.theta t - t| ≤ 8.6315e-7 * t / log t)
    (hθsign : ∀ t : ℝ, 1e12 ≤ t → t ≤ 1e19 → Chebyshev.theta t ≤ t) :
    -(1.99551e-8 : ℝ) ≤ ∫ t in Set.Ioi x, thetaError t := by
  have hx1 : 1 < x := by linarith
  have hbig1 : (1 : ℝ) < 1e19 := by norm_num
  by_cases hsplit : x ≤ 1e19
  · have hfinite := finite_error_nonneg hx1 hsplit
      (fun t ht htb => hθsign t (by linarith) htb)
    have htail := theta_tail_bound hbig1 hθbig
    have hround := tail_rounding log_split_lower
    have hbound : -(1.99551e-8 : ℝ) ≤ ∫ t in Set.Ioi (1e19 : ℝ), thetaError t := by
      have hh := (abs_le.mp (htail.trans hround)).1
      exact hh
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (thetaError_integrable hx1 hθ) (thetaError_integrable hbig1 hθbig)
    linarith
  · have hθx : ∀ t : ℝ, x ≤ t →
        |Chebyshev.theta t - t| ≤ 8.6315e-7 * t / log t := by
      intro t ht
      exact hθbig t (by linarith)
    have htail := theta_tail_bound hx1 hθx
    have hlog : 43.7491167594 ≤ log x :=
      log_split_lower.trans (log_le_log (by norm_num) (le_of_not_ge hsplit))
    exact (abs_le.mp (htail.trans (tail_rounding hlog))).1

/-- Inclusive lower estimate from the three published theta inputs. -/
theorem reciprocal_lower_inclusive (M : ℝ)
    (hlim : Tendsto (fun y : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) - log (log y)) atTop (nhds M))
    {x : ℝ} (hx : 1e12 < x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ 6.9322e-5 * t / log t)
    (hθbig : ∀ t : ℝ, 1e19 ≤ t →
      |Chebyshev.theta t - t| ≤ 8.6315e-7 * t / log t)
    (hθsign : ∀ t : ℝ, 1e12 ≤ t → t ≤ 1e19 → Chebyshev.theta t ≤ t) :
    log (log x) + M - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p := by
  have hx2 : 2 ≤ x := by linarith
  have hx1 : 1 < x := by linarith
  rw [reciprocal_tail M hlim hx2 (thetaError_integrable hx1 hθ) (theta_boundary_limit hθ)]
  have hend := theta_endpoint_bound hx1 (hθ x le_rfl)
  have hround := endpoint_rounding (log_lower_cutoff hx.le)
  have hbound := (abs_le.mp (hend.trans hround)).1
  have htail := signed_tail_lower hx hθ hθbig hθsign
  linarith

/-- Pass from inclusive lower bounds to the exact strict endpoint by a left limit. -/
theorem inclusive_to_strict_lower (M E a : ℝ) (ha : 1 ≤ a)
    (hbound : ∀ y : ℝ, a < y → log (log y) + M - E ≤
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    {x : ℝ} (hx : a < x) :
    log (log x) + M - E ≤ ∑ p ∈ Nat.primesBelow ⌈x⌉₊, (1 : ℝ) / p := by
  have hx1 : 1 < x := ha.trans_lt hx
  have hcont : ContinuousAt (fun y : ℝ => log (log y) + M - E) x := by
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
    have hlog : log x ≠ 0 := ne_of_gt (log_pos hx1)
    fun_prop
  apply le_of_tendsto (hcont.tendsto.mono_left
    (show nhdsWithin x (Set.Iio x) ≤ nhds x from nhdsWithin_le_nhds))
  have haevent : ∀ᶠ y in nhdsWithin x (Set.Iio x), a < y :=
    (show ∀ᶠ y in nhds x, a < y from lt_mem_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, haevent] with y hy hay
  apply (hbound y hay).trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpy, hprime⟩ := Nat.mem_primesLE.mp hp
    apply Nat.mem_primesBelow.mpr
    refine ⟨Nat.lt_ceil.mpr ?_, hprime⟩
    have hpyreal : (p : ℝ) ≤ y :=
      (Nat.cast_le.mpr hpy).trans (Nat.floor_le (by linarith : 0 ≤ y))
    exact hpyreal.trans_lt hy
  · intro p hp hnot
    positivity

end
end LeanLab.BS2022GRH.LowerMertens224

#print axioms LeanLab.BS2022GRH.LowerMertens224.log_ten_lower
#print axioms LeanLab.BS2022GRH.LowerMertens224.log_lower_cutoff
#print axioms LeanLab.BS2022GRH.LowerMertens224.log_split_lower
#print axioms LeanLab.BS2022GRH.LowerMertens224.endpoint_rounding
#print axioms LeanLab.BS2022GRH.LowerMertens224.tail_rounding
#print axioms LeanLab.BS2022GRH.LowerMertens224.finite_error_nonneg
#print axioms LeanLab.BS2022GRH.LowerMertens224.signed_tail_lower
#print axioms LeanLab.BS2022GRH.LowerMertens224.reciprocal_lower_inclusive
#print axioms LeanLab.BS2022GRH.LowerMertens224.inclusive_to_strict_lower
