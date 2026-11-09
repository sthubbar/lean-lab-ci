/- AI wrote this Lean code for CODEX task339. Goldbach is open.
A scalar audit of the endpoint route on journal p. 1241.
This does not refute the finite remainder or Theorem 7.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Endpoint339
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.BS2022GRH.EndpointGrowth339
open Real Filter ChenThresholdGRH DecompC164c
noncomputable section

/-- The printed majorant has a uniform positive constant lower bound.
Journal p. 1240 display 31. All discarded summands are nonnegative. -/
theorem mbar_lower (N A W : ℝ) (hN : 1 < N) (hW : 0 < W) (hL : 2750 ≤ log W)
    (hD : 1e8 ≤ √N / log N ^ (A + 1)) : 4 / log 2 ≤ mbarJ N A W := by
  have hN0 : 0 < N := by linarith
  have hLN : 0 < log N := log_pos hN
  have hW25 : 25 ≤ W := by linarith [log_le_sub_one_of_pos hW]
  have hlW : 0 < log W := by linarith
  have hl2W : 0 < log (2 * W) := log_pos (by linarith)
  have hqW := DecompC164b.qG_positive W hW25
  have hq2W := DecompC164b.qG_positive (2 * W) (by linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hPhi0 : 0 < Mphi0 W := by linarith [Mphi339.one_le_Mphi0 W hW hL]
  have hD1 : 1 < √N / log N ^ (A + 1) := by linarith
  have hPhi : 0 < Mphi (√N / log N ^ (A + 1)) := by
    linarith [Lemma5Coeffs138.one_le_Mphi _ hD1]
  have hlogD1 : 1 < log (√N / log N ^ (A + 1)) := by
    rw [lt_log_iff_exp_lt (by positivity)]
    linarith [exp_one_lt_d9]
  have hgap : 0 < log (log (√N) - (A + 1) * log (log N)) := by
    have he : log (√N) - (A + 1) * log (log N) = log (√N / log N ^ (A + 1)) := by
      rw [log_div (sqrt_pos.mpr hN0).ne' (rpow_pos_of_pos hLN _).ne', log_rpow hLN]
    rw [he]
    exact log_pos hlogD1
  have hPhi1 := Lemma5Coeffs138.one_le_Mphi (√N / log N ^ (A + 1)) hD1
  unfold mbarJ
  calc 4 / log 2 = 2 * 1 * (2 / log 2) := by ring
       _ ≤ _ := by
         gcongr
         apply le_trans ?_ (le_add_of_nonneg_right (by positivity))
         apply le_trans ?_ (le_add_of_nonneg_right (by positivity))
         exact le_add_of_nonneg_right (by positivity)

/-- At A equal to one the full scalar bracket has a positive cubic logarithm lower bound.
Journal p. 1241 display 33. This is only a scalar route audit. -/
theorem small_A_error_lower (N : ℝ) (hN : 1 < N) (hL : 22000 ≤ log N)
    (hD : 1e8 ≤ √N / log N ^ ((1 : ℝ) + 1)) :
    (invTw * (1 + (1 / 2 : ℝ)) / log (1 + (1 / 2 : ℝ)) *
      (0.053 * (1 + (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ)) * (4 / log 2)) * log N ^ (3 : ℕ) ≤
      errorBracket 1 N (1 / 2) := by
  have hN0 : 0 < N := by linarith
  have hLN : 0 < log N := log_pos hN
  have hW : 0 < N ^ (1 / 8 : ℝ) := rpow_pos_of_pos hN0 _
  have hLW : 2750 ≤ log (N ^ (1 / 8 : ℝ)) := by rw [log_rpow hN0]; linarith
  have hm := mbar_lower N 1 (N ^ (1 / 8 : ℝ)) hN hW hLW hD
  have hinv : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hlb : 0 < log (1 + (1 / 2 : ℝ)) := log_pos (by norm_num)
  have hp : log N ^ ((1 : ℝ) - 4) = (log N ^ (3 : ℕ))⁻¹ := by
    norm_num [rpow_neg_natCast]
  rw [Endpoint339.error_normalization N 1 (1 / 2) hN (by norm_num), hp, div_inv_eq_mul]
  calc _ = invTw * (1 + (1 / 2 : ℝ)) / log (1 + (1 / 2 : ℝ)) *
      (0.053 * (1 + (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) * ((4 / log 2) * log N ^ (3 : ℕ)) + 0) := by ring
       _ ≤ _ := by gcongr <;> positivity


/-- The full scalar error bracket is unbounded on the stated real endpoint range at A one.
Journal p. 1241 endpoint route audit. This says nothing about the finite remainder. -/
theorem small_A_unbounded (M : ℝ) : ∃ N : ℝ, exp (exp 10) ≤ N ∧
    M < errorBracket 1 N (1 / 2) := by
  let C : ℝ := invTw * (1 + (1 / 2 : ℝ)) / log (1 + (1 / 2 : ℝ)) *
      (0.053 * (1 + (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ)) * (4 / log 2)
  have hinv : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hlb : 0 < log (1 + (1 / 2 : ℝ)) := log_pos (by norm_num)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdlim : Tendsto (fun t : ℝ => √(exp t) / log (exp t) ^ ((1 : ℝ) + 1)) atTop atTop := by
    convert tendsto_exp_mul_div_rpow_atTop (2 : ℝ) (1 / 2) (by norm_num) using 1
    funext t
    rw [sqrt_eq_rpow, ← exp_mul, log_exp]
    congr 1 <;> ring
  have hclim : Tendsto (fun t : ℝ => C * t ^ (3 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).const_mul_atTop hC
  have hev : ∀ᶠ t : ℝ in atTop, exp 10 ≤ t ∧ 22000 ≤ t ∧
      1e8 ≤ √(exp t) / log (exp t) ^ ((1 : ℝ) + 1) ∧ M < C * t ^ (3 : ℕ) := by
    filter_upwards [eventually_ge_atTop (exp (10 : ℝ)), eventually_ge_atTop (22000 : ℝ),
      hdlim.eventually_ge_atTop (1e8 : ℝ), hclim.eventually_gt_atTop M] with t ht h22000 hd hM
    exact ⟨ht, h22000, hd, hM⟩
  obtain ⟨t, ht, h22000, hd, hM⟩ := hev.exists
  refine ⟨exp t, exp_le_exp.mpr ht, hM.trans_le ?_⟩
  have h := small_A_error_lower (exp t) (one_lt_exp_iff.mpr (by linarith))
    (by simpa only [log_exp] using h22000) hd
  simpa only [log_exp, C] using h

/-- The full scalar error bracket is not decreasing on the source range at A one.
Journal p. 1241 route audit. Neither original sealed leaf is refuted. -/
theorem small_A_not_antitone :
    ¬ AntitoneOn (fun N : ℝ => errorBracket 1 N (1 / 2)) (Set.Ici (exp (exp 10))) := by
  intro hanti
  obtain ⟨N, hN, hlt⟩ := small_A_unbounded (errorBracket 1 (exp (exp 10)) (1 / 2))
  have hle := hanti (Set.mem_Ici.mpr (le_refl (exp (exp (10 : ℝ)))))
    (Set.mem_Ici.mpr hN) hN
  exact (not_lt_of_ge hle) hlt


/-- The full scalar bracket tends to infinity at A one and epsilon one half.
Journal p. 1241 scalar route audit, using the uniform cubic lower bound. -/
theorem small_A_tendsto :
    Tendsto (fun N : ℝ => errorBracket 1 N (1 / 2)) atTop atTop := by
  let C : ℝ := invTw * (1 + (1 / 2 : ℝ)) / log (1 + (1 / 2 : ℝ)) *
      (0.053 * (1 + (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ)) * (4 / log 2)
  have hinv : 0 < invTw := by
    unfold invTw
    exact inv_pos.mpr (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos)
  have hlb : 0 < log (1 + (1 / 2 : ℝ)) := log_pos (by norm_num)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdexp : Tendsto (fun t : ℝ => √(exp t) / log (exp t) ^ ((1 : ℝ) + 1)) atTop atTop := by
    convert tendsto_exp_mul_div_rpow_atTop (2 : ℝ) (1 / 2) (by norm_num) using 1
    funext t
    rw [sqrt_eq_rpow, ← exp_mul, log_exp]
    congr 1 <;> ring
  have hdlim : Tendsto (fun N : ℝ => √N / log N ^ ((1 : ℝ) + 1)) atTop atTop := by
    refine (hdexp.comp tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    simp only [Function.comp_apply, exp_log hN]
  have hclim : Tendsto (fun N : ℝ => C * log N ^ (3 : ℕ)) atTop atTop :=
    ((tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp tendsto_log_atTop).const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hclim
  filter_upwards [eventually_gt_atTop (1 : ℝ), tendsto_log_atTop.eventually_ge_atTop (22000 : ℝ),
    hdlim.eventually_ge_atTop (1e8 : ℝ)] with N hN hL hD
  exact small_A_error_lower N hN hL hD

/-- Arbitrarily large scalar bracket values occur at even natural endpoints.
Journal p. 1241 route audit. The actual finite remainder is not part of the statement. -/
theorem small_A_even_witness (M : ℝ) : ∃ n : ℕ, Even n ∧ exp (exp 10) ≤ (n : ℝ) ∧
    M < errorBracket 1 n (1 / 2) := by
  have hnat : Tendsto (fun k : ℕ => (2 : ℝ) * k) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlim := small_A_tendsto.comp hnat
  have hev : ∀ᶠ k : ℕ in atTop, exp (exp 10) ≤ (2 : ℝ) * k ∧
      M < errorBracket 1 ((2 : ℝ) * k) (1 / 2) :=
    (hnat.eventually_ge_atTop (exp (exp (10 : ℝ)))).and (hlim.eventually_gt_atTop M)
  obtain ⟨k, hk, hM⟩ := hev.exists
  refine ⟨2 * k, ⟨k, by omega⟩, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hM

/-- An even natural endpoint refutes the proposed universal scalar transfer at A one.
Journal p. 1241 route audit. Neither sealed finite leaf is refuted. -/
theorem small_A_even_counterexample : ∃ n : ℕ, Even n ∧ exp (exp 10) ≤ (n : ℝ) ∧
    errorBracket 1 (exp (exp 10)) (1 / 2) < errorBracket 1 n (1 / 2) := by
  exact small_A_even_witness _

end
end LeanLab.BS2022GRH.EndpointGrowth339
#print axioms LeanLab.BS2022GRH.EndpointGrowth339.mbar_lower
#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_error_lower

#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_unbounded
#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_not_antitone

#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_tendsto

#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_even_witness

#print axioms LeanLab.BS2022GRH.EndpointGrowth339.small_A_even_counterexample
