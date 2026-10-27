/-
P0071 Languasco-Perelli 1996, Corollary 2 from Theorem 4, page 352, in the OneDrive encoding.
PC run 20261020T0503Z-11094, unit U-1179. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; GRH and GMC are unproved hypotheses.

The paper: Theorem 4 with `ξ = 1/(qQ)`, `Q = X^θ/2`, gives Corollary 2 at once, since then
`W = Xξ/2 = X^{1-θ}/q`, so GMC(θ; ξ) is GMC(θ), and
`X^{1/2+ε}(1 + (X/(qQ))^{1/2}) ≤ 2 X^{1+ε}/(qQ)^{1/2}` because `qQ ≤ Q² ≤ X/4`.
The repo encoding proved the same as `cor2_of_thm4`, now in LanguascoPerelli1996/B; this file
proves it for the encoding the other folders import.
* `xiQ`: `ξ = 1/(qQ)` where it lies in `(0, 1/2]`, else `1/2`, so GMC(θ; ξ)'s range condition holds.
* `gmcxi_of_gmc`: GMC(θ) implies GMC(θ; ξ).
* `corollary2_of_theorem4`: Corollary 2 CONDITIONAL ON Theorem 4 only.
-/
import LeanLab.LanguascoPerelli1996.Statements

namespace LeanLab.LanguascoPerelli1996
open Real

noncomputable section

/-- `ξ(X, q) = 1/(qQ)`, `Q = X^θ/2`, where this lies in `(0, 1/2]`; `1/2` otherwise. -/
def xiQ (θ : ℝ) (X : ℝ) (q : ℕ) : ℝ :=
  if 0 < 1 / (q * (X ^ θ / 2)) ∧ 1 / (q * (X ^ θ / 2)) ≤ 1 / 2 then 1 / (q * (X ^ θ / 2)) else 1 / 2

lemma xiQ_range (θ X : ℝ) (q : ℕ) : 0 < xiQ θ X q ∧ xiQ θ X q ≤ 1 / 2 := by
  unfold xiQ; split_ifs with h
  · exact h
  · norm_num

lemma xiQ_eq {θ X : ℝ} {q : ℕ} (hq : 1 ≤ q) (hX : 4 ≤ X ^ θ) :
    xiQ θ X q = 1 / (q * (X ^ θ / 2)) := by
  unfold xiQ
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) * (X ^ θ / 2) := by positivity
  have h2 : 2 ≤ (q : ℝ) * (X ^ θ / 2) := by nlinarith
  rw [if_pos ⟨by positivity, by rw [div_le_div_iff₀ hpos (by norm_num)]; linarith⟩]

/-- GMC(θ) gives GMC(θ; ξ) for `ξ = xiQ θ`, since `Xξ/2 = X^{1-θ}/q` for large `X`. -/
theorem gmcxi_of_gmc {θ : ℝ} (hθ : 0 < θ) (h : GMC θ) : GMCxi θ (xiQ θ) := by
  refine ⟨h.1, xiQ_range θ, fun ε hε => ?_⟩
  obtain ⟨C, X0, hC⟩ := h.2 ε hε
  refine ⟨C, max X0 (4 ^ (1 / θ)), fun X hX q _ hq a ha T hT1 hT2 => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have h4 : 4 ^ (1 / θ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) h4
  have hXθ : 4 ≤ X ^ θ := by
    have := Real.rpow_le_rpow (by positivity) h4 hθ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one] at this
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  rw [xiQ_eq hq1 hXθ] at hT1
  apply hC X hX0 q hq a ha T _ hT2
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hXθpos : 0 < X ^ θ := by positivity
  have e : X * (1 / (q * (X ^ θ / 2))) / 2 = X ^ (1 - θ) / q := by
    rw [Real.rpow_sub hXpos, Real.rpow_one]; field_simp
  rw [e] at hT1; exact hT1

/-- **Corollary 2**, p. 352, CONDITIONAL ON Theorem 4 only. -/
theorem corollary2_of_theorem4 (h4 : Theorem4) : Corollary2 := by
  intro θ hθ hθ2 hG ε hε
  obtain ⟨C, X0, hC⟩ := h4 θ hθ hθ2 (xiQ θ) (gmcxi_of_gmc hθ hG) ε hε
  refine ⟨2 * max C 0, max (max X0 (4 ^ (1 / θ))) 1, fun X hX q _ hq a ha η hη => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have h4' : 4 ^ (1 / θ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hXθ : 4 ≤ X ^ θ := by
    have := Real.rpow_le_rpow (by positivity) h4' hθ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ.ne', Real.rpow_one] at this
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hXθpos : 0 < X ^ θ := by positivity
  set Q := X ^ θ / 2 with hQ
  have hQpos : 0 < Q := by positivity
  have hqθ : (q : ℝ) ≤ X ^ θ := le_trans hq (by linarith)
  have hxi := xiQ_eq (θ := θ) hq1 hXθ
  have hb := hC X hX0 q hqθ a ha η (by rw [hxi]; exact hη)
  rw [hxi] at hb
  -- `qQ ≤ Q² ≤ X/4`
  have hqQ : (q : ℝ) * Q ≤ X := by
    have h1 : (q : ℝ) * Q ≤ Q * Q := mul_le_mul_of_nonneg_right hq hQpos.le
    have h2 : Q * Q = X ^ (2 * θ) / 4 := by
      have e : X ^ (2 * θ) = (X ^ θ) ^ 2 := by
        rw [mul_comm, Real.rpow_mul hXpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
      rw [e, hQ]; ring
    have h3 : X ^ (2 * θ) ≤ X := by
      calc X ^ (2 * θ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    linarith
  set P := (q : ℝ) * Q with hP
  have hPpos : 0 < P := by positivity
  have hsP : 0 < P ^ (1 / 2 : ℝ) := by positivity
  -- `(X/P)^{1/2} = X^{1/2}/P^{1/2}`
  have hxi1 : X * (1 / P) = X / P := by ring
  rw [hxi1] at hb
  have hsplit : (X / P) ^ (1 / 2 : ℝ) = X ^ (1 / 2 : ℝ) / P ^ (1 / 2 : ℝ) :=
    Real.div_rpow hXpos.le hPpos.le _
  have hXe : X ^ (1 / 2 + ε) * X ^ (1 / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_add hXpos]; ring_nf
  have hPle : P ^ (1 / 2 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hPpos.le hqQ (by norm_num)
  have hterm1 : X ^ (1 / 2 + ε) ≤ X ^ (1 + ε) / P ^ (1 / 2 : ℝ) := by
    rw [le_div_iff₀ hsP, ← hXe]
    exact mul_le_mul_of_nonneg_left hPle (by positivity)
  have hterm2 : X ^ (1 / 2 + ε) * (X / P) ^ (1 / 2 : ℝ) = X ^ (1 + ε) / P ^ (1 / 2 : ℝ) := by
    rw [hsplit, ← hXe]; ring
  have hsum : X ^ (1 / 2 + ε) * (1 + (X / P) ^ (1 / 2 : ℝ)) ≤ 2 * (X ^ (1 + ε) / P ^ (1 / 2 : ℝ)) := by
    rw [mul_add, mul_one, hterm2]; linarith
  have hnn : 0 ≤ X ^ (1 / 2 + ε) * (1 + (X / P) ^ (1 / 2 : ℝ)) := by positivity
  calc ‖R X η q a‖ ≤ C * X ^ (1 / 2 + ε) * (1 + (X / P) ^ (1 / 2 : ℝ)) := hb
    _ ≤ max C 0 * (X ^ (1 / 2 + ε) * (1 + (X / P) ^ (1 / 2 : ℝ))) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ ≤ max C 0 * (2 * (X ^ (1 + ε) / P ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (le_max_right _ _)
    _ = 2 * max C 0 * X ^ (1 + ε) / P ^ (1 / 2 : ℝ) := by ring

end

end LeanLab.LanguascoPerelli1996
