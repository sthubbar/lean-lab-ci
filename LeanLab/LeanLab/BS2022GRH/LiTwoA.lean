/-
P0021, Bordignon-Starichkova 2022, shared input `li 2 ≤ 1.046`, part A: the two pointwise
bounds on the regular part `gli t = 1 / log t - 1 / (t - 1)` of `1 / log t`.

* `log_ge_pade`: `3 (t - 1)(t + 1) / (t² + 4t + 1) ≤ log t` for `t ≥ 1`, the [2/2] Padé
  lower bound; the derivative of the difference is `(t - 1)⁴ / (t (t² + 4t + 1)²) ≥ 0`.
* `log_ge_low`: `-2 (1 - t) / (t (3 - t)) ≤ log t` for `0 < t ≤ 1`; the derivative of the
  difference is `(t - 1)² (t - 6) / (t² (3 - t)²) ≤ 0`.
* `gli_le_right`: `gli t ≤ (t + 2) / (3 (t + 1))` for `t > 1`.
* `gli_le_left`: `gli t ≤ 1 - t / 2` for `0 < t < 1`.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1154. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.LiPV

namespace LeanLab.BS2022GRH.LiTwo
open Real Set

/-- The difference `log t - 3 (t² - 1) / (t² + 4t + 1)`. -/
noncomputable def dA (t : ℝ) : ℝ := log t - 3 * (t ^ 2 - 1) / (t ^ 2 + 4 * t + 1)

lemma dA_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt dA ((t - 1) ^ 4 / (t * (t ^ 2 + 4 * t + 1) ^ 2)) t := by
  have hden : t ^ 2 + 4 * t + 1 ≠ 0 := by positivity
  have hn : HasDerivAt (fun x : ℝ => 3 * (x ^ 2 - 1)) (3 * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).sub_const 1).const_mul 3
    simpa using this
  have hd : HasDerivAt (fun x : ℝ => x ^ 2 + 4 * x + 1) (2 * t + 4) t := by
    have := (((hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 4)).add_const 1)
    simpa using this
  have h : HasDerivAt dA _ t := (Real.hasDerivAt_log ht.ne').sub (hn.div hd hden)
  refine h.congr_deriv ?_
  field_simp
  ring

lemma log_ge_pade {t : ℝ} (ht : 1 ≤ t) : 3 * (t ^ 2 - 1) / (t ^ 2 + 4 * t + 1) ≤ log t := by
  have hmono : MonotoneOn dA (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
      exact (dA_hasDerivAt hx0).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (dA_hasDerivAt (lt_trans one_pos hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans one_pos hx
      rw [(dA_hasDerivAt hx0).deriv]
      positivity
  have h := hmono (show (1:ℝ) ∈ Ici 1 from Set.mem_Ici.mpr le_rfl) ht ht
  have h1 : dA 1 = 0 := by simp [dA]
  unfold dA at h h1
  linarith

/-- The difference `log t + 2 (1 - t) / (t (3 - t))`. -/
noncomputable def dB (t : ℝ) : ℝ := log t + 2 * (1 - t) / (t * (3 - t))

lemma dB_hasDerivAt {t : ℝ} (ht : 0 < t) (ht3 : t < 3) :
    HasDerivAt dB ((t - 1) ^ 2 * (t - 6) / (t ^ 2 * (3 - t) ^ 2)) t := by
  have hden : t * (3 - t) ≠ 0 := by
    have : 0 < 3 - t := by linarith
    positivity
  have h3 : (3 - t) ≠ 0 := by linarith
  have hn : HasDerivAt (fun x : ℝ => 2 * (1 - x)) (2 * (-1)) t := by
    have := ((hasDerivAt_id t).const_sub 1).const_mul 2
    simpa using this
  have hd : HasDerivAt (fun x : ℝ => x * (3 - x)) (1 * (3 - t) + t * (-1)) t :=
    (hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_sub 3)
  have h : HasDerivAt dB _ t := (Real.hasDerivAt_log ht.ne').add (hn.div hd hden)
  refine h.congr_deriv ?_
  field_simp
  ring

lemma log_ge_low {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : -(2 * (1 - t) / (t * (3 - t))) ≤ log t := by
  have hanti : AntitoneOn dB (Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · intro x hx
      exact (dB_hasDerivAt hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (dB_hasDerivAt hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(dB_hasDerivAt hx.1 (by linarith [hx.2])).deriv]
      have h6 : x - 6 ≤ 0 := by linarith [hx.2]
      have hd : 0 ≤ x ^ 2 * (3 - x) ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h6) hd
  have h := hanti ⟨ht, ht1⟩ ⟨one_pos, le_rfl⟩ ht1
  have h1 : dB 1 = 0 := by simp [dB]
  unfold dB at h h1
  linarith

/-- On `(1, ∞)`: `gli t ≤ (t + 2) / (3 (t + 1)) = 1/3 + 1 / (3 (t + 1))`. -/
lemma gli_le_right {t : ℝ} (ht : 1 < t) : gli t ≤ (t + 2) / (3 * (t + 1)) := by
  have hR : 0 < 3 * (t ^ 2 - 1) / (t ^ 2 + 4 * t + 1) := by
    have : 0 < t ^ 2 - 1 := by nlinarith
    positivity
  have hL := log_ge_pade ht.le
  have h1 : 1 / log t ≤ 1 / (3 * (t ^ 2 - 1) / (t ^ 2 + 4 * t + 1)) :=
    one_div_le_one_div_of_le hR hL
  have hs : t - 1 ≠ 0 := by linarith
  have hs1 : t + 1 ≠ 0 := by linarith
  have hq : t ^ 2 + 4 * t + 1 ≠ 0 := by positivity
  have e : 1 / (3 * (t ^ 2 - 1) / (t ^ 2 + 4 * t + 1)) - 1 / (t - 1)
      = (t + 2) / (3 * (t + 1)) := by
    have : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
    rw [this]
    field_simp
    ring
  unfold gli
  linarith

/-- On `(0, 1)`: `gli t ≤ 1 - t / 2`. -/
lemma gli_le_left {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : gli t ≤ 1 - t / 2 := by
  have hL := log_ge_low ht ht1.le
  have hlog : log t < 0 := log_neg ht ht1
  have h1 : 1 / log t ≤ 1 / (-(2 * (1 - t) / (t * (3 - t)))) :=
    one_div_le_one_div_of_neg_of_le hlog hL
  have hs : 1 - t ≠ 0 := by linarith
  have hs' : t - 1 ≠ 0 := by linarith
  have h3 : 3 - t ≠ 0 := by linarith
  have e : 1 / (-(2 * (1 - t) / (t * (3 - t)))) - 1 / (t - 1) = 1 - t / 2 := by
    field_simp
    ring
  unfold gli
  linarith

#print axioms log_ge_pade
#print axioms log_ge_low
#print axioms gli_le_right
#print axioms gli_le_left

end LeanLab.BS2022GRH.LiTwo
