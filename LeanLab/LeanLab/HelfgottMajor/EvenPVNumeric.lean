import Mathlib

/-!
# Numeric inequalities for the even case of the explicit Polya Vinogradov bound

AI wrote this Lean code (Claude). It proves three pure real inequalities with
`π`, `log` and `sqrt`, used by the even primitive character case of an explicit
Polya Vinogradov type bound (completion of a character sum by Gauss sums with a
Fejer type smoothing):

* `even_pv_min_le`: the minimum over `H` of `q / H + (4 / π ^ 2) sqrt q log H`.
* `even_pv_small`: the trivial completion bound suffices for `2 ≤ q ≤ 128`.
* `even_pv_large`: the smoothed bound with `L = Nat.sqrt q + 1` suffices for `128 ≤ q`.

This is standard mathematics, nothing new. The binary Goldbach conjecture is OPEN;
nothing here proves it.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123

open Real

theorem inv_pi_gt : (0.3183 : ℝ) < 1 / π := by
  rw [lt_div_iff₀ pi_pos]
  linarith [pi_lt_d4]

theorem inv_pi_lt : 1 / π < (0.3184 : ℝ) := by
  rw [div_lt_iff₀ pi_pos]
  linarith [pi_gt_d4]

theorem log_pi_sq_div_four_ge : (0.839 : ℝ) ≤ log (π ^ 2 / 4) := by
  have hπ := pi_pos
  have h := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 4) hπ)
  rw [Real.log_div (by norm_num) hπ.ne'] at h
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have e : log (π ^ 2 / 4) = 2 * log π - 2 * log 2 := by
    rw [Real.log_div (pow_ne_zero 2 hπ.ne') (by norm_num), Real.log_pow, h4]
    norm_num
  have hu := inv_pi_lt
  have h8 : 4 / π = 4 * (1 / π) := by ring
  rw [e]
  linarith [log_two_gt_d9]

theorem c1_ge : (0.7451 : ℝ) ≤ 4 * (1 / π) ^ 2 * (1 + log (π ^ 2 / 4)) := by
  have hu := inv_pi_gt
  have hL := log_pi_sq_div_four_ge
  have hu2 : (0.1013 : ℝ) ≤ (1 / π) ^ 2 := by nlinarith
  have h := mul_le_mul hu2 (by linarith : (1.839 : ℝ) ≤ 1 + log (π ^ 2 / 4))
    (by norm_num) (by positivity)
  nlinarith [h]

theorem even_pv_min_le {q : ℕ} (hq : 2 ≤ q) (H : ℝ) (hH : 1 ≤ H) :
    sqrt q * (1 / 4 + 4 / π ^ 2 * (1 + log (π ^ 2 / 4 * sqrt q))) ≤
      (q : ℝ) / H + 4 / π ^ 2 * sqrt q * log H + 1 / 4 * sqrt q := by
  have hQ2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have ht : 0 < sqrt q := Real.sqrt_pos.mpr hQ0
  have hsq : (q : ℝ) = sqrt q * sqrt q := (Real.mul_self_sqrt hQ0.le).symm
  have hπ := pi_pos
  have hH0 : 0 < H := by linarith
  have hHs : 0 < π ^ 2 / 4 * sqrt q := by positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos hHs hH0)
  rw [Real.log_div hHs.ne' hH0.ne'] at h1
  have h2 : 4 / π ^ 2 * sqrt q * (log (π ^ 2 / 4 * sqrt q) - log H) ≤
      4 / π ^ 2 * sqrt q * (π ^ 2 / 4 * sqrt q / H - 1) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : ∀ t : ℝ, 4 / π ^ 2 * t * (π ^ 2 / 4 * t / H - 1) =
      t * t / H - 4 / π ^ 2 * t := by
    intro t
    field_simp
  have h3' := h3 (sqrt q)
  rw [← hsq] at h3'
  have key : sqrt q * (1 / 4 + 4 / π ^ 2 * (1 + log (π ^ 2 / 4 * sqrt q))) =
      4 / π ^ 2 * sqrt q * (log (π ^ 2 / 4 * sqrt q) - log H) +
        (4 / π ^ 2 * sqrt q + 4 / π ^ 2 * sqrt q * log H + 1 / 4 * sqrt q) := by ring
  rw [key]
  linarith [h2, h3']

theorem even_pv_small_aux (t Q Lq : ℝ) (ht : 0 < t) (hQ : Q = t * t) (hQ2 : 2 ≤ Q)
    (hLq0 : 0 ≤ Lq) (hLq : Lq ≤ 7 * log 2) :
    1 / (2 * t) * (2 * ((Q / π) * (1 + (Lq - log 2)) + π * (Q + 2) / 24)) ≤
      t * (1 / 4 + 4 / π ^ 2 * (1 + (log (π ^ 2 / 4) + Lq / 2))) := by
  subst hQ
  have hπ := pi_pos
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / π := ⟨_, rfl⟩
  have hu1 : 0.3183 < u := by rw [hu]; exact inv_pi_gt
  have hu2 : u < 0.3184 := by rw [hu]; exact inv_pi_lt
  have hC : 0.7451 ≤ 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) := by rw [hu]; exact c1_ge
  have hπ1 := pi_gt_d4
  have hπ2 := pi_lt_d4
  have l1 := log_two_gt_d9
  have l2 := log_two_lt_d9
  have e1 : 1 / (2 * t) * (2 * ((t * t / π) * (1 + (Lq - log 2)) + π * (t * t + 2) / 24)) =
      t * (u * (1 + Lq - log 2) + π / 24) + π / 12 * (1 / t) := by
    rw [hu]; field_simp; ring
  have e2 : t * (1 / 4 + 4 / π ^ 2 * (1 + (log (π ^ 2 / 4) + Lq / 2))) =
      t * (1 / 4 + 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) + 2 * u ^ 2 * Lq) := by
    rw [hu]; field_simp; ring
  rw [e1, e2]
  have hv : 1 / t ≤ t / 2 := by rw [div_le_iff₀ ht]; nlinarith
  have h1 : π / 12 * (1 / t) ≤ π / 12 * (t / 2) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  have hA : u - 2 * u ^ 2 ≤ 0.1158 := by nlinarith
  have hA0 : 0 ≤ u - 2 * u ^ 2 := by nlinarith
  have hLq' : Lq ≤ 4.8521 := by linarith
  have hALq : (u - 2 * u ^ 2) * Lq ≤ 0.1158 * 4.8521 :=
    mul_le_mul hA hLq' hLq0 (by norm_num)
  have h5 : u * (1 - log 2) ≤ 0.3184 * 0.3068529 :=
    mul_le_mul hu2.le (by linarith) (by linarith) (by norm_num)
  have B : u * (1 + Lq - log 2) + π / 24 + π / 24 ≤
      1 / 4 + 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) + 2 * u ^ 2 * Lq := by
    nlinarith [hALq, h5, hC]
  have h2 := mul_le_mul_of_nonneg_left B ht.le
  nlinarith [h1, h2]

theorem even_pv_small {q : ℕ} (hq : 2 ≤ q) (hq' : q ≤ 128) :
    1 / (2 * sqrt q) * (2 * (((q : ℝ) / π) * (1 + log ((q : ℝ) / 2)) + π * ((q : ℝ) + 2) / 24)) ≤
      sqrt q * (1 / 4 + 4 / π ^ 2 * (1 + log (π ^ 2 / 4 * sqrt q))) := by
  have hQ2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ128 : (q : ℝ) ≤ 128 := by exact_mod_cast hq'
  have hQ0 : (0 : ℝ) < q := by linarith
  have ht : 0 < sqrt q := Real.sqrt_pos.mpr hQ0
  have hsq : (q : ℝ) = sqrt q * sqrt q := (Real.mul_self_sqrt hQ0.le).symm
  have hπ := pi_pos
  have hlt : log (sqrt q) = log q / 2 := Real.log_sqrt hQ0.le
  rw [Real.log_div (x := (q : ℝ)) (y := 2) hQ0.ne' two_ne_zero,
    Real.log_mul (x := π ^ 2 / 4) (y := sqrt q) (by positivity) ht.ne', hlt]
  refine even_pv_small_aux (sqrt q) q (log q) ht hsq hQ2 (Real.log_nonneg (by linarith)) ?_
  have h128 : log (128 : ℝ) = 7 * log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  rw [← h128]
  exact Real.log_le_log hQ0 hQ128

theorem even_pv_large_aux (t Q m Lt Lm : ℝ) (hQ : Q = t * t) (ht : 11.3 ≤ t)
    (hm1 : t < m) (hm2 : m ≤ t + 1) (hLt : 2.426 ≤ Lt) (hLm : Lm ≤ Lt + 1 / t) :
    (m - 1) / 2 + 1 / (2 * t) *
      (2 * ((Q / π) * (1 + Lm) + π * m * (m + 1) / (6 * Q) + Q ^ 2 / (4 * m * m))) ≤
      t * (1 / 4 + 4 / π ^ 2 * (1 + (log (π ^ 2 / 4) + Lt))) := by
  subst hQ
  have hπ := pi_pos
  have ht0 : 0 < t := by linarith
  have hm0 : 0 < m := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / π := ⟨_, rfl⟩
  have hu1 : 0.3183 < u := by rw [hu]; exact inv_pi_gt
  have hu2 : u < 0.3184 := by rw [hu]; exact inv_pi_lt
  have hu0 : 0 < u := by linarith
  have hC : 0.7451 ≤ 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) := by rw [hu]; exact c1_ge
  have hπ2 := pi_lt_d4
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / t := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw1 : w ≤ 0.0885 := by rw [hw, div_le_iff₀ ht0]; linarith
  have e : (m - 1) / 2 + 1 / (2 * t) *
      (2 * ((t * t / π) * (1 + Lm) + π * m * (m + 1) / (6 * (t * t)) +
        (t * t) ^ 2 / (4 * m * m))) =
      (m - 1) / 2 + t * (u * (1 + Lm)) + π * (m * (m + 1)) * (w * w * w) / 6 +
        (t * t) ^ 2 / (4 * m * m) / t := by
    rw [hu, hw]; field_simp; ring
  have e2 : t * (1 / 4 + 4 / π ^ 2 * (1 + (log (π ^ 2 / 4) + Lt))) =
      t * (1 / 4 + 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) + 4 * u ^ 2 * Lt) := by
    rw [hu]; field_simp; ring
  rw [e, e2]
  have b1 : Lm ≤ Lt + w := by rw [hw]; exact hLm
  have b2 : t * (u * (1 + Lm)) ≤ t * (u * (1 + Lt + w)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hu0.le) ht0.le
  have b3a : m * (m + 1) ≤ (t + 1) * (t + 2) :=
    mul_le_mul hm2 (by linarith) (by linarith) (by linarith)
  have b3 : π * (m * (m + 1)) * (w * w * w) / 6 ≤ π * ((t + 1) * (t + 2)) * (w * w * w) / 6 := by
    have h := mul_le_mul_of_nonneg_left b3a hπ.le
    have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg hw0.le hw0.le) hw0.le)
    linarith
  have b3e : π * ((t + 1) * (t + 2)) * (w * w * w) / 6 =
      t * (π * ((1 + w) * (1 + 2 * w) * (w * w)) / 6) := by
    rw [hw]; field_simp
  have b4 : (t * t) ^ 2 / (4 * m * m) / t ≤ t * (1 / 4) := by
    rw [div_le_iff₀ ht0, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hm0) hm0)]
    have hmm : t * t ≤ m * m := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hmm (mul_nonneg ht0.le ht0.le)]
  have p1 : (1 + w) * (1 + 2 * w) ≤ 1.0885 * 1.177 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have p2 : w * w ≤ 0.0885 * 0.0885 := mul_le_mul hw1 hw1 hw0.le (by norm_num)
  have p3 : (1 + w) * (1 + 2 * w) * (w * w) ≤ 1.0885 * 1.177 * (0.0885 * 0.0885) :=
    mul_le_mul p1 p2 (mul_nonneg hw0.le hw0.le) (by norm_num)
  have p4 : π * ((1 + w) * (1 + 2 * w) * (w * w)) ≤
      3.1416 * (1.0885 * 1.177 * (0.0885 * 0.0885)) :=
    mul_le_mul hπ2.le p3
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hw0.le hw0.le))
      (by norm_num)
  have p5 : u * w ≤ 0.3184 * 0.0885 := mul_le_mul hu2.le hw1 hw0.le (by norm_num)
  have hD : 0.0869 ≤ 4 * u ^ 2 - u := by nlinarith
  have p6 : 0.0869 * 2.426 ≤ (4 * u ^ 2 - u) * Lt :=
    mul_le_mul hD hLt (by norm_num) (by linarith)
  have B : 1 / 2 + u * (1 + Lt + w) + π * ((1 + w) * (1 + 2 * w) * (w * w)) / 6 + 1 / 4 ≤
      1 / 4 + 4 * u ^ 2 * (1 + log (π ^ 2 / 4)) + 4 * u ^ 2 * Lt := by
    have p6' : (4 * u ^ 2 - u) * Lt = 4 * u ^ 2 * Lt - u * Lt := by ring
    have hexpB : u * (1 + Lt + w) = u + u * Lt + u * w := by ring
    rw [hexpB]
    rw [p6'] at p6
    linarith only [p4, p5, p6, hC, hu2]
  have h2 := mul_le_mul_of_nonneg_left B ht0.le
  have hT1 : (m - 1) / 2 ≤ t * (1 / 2) := by linarith
  have hexp : t * (1 / 2 + u * (1 + Lt + w) + π * ((1 + w) * (1 + 2 * w) * (w * w)) / 6 + 1 / 4) =
      t * (1 / 2) + t * (u * (1 + Lt + w)) + t * (π * ((1 + w) * (1 + 2 * w) * (w * w)) / 6) +
        t * (1 / 4) := by ring
  rw [hexp] at h2
  rw [b3e] at b3
  linarith only [h2, b2, b3, b4, hT1]

theorem even_pv_large {q : ℕ} (hq : 128 ≤ q) :
    (((Nat.sqrt q + 1 : ℕ) : ℝ) - 1) / 2 + 1 / (2 * sqrt q) *
      (2 * (((q : ℝ) / π) * (1 + log ((Nat.sqrt q + 1 : ℕ) : ℝ)) +
        π * ((Nat.sqrt q + 1 : ℕ) : ℝ) * (((Nat.sqrt q + 1 : ℕ) : ℝ) + 1) / (6 * q) +
        (q : ℝ) ^ 2 / (4 * ((Nat.sqrt q + 1 : ℕ) : ℝ) * ((Nat.sqrt q + 1 : ℕ) : ℝ)))) ≤
      sqrt q * (1 / 4 + 4 / π ^ 2 * (1 + log (π ^ 2 / 4 * sqrt q))) := by
  have hQ : (128 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have ht : 0 < sqrt q := Real.sqrt_pos.mpr hQ0
  have hsq : (q : ℝ) = sqrt q * sqrt q := (Real.mul_self_sqrt hQ0.le).symm
  have hπ := pi_pos
  have ht11 : 11.3 ≤ sqrt q := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h') ht]
  have hmeq : ((Nat.sqrt q + 1 : ℕ) : ℝ) = (Nat.sqrt q : ℝ) + 1 := Nat.cast_succ _
  have hm1 : sqrt q < ((Nat.sqrt q + 1 : ℕ) : ℝ) := by
    rw [hmeq]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hm2 : ((Nat.sqrt q + 1 : ℕ) : ℝ) ≤ sqrt q + 1 := by
    rw [hmeq]; linarith [Real.nat_sqrt_le_real_sqrt (a := q)]
  have hLt : 2.426 ≤ log (sqrt q) := by
    rw [Real.log_sqrt hQ0.le]
    have h128 : log (128 : ℝ) = 7 * log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have hle : log (128 : ℝ) ≤ log q := Real.log_le_log (by norm_num) hQ
    linarith [log_two_gt_d9]
  have hLm : log ((Nat.sqrt q + 1 : ℕ) : ℝ) ≤ log (sqrt q) + 1 / sqrt q := by
    have h1 : log ((Nat.sqrt q + 1 : ℕ) : ℝ) ≤ log (sqrt q + 1) :=
      Real.log_le_log (by linarith) hm2
    have hp : 0 < sqrt q + 1 := by linarith
    have h2 := Real.log_le_sub_one_of_pos (div_pos hp ht)
    rw [Real.log_div hp.ne' ht.ne'] at h2
    have h3 : (sqrt q + 1) / sqrt q - 1 = 1 / sqrt q := by
      rw [add_div, div_self ht.ne']; ring
    linarith
  rw [Real.log_mul (x := π ^ 2 / 4) (y := sqrt q) (by positivity) ht.ne']
  exact even_pv_large_aux (sqrt q) q _ _ _ hsq ht11 hm1 hm2 hLt hLm

end LeanLab.HelfgottMajor.PolyaVinogradov123
