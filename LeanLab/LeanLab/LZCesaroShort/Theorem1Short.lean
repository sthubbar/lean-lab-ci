import LeanLab.LZCesaroShort.Theorem2aShort
import LeanLab.LZCesaroShort.Lemma8Proof

/-!
# P0058 Theorem 1 as printed, under RH, for `2 ≤ H` and `2H(log N + 1) ≤ √N`

Lab proof, unit U-6112, CLOUD 20261020T0618Z-cloud36. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only, through `theorem2a_short` and `theorem2b_short`; Lemma 8 is the lab's
unconditional `lz_lemma8_proved`. Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 2, Theorem 1, and its proof p. 8, eq. (24) and (25): partial
summation removes the weight `e^{−n/N}` from Theorem 2 at the cost of the uniform eq. (2), and
Lemma 8 turns `2 Σ t_H(n − N)(ψ(n) − n)` into the zero sum `−2S`.

* `abel_bound`: summation by parts with a nondecreasing weight;
* `theorem1_short`: **under RH**, there are `K` and `N₀` with
  `‖Σ_{|n−N| ≤ H} R(n)(1 − |n − N|/H) − HN + (2/H) S‖ ≤ K (N (log(2N/H))² + H (log N)² log(2H))`
  for every `N ≥ N₀` and `2 ≤ H` with `2H(log N + 1) ≤ √N`; this is `Theorem1P` on that range.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- Summation by parts with a nondecreasing weight `f`. -/
lemma abel_bound (f g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hf : ∀ i, f i ≤ f (i + 1))
    {B₁ B₂ : ℝ} (hB₂ : 0 ≤ B₂) (h1 : |∑ i ∈ range n, g i| ≤ B₁)
    (h2 : ∀ i < n - 1, |∑ j ∈ range (i + 1), g j| ≤ B₂) :
    |∑ i ∈ range n, f i * g i| ≤ |f (n - 1)| * B₁ + (f (n - 1) - f 0) * B₂ := by
  have hp := Finset.sum_range_by_parts f g n
  simp only [smul_eq_mul] at hp
  rw [hp]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∑ i ∈ range (n - 1), |(f (i + 1) - f i) * ∑ j ∈ range (i + 1), g j|
        ≤ ∑ i ∈ range (n - 1), (f (i + 1) - f i) * B₂ := by
      refine sum_le_sum fun i hi => ?_
      rw [abs_mul, abs_of_nonneg (by linarith [hf i])]
      exact mul_le_mul_of_nonneg_left (h2 i (mem_range.mp hi)) (by linarith [hf i])
    refine this.trans (le_of_eq ?_)
    rw [← sum_mul, sum_range_sub (fun i => f i)]

lemma sum_Icc_eq_range (F : ℕ → ℝ) (a i : ℕ) :
    ∑ n ∈ Icc a (a + i), F n = ∑ j ∈ range (i + 1), F (a + j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ← ih, show a + (i + 1) = (a + i) + 1 by ring,
      Finset.sum_Icc_succ_top (by omega)]

lemma filter_eq_Icc {N H i : ℕ} (hHN : H ≤ N) (hi : i ≤ 2 * H) :
    (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + ((i : ℝ) - H))
      = Icc (N - H) (N - H + i) := by
  ext n
  simp only [mem_filter, mem_Icc]
  have e : ((N - H + i : ℕ) : ℝ) = N + ((i : ℝ) - H) := by push_cast [Nat.cast_sub hHN]; ring
  rw [← e, Nat.cast_le]
  omega

set_option maxHeartbeats 4000000 in
/-- **P0058 Theorem 1 as printed, under RH, for `2 ≤ H` and `2H(log N + 1) ≤ √N`.** -/
theorem theorem1_short (hRH : RiemannHypothesis) : ∃ K : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
        ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) := by
  obtain ⟨Ka, hKa, hTa⟩ := theorem2a_short hRH
  obtain ⟨Kb, hKb, hTb⟩ := theorem2b_short hRH
  obtain ⟨N8, K8, h8⟩ := lz_lemma8_proved
  refine ⟨8 * Kb + 16 * Ka + 6 * |K8|, max N8 (10 ^ 20), fun N H hN hH hHs => ?_⟩
  have hN20 : (10 : ℝ) ^ 20 ≤ N := by
    have : (10 ^ 20 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN20
  have hH1 : 1 ≤ H := by omega
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hsle : Real.sqrt (N : ℝ) ≤ N := by nlinarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hHN : (H : ℝ) < N := by nlinarith
  have hHNn : H ≤ N := by exact_mod_cast hHN.le
  -- the weighted sum `X = Σ w (R − (2ψ − n))`
  set b : ℕ → ℝ := fun j => Real.exp (-((N - H + j : ℕ) : ℝ) / N) * (R (N - H + j)
    - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ))) * w N H (N - H + j) with hb
  set f : ℕ → ℝ := fun j => Real.exp (((N - H + j : ℕ) : ℝ) / N) with hf
  set X : ℝ := ∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n)) with hX
  have hNH : N + H = (N - H) + 2 * H := by omega
  have hXeq : X = ∑ j ∈ range (2 * H + 1), f j * b j := by
    rw [hX, hNH, sum_Icc_eq_range]
    refine sum_congr rfl fun j _ => ?_
    simp only [hf, hb]
    have : Real.exp (((N - H + j : ℕ) : ℝ) / N) * Real.exp (-((N - H + j : ℕ) : ℝ) / N) = 1 := by
      rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
    calc w N H (N - H + j) * (R (N - H + j) - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ)))
        = (Real.exp (((N - H + j : ℕ) : ℝ) / N) * Real.exp (-((N - H + j : ℕ) : ℝ) / N))
          * (w N H (N - H + j) * (R (N - H + j) - (2 * ψ ((N - H + j : ℕ) : ℝ) - ((N - H + j : ℕ) : ℝ)))) := by
            rw [this, one_mul]
      _ = _ := by ring
  -- partial sums are `wsum`
  have hG : ∀ i ≤ 2 * H, ∑ j ∈ range (i + 1), b j = wsum N H ((i : ℝ) - H) := by
    intro i hi
    unfold wsum
    rw [filter_eq_Icc hHNn hi, sum_Icc_eq_range]
  have hGa : ∀ i < 2 * H + 1 - 1, |∑ j ∈ range (i + 1), b j| ≤ Ka * N * Real.log N ^ 2 * Real.log (2 * H) := by
    intro i hi
    rw [hG i (by omega)]
    refine hTa N H _ hN20 hH1 hHs ?_ ?_
    · have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · have : (i : ℝ) < 2 * H := by exact_mod_cast (by omega : i < 2 * H)
      linarith
  have hGb : |∑ j ∈ range (2 * H + 1), b j| ≤ Kb * N * Real.log (2 * N / H) ^ 2 := by
    rw [hG (2 * H) le_rfl]
    have : ((2 * H : ℕ) : ℝ) - H = H := by push_cast; ring
    rw [this]; exact hTb N H hN20 hH1 hHs
  have hfm : ∀ i, f i ≤ f (i + 1) := by
    intro i; simp only [hf]
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hN0.le
    exact_mod_cast (by omega : N - H + i ≤ N - H + (i + 1))
  have hlH0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hab := abel_bound f b (2 * H + 1) (by omega) hfm (by positivity) hGb hGa
  rw [← hXeq] at hab
  -- the weights
  have hf2 : f (2 * H + 1 - 1) ≤ Real.exp 2 := by
    simp only [hf]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hN0]
    have : ((N - H + (2 * H + 1 - 1) : ℕ) : ℝ) = N + H := by
      rw [show N - H + (2 * H + 1 - 1) = N + H by omega]; push_cast; ring
    rw [this]; linarith
  have hfd : f (2 * H + 1 - 1) - f 0 ≤ Real.exp 2 * (2 * H / N) := by
    simp only [hf]
    have e1 : ((N - H + (2 * H + 1 - 1) : ℕ) : ℝ) = N + H := by
      rw [show N - H + (2 * H + 1 - 1) = N + H by omega]; push_cast; ring
    have e0 : ((N - H + 0 : ℕ) : ℝ) = N - H := by push_cast [Nat.cast_sub hHNn]; ring
    rw [e1, e0]
    set u := ((N : ℝ) + H) / N
    set v := ((N : ℝ) - H) / N
    have huv : u - v = 2 * H / N := by simp only [u, v]; field_simp; ring
    have hu2 : u ≤ 2 := by simp only [u]; rw [div_le_iff₀ hN0]; linarith
    -- `e^u − e^v ≤ e^u (u − v)`
    have h := Real.add_one_le_exp (v - u)
    have hk : Real.exp u * Real.exp (v - u) = Real.exp v := by rw [← Real.exp_add]; ring_nf
    have : Real.exp u - Real.exp v ≤ Real.exp u * (u - v) := by nlinarith [Real.exp_pos u]
    calc Real.exp u - Real.exp v ≤ Real.exp u * (u - v) := this
      _ ≤ Real.exp 2 * (2 * H / N) := by
          rw [huv]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu2) (by positivity)
  have hf2abs : |f (2 * H + 1 - 1)| ≤ Real.exp 2 := by
    rw [abs_of_pos (by simp only [hf]; exact Real.exp_pos _)]; exact hf2
  have he2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  have hXb : |X| ≤ 8 * (Kb * N * Real.log (2 * N / H) ^ 2)
      + 8 * (2 * H / N) * (Ka * N * Real.log N ^ 2 * Real.log (2 * H)) := by
    have hB1 : 0 ≤ Kb * N * Real.log (2 * N / H) ^ 2 := by positivity
    have hlH : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith)
    have hB2 : 0 ≤ Ka * N * Real.log N ^ 2 * Real.log (2 * H) := by positivity
    calc |X| ≤ |f (2 * H + 1 - 1)| * (Kb * N * Real.log (2 * N / H) ^ 2)
          + (f (2 * H + 1 - 1) - f 0) * (Ka * N * Real.log N ^ 2 * Real.log (2 * H)) := hab
      _ ≤ 8 * (Kb * N * Real.log (2 * N / H) ^ 2)
          + 8 * (2 * H / N) * (Ka * N * Real.log N ^ 2 * Real.log (2 * H)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hf2abs.trans he2) hB1
          · apply mul_le_mul_of_nonneg_right _ hB2
            have : Real.exp 2 * (2 * H / N) ≤ 8 * (2 * H / N) :=
              mul_le_mul_of_nonneg_right he2 (by positivity)
            linarith
  -- Lemma 8 and the main term
  have hl8 := h8 N H (le_trans (le_max_left _ _) hN) hH hHNn
  set P : ℝ := ∑ n ∈ Icc (N - H) (N + H), ((H : ℝ) - |(n : ℝ) - N|) * (ψ n - n) with hP
  have hcesaro : cesaro N H = X + H * N + 2 / H * P := by
    have h1 := sum_w_mul_n hH1 hHNn
    unfold cesaro
    rw [hX, hP, ← h1, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [w_eq hH1]; field_simp; ring
  have hid : ((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H
      = (X : ℂ) + 2 / (H : ℂ) * ((P : ℂ) + ZH N H) := by
    rw [hcesaro]; push_cast; ring
  rw [hid]
  have hnorm2 : ‖2 / (H : ℂ) * ((P : ℂ) + ZH N H)‖ ≤ 2 * |K8| * N := by
    rw [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_natCast]
    have hP' : ‖((P : ℝ) : ℂ) + ZH N H‖ ≤ |K8| * H * N := by
      refine hl8.trans ?_
      have := le_abs_self K8
      have : 0 ≤ (H : ℝ) * N := by positivity
      nlinarith
    calc 2 / (H : ℝ) * ‖((P : ℝ) : ℂ) + ZH N H‖ ≤ 2 / H * (|K8| * H * N) :=
          mul_le_mul_of_nonneg_left hP' (by positivity)
      _ = 2 * |K8| * N := by field_simp
  have hnX : ‖((X : ℝ) : ℂ)‖ = |X| := by rw [Complex.norm_real, Real.norm_eq_abs]
  -- final comparison
  have hl2 := Real.log_two_gt_d9
  have ha : Real.log 2 ≤ Real.log (2 * N / H) := by
    apply Real.log_le_log (by norm_num); rw [le_div_iff₀ hH0]; linarith
  have hNa : (N : ℝ) ≤ 3 * (N * Real.log (2 * (N : ℝ) / H) ^ 2) := by
    have : (1 : ℝ) / 3 ≤ Real.log (2 * N / H) ^ 2 := by nlinarith
    nlinarith
  have hterm2 : 8 * (2 * H / N) * (Ka * N * Real.log N ^ 2 * Real.log (2 * H))
      = 16 * Ka * (H * Real.log N ^ 2 * Real.log (2 * H)) := by field_simp; ring
  have hA : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2 := by positivity
  have hB : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by
    have : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
    positivity
  have hK8 : 0 ≤ |K8| := abs_nonneg _
  calc ‖((X : ℝ) : ℂ) + 2 / (H : ℂ) * ((P : ℂ) + ZH N H)‖
      ≤ ‖((X : ℝ) : ℂ)‖ + ‖2 / (H : ℂ) * ((P : ℂ) + ZH N H)‖ := norm_add_le _ _
    _ ≤ (8 * (Kb * N * Real.log (2 * N / H) ^ 2) + 16 * Ka * (H * Real.log N ^ 2 * Real.log (2 * H)))
        + 2 * |K8| * N := by rw [hnX, ← hterm2]; linarith
    _ ≤ (8 * Kb + 16 * Ka + 6 * |K8|) * (N * Real.log (2 * (N : ℝ) / H) ^ 2
        + H * Real.log N ^ 2 * Real.log (2 * H)) := by
        have e : Kb * N * Real.log (2 * N / H) ^ 2 = Kb * (N * Real.log (2 * (N : ℝ) / H) ^ 2) := by ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hNa (show (0 : ℝ) ≤ 2 * |K8| by positivity)]

/-- `Theorem1P` holds under RH on the range `2 ≤ H`, `2H(log N + 1) ≤ √N`, `N` large. -/
theorem theorem1P_short (hRH : RiemannHypothesis) : ∃ K : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → 2 * H * (Real.log N + 1) ≤ Real.sqrt N →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
        ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) :=
  theorem1_short hRH

end LeanLab.LZCesaroShort
