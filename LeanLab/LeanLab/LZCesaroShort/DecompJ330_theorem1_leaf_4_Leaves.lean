import LeanLab.LZCesaroShort.DecompJ330

/-!
AI wrote the Lean code. Binary Goldbach is open.
Source: arXiv:1606.00869v2, Languasco and Zaccagnini, page 2 Theorem 1 and its page 8 proof,
equations 24 and 25: the weighted sum `Σ w (R - (2ψ - n))` is recovered from the partial sums
`wsum` by partial summation against the nondecreasing weight `e^{n/N}`.

S99 feed1122 split of `theorem1_leaf_4`. No new sorry is introduced here: the leaves are the
existing `theorem1_leaf_1`, which is proved from `theorem2a_full`, and `theorem1_leaf_2`, which
still carries the legacy logarithm `log (2 N^2 / H)` and stays open in `DecompJ330`.
The original file keeps its sorry, because this file must import it.
-/

namespace LeanLab.LZCesaroShort

open Complex MeasureTheory Finset

open scoped ArithmeticFunction.vonMangoldt Chebyshev

set_option maxHeartbeats 4000000 in
/-- arXiv:1606.00869v2 page 8, equations 24 and 25: partial summation of `theorem1_leaf_1` and
`theorem1_leaf_2` against `e^{n/N}`, with `e^{(N+H)/N} ≤ e^2 ≤ 8` and
`e^{(N+H)/N} - e^{(N-H)/N} ≤ 8 · 2H/N`. Exactly the statement of `theorem1_leaf_4`. -/
theorem theorem1_leaf_4_from_leaves (hRH : RiemannHypothesis) : ∃ Kd : ℝ, ∃ N0d : ℕ, ∀ N H : ℕ, N0d ≤ N → 2 ≤ H → H ≤ N →
  |∑ n ∈ Icc (N - H) (N + H), w N H n * (R n - (2 * ψ (n : ℝ) - n))| ≤ Kd * (N * Real.log (2 * (N : ℝ) ^ 2 / H) + H * Real.log N ^ 2 * Real.log (2 * H)) := by
  obtain ⟨Ka, Na, hTa⟩ := theorem1_leaf_1 hRH
  obtain ⟨Kb, Nb, hTb⟩ := theorem1_leaf_2 hRH
  refine ⟨8 * |Kb| + 16 * |Ka|, max (max Na Nb) 2, fun N H hN hH hHN => ?_⟩
  have hNa : Na ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : Nb ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
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
  have hlog1 : 0 ≤ Real.log (2 * (N : ℝ) ^ 2 / H) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hlH0 : 0 ≤ Real.log (2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hGa : ∀ i < 2 * H + 1 - 1, |∑ j ∈ range (i + 1), b j|
      ≤ |Ka| * N * Real.log N ^ 2 * Real.log (2 * H) := by
    intro i hi
    refine (hTa N H hNa hH hHN i hi).trans ?_
    have : 0 ≤ (N : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by positivity
    have h := mul_le_mul_of_nonneg_right (le_abs_self Ka) this
    linarith [show Ka * N * Real.log N ^ 2 * Real.log (2 * H)
      = Ka * ((N : ℝ) * Real.log N ^ 2 * Real.log (2 * H)) by ring,
      show |Ka| * N * Real.log N ^ 2 * Real.log (2 * H)
      = |Ka| * ((N : ℝ) * Real.log N ^ 2 * Real.log (2 * H)) by ring]
  have hGb : |∑ j ∈ range (2 * H + 1), b j| ≤ |Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H) := by
    refine (hTb N H hNb hH hHN).trans ?_
    have : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H) := by positivity
    have h := mul_le_mul_of_nonneg_right (le_abs_self Kb) this
    linarith [show Kb * N * Real.log (2 * (N : ℝ) ^ 2 / H)
      = Kb * ((N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)) by ring,
      show |Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H)
      = |Kb| * ((N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H)) by ring]
  have hfm : ∀ i, f i ≤ f (i + 1) := by
    intro i; simp only [hf]
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hN0.le
    exact_mod_cast (by omega : N - H + i ≤ N - H + (i + 1))
  have hB2 : 0 ≤ |Ka| * N * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  have hab := abel_bound f b (2 * H + 1) (by omega) hfm hB2 hGb hGa
  rw [← hXeq] at hab
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
    have e0 : ((N - H + 0 : ℕ) : ℝ) = N - H := by push_cast [Nat.cast_sub hHN]; ring
    rw [e1, e0]
    set u := ((N : ℝ) + H) / N
    set v := ((N : ℝ) - H) / N
    have huv : u - v = 2 * H / N := by simp only [u, v]; field_simp; ring
    have hu2 : u ≤ 2 := by simp only [u]; rw [div_le_iff₀ hN0]; linarith
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
  have hB1 : 0 ≤ |Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H) := by positivity
  have hXb : |X| ≤ 8 * (|Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H))
      + 8 * (2 * H / N) * (|Ka| * N * Real.log N ^ 2 * Real.log (2 * H)) := by
    calc |X| ≤ |f (2 * H + 1 - 1)| * (|Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H))
          + (f (2 * H + 1 - 1) - f 0) * (|Ka| * N * Real.log N ^ 2 * Real.log (2 * H)) := hab
      _ ≤ _ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hf2abs.trans he2) hB1
          · apply mul_le_mul_of_nonneg_right _ hB2
            have : Real.exp 2 * (2 * H / N) ≤ 8 * (2 * H / N) :=
              mul_le_mul_of_nonneg_right he2 (by positivity)
            linarith
  have hsimp : 8 * (2 * H / N) * (|Ka| * N * Real.log N ^ 2 * Real.log (2 * H))
      = 16 * |Ka| * (H * Real.log N ^ 2 * Real.log (2 * H)) := by
    field_simp
    ring
  rw [hsimp] at hXb
  have hT2 : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by positivity
  have hT1 : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) ^ 2 / H) := by positivity
  have hKa0 := abs_nonneg Ka
  have hKb0 := abs_nonneg Kb
  calc |X| ≤ 8 * (|Kb| * N * Real.log (2 * (N : ℝ) ^ 2 / H))
        + 16 * |Ka| * (H * Real.log N ^ 2 * Real.log (2 * H)) := hXb
    _ ≤ (8 * |Kb| + 16 * |Ka|) * (N * Real.log (2 * (N : ℝ) ^ 2 / H)
        + H * Real.log N ^ 2 * Real.log (2 * H)) := by nlinarith

#print axioms theorem1_leaf_4_from_leaves

end LeanLab.LZCesaroShort
