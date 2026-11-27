/-
P0068 Zhan 1991, page 263 display (3.3): the harmonic LEAF `perron_harmonic_leaf_ps2` of
PerronSum1122d.lean, split. Burst 20261124, session S9, unit A-extra-3. The terms with
`|m - v| < 1` are at most `4e` and there are at most two of them; the others are at most
`(2e v/T)(1/m + 1/|m - v|)`; these three facts are PROVED here. What is left are the LEAFs
`harm_H_leaf_A2` and `harm_dist_leaf_A2`, the two harmonic sums. The statement of `perron_harmonic_leaf_ps2` is
PROVED from it as `perron_harmonic_of_leaves_A2`, with `K = 8e + 14e (1 + 21 log 2 + 1/ε)` and
`N₀ = 3`. AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronSum1122d
namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- Page 263 display (3.3), the single term error at `m` with `|m - v| < 1`: with
`c = 1 + 1/log N ≤ 2`, it is `1/2 + c/T ≤ 2` at `m = v` and `2 (v/m)^c ≤ 2 e v/m ≤ 4e`
otherwise, since `(v/m)^{1/log N} ≤ N^{1/log N} = e` and `v/m ≤ 2`. PROVED. -/
theorem harm_near_A2 : ∀ (N : ℕ) (T v : ℝ) (m : ℕ), 3 ≤ N → 2 ≤ T → 0 < v → v ≤ N →
    1 ≤ m → |(m : ℝ) - v| < 1 →
    (if v / (m : ℝ) = 1 then 1 / 2 + (1 + 1 / Real.log N) / T
        else 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) *
          min 1 (1 / (T * |Real.log (v / (m : ℝ))|))) ≤ 4 * Real.exp 1 := by
  intro N T v m hN hT hv hvN hm hnear
  have he2 : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hinv : 1 / Real.log N ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hlog1
  have hinv0 : 0 ≤ 1 / Real.log N := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT0 : 0 < T := by linarith
  split_ifs with h
  · have : (1 + 1 / Real.log N) / T ≤ 1 := by
      rw [div_le_one hT0]; linarith
    linarith
  · have hx0 : 0 ≤ v / (m : ℝ) := by positivity
    have hx2 : v / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := (abs_lt.mp hnear).1; linarith
    have hpow : (v / (m : ℝ)) ^ (1 + 1 / Real.log N) ≤ 4 := by
      calc (v / (m : ℝ)) ^ (1 + 1 / Real.log N) ≤ (2 : ℝ) ^ (1 + 1 / Real.log N) :=
            Real.rpow_le_rpow hx0 hx2 (by linarith)
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have hmin : min 1 (1 / (T * |Real.log (v / (m : ℝ))|)) ≤ 1 := min_le_left _ _
    have hmin0 : 0 ≤ min 1 (1 / (T * |Real.log (v / (m : ℝ))|)) := le_min zero_le_one (by positivity)
    have hp0 : 0 ≤ (v / (m : ℝ)) ^ (1 + 1 / Real.log N) := by positivity
    calc 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) * min 1 (1 / (T * |Real.log (v / (m : ℝ))|))
        ≤ 2 * 4 * 1 := by gcongr
      _ ≤ 4 * Real.exp 1 := by linarith

/-- Page 263 display (3.3), the single term error at `m` with `|m - v| ≥ 1`:
`2 (v/m)^c min(1, 1/(T|log(v/m)|)) ≤ 2e (v/m) max(v,m)/(T|v - m|) ≤ (2e v/T)(1/m + 1/|v - m|)`,
by `|log(v/m)| ≥ |v - m|/max(v, m)` and `(v/m)^{1/log N} ≤ e`. PROVED. -/
theorem harm_far_A2 : ∀ (N : ℕ) (T v : ℝ) (m : ℕ), 3 ≤ N → 2 ≤ T → 0 < v → v ≤ N →
    1 ≤ m → 1 ≤ |(m : ℝ) - v| →
    (if v / (m : ℝ) = 1 then 1 / 2 + (1 + 1 / Real.log N) / T
        else 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) *
          min 1 (1 / (T * |Real.log (v / (m : ℝ))|)))
      ≤ 2 * Real.exp 1 * v / T * (1 / (m : ℝ) + 1 / |(m : ℝ) - v|) := by
  intro N T v m hN hT hv hvN hm hfar
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hT0 : 0 < T := by linarith
  have hne : (m : ℝ) ≠ v := by
    intro h; rw [h, sub_self, abs_zero] at hfar; linarith
  set x := v / (m : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≠ 1 := by
    intro h; rw [hxdef, div_eq_one_iff_eq hm0.ne'] at h; exact hne h.symm
  rw [if_neg hx1]
  have hxN : x ≤ N := by
    rw [hxdef, div_le_iff₀ hm0]; nlinarith
  -- `x^c ≤ e x`
  have hpow : x ^ (1 + 1 / Real.log N) ≤ Real.exp 1 * x := by
    rw [Real.rpow_add hx0, Real.rpow_one, mul_comm (Real.exp 1)]
    gcongr
    rcases le_or_gt x 1 with h | h
    · calc x ^ (1 / Real.log N) ≤ 1 := Real.rpow_le_one hx0.le h (by positivity)
        _ ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    · calc x ^ (1 / Real.log N) ≤ (N : ℝ) ^ (1 / Real.log N) :=
            Real.rpow_le_rpow hx0.le hxN (by positivity)
        _ = Real.exp 1 := by
            rw [Real.rpow_def_of_pos hNpos]; congr 1; field_simp
  -- `|log x| ≥ |x - 1| / max x 1`, used as `1/|log x| ≤ max x 1 / |x - 1|`
  have hlogx : |x - 1| / max x 1 ≤ |Real.log x| := by
    rcases le_or_gt x 1 with h | h
    · have hl : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
      rw [max_eq_right h, div_one, abs_of_nonpos (by linarith),
        abs_of_nonpos (Real.log_nonpos hx0.le h)]
      linarith
    · have hl : 1 - 1 / x ≤ Real.log x := by
        have := Real.one_sub_inv_le_log_of_pos hx0; simpa [one_div] using this
      rw [max_eq_left h.le, abs_of_pos (by linarith), abs_of_pos (Real.log_pos h)]
      calc (x - 1) / x = 1 - 1 / x := by field_simp
        _ ≤ _ := hl
  have hxm1 : 0 < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
  have hlogpos : 0 < |Real.log x| := lt_of_lt_of_le (by positivity) hlogx
  have hmin : min 1 (1 / (T * |Real.log x|)) ≤ max x 1 / (T * |x - 1|) := by
    refine le_trans (min_le_right _ _) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := (div_le_iff₀ (show 0 < max x 1 by positivity)).mp hlogx
    nlinarith
  have hmin0 : 0 ≤ min 1 (1 / (T * |Real.log x|)) := le_min zero_le_one (by positivity)
  -- `x max(x,1) / |x - 1| ≤ v (1/m + 1/|m - v|)`
  have hkey : x * (max x 1 / (T * |x - 1|)) ≤ v / T * (1 / (m : ℝ) + 1 / |(m : ℝ) - v|) := by
    have hx1' : |x - 1| = |(m : ℝ) - v| / m := by
      rw [hxdef, abs_sub_comm, show (1 : ℝ) - v / m = ((m : ℝ) - v) / m by field_simp,
        abs_div, abs_of_pos hm0]
    have hd : 0 < |(m : ℝ) - v| := by linarith
    rw [hx1']
    rcases le_or_gt x 1 with h | h
    · rw [max_eq_right h, hxdef]
      have : v / m * (1 / (T * (|(m : ℝ) - v| / m))) = v / T * (1 / |(m : ℝ) - v|) := by
        field_simp
      rw [this]
      gcongr
      have : 0 ≤ 1 / (m : ℝ) := by positivity
      linarith
    · rw [max_eq_left h.le, hxdef]
      have hvm : (m : ℝ) < v := by
        rw [hxdef, lt_div_iff₀ hm0, one_mul] at h; exact h
      have habs : |(m : ℝ) - v| = v - m := by rw [abs_of_neg (by linarith)]; ring
      rw [habs]
      have hvm' : 0 < v - m := by linarith
      have : v / m * (v / m / (T * ((v - m) / m))) = v / T * (1 / m + 1 / (v - m)) := by
        field_simp; ring
      rw [this]
  have hp0 : 0 ≤ x ^ (1 + 1 / Real.log N) := by positivity
  calc 2 * x ^ (1 + 1 / Real.log N) * min 1 (1 / (T * |Real.log x|))
      ≤ 2 * (Real.exp 1 * x) * (max x 1 / (T * |x - 1|)) := by gcongr
    _ = 2 * Real.exp 1 * (x * (max x 1 / (T * |x - 1|))) := by ring
    _ ≤ 2 * Real.exp 1 * (v / T * (1 / (m : ℝ) + 1 / |(m : ℝ) - v|)) := by gcongr
    _ = 2 * Real.exp 1 * v / T * (1 / (m : ℝ) + 1 / |(m : ℝ) - v|) := by ring

/-- Page 263 display (3.3), at most two integers `m` lie within distance `1` of `v`,
namely `⌊v⌋` and `⌊v⌋ + 1`. PROVED. -/
theorem harm_near_card_A2 : ∀ (M : ℕ) (v : ℝ), 0 < v →
    ((Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => |(m : ℝ) - v| < 1)).card ≤ 2 := by
  intro M v hv
  have hsub : (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => |(m : ℝ) - v| < 1) ⊆
      {⌊v⌋₊, ⌊v⌋₊ + 1} := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have h := abs_lt.mp hm.2
    have hf1 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv.le
    have hf2 : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
    have a1 : (m : ℝ) < (⌊v⌋₊ : ℝ) + 2 := by linarith
    have a2 : (⌊v⌋₊ : ℝ) < (m : ℝ) + 1 := by linarith
    have b1 : m < ⌊v⌋₊ + 2 := by exact_mod_cast a1
    have b2 : ⌊v⌋₊ < m + 1 := by exact_mod_cast a2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc _ ≤ ({⌊v⌋₊, ⌊v⌋₊ + 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- LEAF: page 263 display (3.3), the harmonic sum `Σ_{1 ≤ m ≤ M} 1/m ≤ 1 + log (M + 1)`,
from `1/(k + 1) ≤ log (k + 1) - log k`. Class EASY. -/
theorem harm_H_leaf_A2 : ∀ M : ℕ,
    ∑ m ∈ Finset.Icc (1 : ℕ) M, 1 / (m : ℝ) ≤ 1 + Real.log (M + 1) := by
  sorry

/-- LEAF: page 263 display (3.3), the harmonic sum around `v`: over `1 ≤ m ≤ M` with
`|m - v| ≥ 1`, `Σ 1/|m - v| ≤ 6 (1 + log (M + 1))`, since `|m - v| ≥ (|m - ⌊v⌋| + 1)/3` there
and each side of `⌊v⌋` is a harmonic sum of at most `M` terms. Class MEDIUM. -/
theorem harm_dist_leaf_A2 : ∀ (M : ℕ) (v : ℝ), 0 < v →
    ∑ m ∈ (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / |(m : ℝ) - v|
      ≤ 6 * (1 + Real.log (M + 1)) := by
  sorry

/-- Page 263 display (3.3), the two harmonic sums together. -/
theorem harm_sums_A2 : ∀ (M : ℕ) (v : ℝ), 0 < v →
    ∑ m ∈ Finset.Icc (1 : ℕ) M, 1 / (m : ℝ) ≤ 1 + Real.log (M + 1) ∧
    ∑ m ∈ (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / |(m : ℝ) - v|
      ≤ 6 * (1 + Real.log (M + 1)) :=
  fun M v hv => ⟨harm_H_leaf_A2 M, harm_dist_leaf_A2 M v hv⟩

/-- Page 263 display (3.3), the harmonic sum, the statement of the LEAF
`perron_harmonic_leaf_ps2`, from the LEAFs `harm_H_leaf_A2`
and `harm_dist_leaf_A2` and the three PROVED pointwise and counting lemmas above. -/
theorem perron_harmonic_of_leaves_A2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (T v : ℝ),
    N₀ ≤ N → 2 ≤ T → T ≤ N → 0 < v → v ≤ N →
    ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
      (if v / (m : ℝ) = 1 then 1 / 2 + (1 + 1 / Real.log N) / T
        else 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) *
          min 1 (1 / (T * |Real.log (v / (m : ℝ))|)))
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  intro ε hε
  refine ⟨8 * Real.exp 1 + 14 * Real.exp 1 * (1 + 21 * Real.log 2 + 1 / ε), 3,
    by positivity, ?_⟩
  intro N T v hN hT hTN hv hvN
  have hN3 : 3 ≤ N := by exact_mod_cast hN
  set M := 2 ^ 20 * N with hM
  set f : ℕ → ℝ := fun m => (if v / (m : ℝ) = 1 then 1 / 2 + (1 + 1 / Real.log N) / T
        else 2 * (v / (m : ℝ)) ^ (1 + 1 / Real.log N) *
          min 1 (1 / (T * |Real.log (v / (m : ℝ))|))) with hf
  have hT0 : 0 < T := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun m : ℕ => |(m : ℝ) - v| < 1)]
  -- near terms
  have hnear : ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => |(m : ℝ) - v| < 1), f m
      ≤ 8 * Real.exp 1 := by
    calc _ ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => |(m : ℝ) - v| < 1), 4 * Real.exp 1 := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_filter, Finset.mem_Icc] at hm
          exact harm_near_A2 N T v m hN3 hT hv hvN hm.1.1 hm.2
      _ = _ * (4 * Real.exp 1) := Finset.sum_const _ |>.trans (nsmul_eq_mul _ _)
      _ ≤ 2 * (4 * Real.exp 1) := by
          gcongr
          exact_mod_cast harm_near_card_A2 M v hv
      _ = 8 * Real.exp 1 := by ring
  -- far terms
  obtain ⟨hH, hS⟩ := harm_sums_A2 M v hv
  have hfar : ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => ¬ |(m : ℝ) - v| < 1), f m
      ≤ 2 * Real.exp 1 * v / T * (7 * (1 + Real.log (M + 1))) := by
    have hfilt : (Finset.Icc 1 M).filter (fun m : ℕ => ¬ |(m : ℝ) - v| < 1)
        = (Finset.Icc 1 M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|) := by
      apply Finset.filter_congr; intro m _; exact not_lt
    rw [hfilt]
    have hc : 0 ≤ 2 * Real.exp 1 * v / T := by positivity
    calc _ ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|),
            2 * Real.exp 1 * v / T * (1 / (m : ℝ) + 1 / |(m : ℝ) - v|) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_filter, Finset.mem_Icc] at hm
          exact harm_far_A2 N T v m hN3 hT hv hvN hm.1.1 hm.2
      _ = 2 * Real.exp 1 * v / T *
            (∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / (m : ℝ) +
             ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|),
               1 / |(m : ℝ) - v|) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * Real.exp 1 * v / T * ((1 + Real.log (M + 1)) + 6 * (1 + Real.log (M + 1))) := by
          gcongr
          calc _ ≤ ∑ m ∈ Finset.Icc 1 M, 1 / (m : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun _ _ _ => by positivity)
            _ ≤ _ := hH
      _ = _ := by ring
  -- the logarithm
  have hlogM : Real.log (M + 1) ≤ 21 * Real.log 2 + (N : ℝ) ^ ε / ε := by
    have h1 : ((M : ℝ) + 1) ≤ 2 ^ 21 * N := by
      rw [hM]; push_cast
      have : (1 : ℝ) ≤ N := by linarith
      nlinarith
    calc Real.log (M + 1) ≤ Real.log (2 ^ 21 * N) := Real.log_le_log (by positivity) h1
      _ = 21 * Real.log 2 + Real.log N := by
          rw [Real.log_mul (by positivity) hNpos.ne', Real.log_pow]; push_cast; ring
      _ ≤ _ := by gcongr; exact Real.log_le_rpow_div hNpos.le hε
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hNT : 1 ≤ (N : ℝ) / T := by rw [le_div_iff₀ hT0]; linarith
  have hrpow : (N : ℝ) ^ (1 + ε) = N * (N : ℝ) ^ ε := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  rw [hrpow]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogM0 : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg _; linarith)
  -- combine: everything is at most (N/T) N^ε times the constant
  have hvT : v / T ≤ N / T := by gcongr
  have hA : 8 * Real.exp 1 ≤ 8 * Real.exp 1 * ((N : ℝ) / T * (N : ℝ) ^ ε) := by
    have : 1 ≤ (N : ℝ) / T * (N : ℝ) ^ ε := by nlinarith
    nlinarith
  have hB : 2 * Real.exp 1 * v / T * (7 * (1 + Real.log (M + 1))) ≤
      14 * Real.exp 1 * (1 + 21 * Real.log 2 + 1 / ε) * ((N : ℝ) / T * (N : ℝ) ^ ε) := by
    have h1 : 1 + Real.log (M + 1) ≤ (1 + 21 * Real.log 2 + 1 / ε) * (N : ℝ) ^ ε := by
      have : (N : ℝ) ^ ε / ε = 1 / ε * (N : ℝ) ^ ε := by ring
      nlinarith
    have h2 : 2 * Real.exp 1 * v / T = 2 * Real.exp 1 * (v / T) := by ring
    rw [h2]
    calc 2 * Real.exp 1 * (v / T) * (7 * (1 + Real.log (M + 1)))
        ≤ 2 * Real.exp 1 * ((N : ℝ) / T) * (7 * ((1 + 21 * Real.log 2 + 1 / ε) * (N : ℝ) ^ ε)) := by
          gcongr
      _ = _ := by ring
  have hgoal : (8 * Real.exp 1 + 14 * Real.exp 1 * (1 + 21 * Real.log 2 + 1 / ε)) *
      (N * (N : ℝ) ^ ε) / T = (8 * Real.exp 1 + 14 * Real.exp 1 * (1 + 21 * Real.log 2 + 1 / ε))
        * ((N : ℝ) / T * (N : ℝ) ^ ε) := by ring
  rw [hgoal]
  linarith
end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.harm_near_A2
#print axioms LeanLab.Zhan1991.harm_far_A2
#print axioms LeanLab.Zhan1991.harm_near_card_A2
#print axioms LeanLab.Zhan1991.perron_harmonic_of_leaves_A2
