/-
P0068 Zhan 1991, page 263 display (3.3): the two LEAFs `harm_H_leaf_A2` and `harm_dist_leaf_A2`
of SPLIT_harmonic_A2.lean, PROVED, and with them the harmonic LEAF `perron_harmonic_leaf_ps2` of
PerronSum1122d.lean, PROVED as `perron_harmonic_proof_A2`. Burst 20261124, session S9, unit
A-extra-4. `Σ 1/m ≤ 1 + log (M + 1)` by induction from `1/(k + 1) ≤ log ((k + 1)/k)`; around `v`,
`1/|m - v| ≤ 3/(|m - ⌊v⌋| + 1)` and each side of `⌊v⌋` injects into `1, …, M`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_harmonic_A2

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- Page 263 display (3.3), the harmonic sum up to `k + 1`, by induction. -/
theorem harmH_aux_A2 (k : ℕ) :
    ∑ m ∈ Finset.Icc (1 : ℕ) (k + 1), 1 / (m : ℝ) ≤ 1 + Real.log (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hstep : 1 / ((k + 1 + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1) := by
      rw [← Real.log_div (by positivity) hk.ne']
      have h := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < ((k + 1 : ℕ) + 1) / ((k : ℝ) + 1) by positivity)
      refine le_trans (le_of_eq ?_) h
      push_cast
      field_simp
      ring
    push_cast at hstep ih ⊢
    linarith
/-- The same statement as the LEAF `harm_H_leaf_A2`, page 263 display (3.3). -/
theorem harm_H_proof_A2 : ∀ M : ℕ,
    ∑ m ∈ Finset.Icc (1 : ℕ) M, 1 / (m : ℝ) ≤ 1 + Real.log (M + 1) := by
  intro M
  rcases M with _ | k
  · simp
  · refine le_trans (harmH_aux_A2 k) ?_
    gcongr
    linarith

/-- An injection of `s` into `1, …, M` bounds `Σ_s 1/g(m)` by the harmonic sum. -/
theorem sum_inj_le_H_A2 (M : ℕ) (s : Finset ℕ) (g : ℕ → ℕ) (hg : Set.InjOn g s)
    (himg : ∀ m ∈ s, g m ∈ Finset.Icc 1 M) :
    ∑ m ∈ s, 1 / (g m : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℝ) := by
  rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ)) hg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    exact himg m hm
  · intro _ _ _; positivity

/-- Page 263 display (3.3): around `v`, `Σ 1/|m - v| ≤ 3 · 2 Σ_{k ≤ M} 1/k`. -/
theorem dist_floor_A2 (M : ℕ) (v : ℝ) (hv : 0 < v) :
    ∑ m ∈ (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / |(m : ℝ) - v|
      ≤ 3 * (2 * ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℝ)) := by
  set n0 := ⌊v⌋₊ with hn0
  have hf1 : (n0 : ℝ) ≤ v := Nat.floor_le hv.le
  have hf2 : v < (n0 : ℝ) + 1 := Nat.lt_floor_add_one v
  -- pointwise: `1/|m - v| ≤ 3/(|m - n0| + 1)`
  have hpt : ∀ m : ℕ, 1 ≤ |(m : ℝ) - v| →
      1 / |(m : ℝ) - v| ≤ 3 * (1 / (|(m : ℝ) - n0| + 1)) := by
    intro m hm
    have hd : |(m : ℝ) - n0| ≤ |(m : ℝ) - v| + 1 := by
      have := abs_sub_le (m : ℝ) v n0
      have h2 : |v - (n0 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have hpos : 0 < |(m : ℝ) - v| := by linarith
    have h3 : |(m : ℝ) - n0| + 1 ≤ 3 * |(m : ℝ) - v| := by linarith
    rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
    linarith
  set F := (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|)
  calc ∑ m ∈ F, 1 / |(m : ℝ) - v| ≤ ∑ m ∈ F, 3 * (1 / (|(m : ℝ) - n0| + 1)) := by
        apply Finset.sum_le_sum
        intro m hm
        exact hpt m (Finset.mem_filter.mp hm).2
    _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) M, 3 * (1 / (|(m : ℝ) - n0| + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = 3 * ∑ m ∈ Finset.Icc (1 : ℕ) M, 1 / (|(m : ℝ) - n0| + 1) := by rw [Finset.mul_sum]
    _ ≤ 3 * (2 * ∑ k ∈ Finset.Icc (1 : ℕ) M, 1 / (k : ℝ)) := by
      gcongr
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun m => n0 < m)]
      rw [two_mul]
      gcongr
      · -- `m > n0`
        calc ∑ m ∈ (Finset.Icc 1 M).filter (fun m => n0 < m), 1 / (|(m : ℝ) - n0| + 1)
            ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => n0 < m), 1 / ((m - n0 : ℕ) : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              rw [Finset.mem_filter] at hm
              have hlt : n0 < m := hm.2
              have hc : ((m - n0 : ℕ) : ℝ) = (m : ℝ) - n0 := by
                rw [Nat.cast_sub hlt.le]
              have hpos : (0 : ℝ) < ((m - n0 : ℕ) : ℝ) := by
                have : 0 < m - n0 := by omega
                exact_mod_cast this
              rw [hc] at hpos ⊢
              rw [abs_of_pos hpos]
              apply one_div_le_one_div_of_le hpos
              linarith
          _ ≤ _ := by
              apply sum_inj_le_H_A2
              · intro a ha b hb hab
                simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
                simp only at hab
                omega
              · intro m hm
                rw [Finset.mem_filter, Finset.mem_Icc] at hm
                rw [Finset.mem_Icc]
                omega
      · -- `m ≤ n0`
        set n1 := min n0 M with hn1
        calc ∑ m ∈ (Finset.Icc 1 M).filter (fun m => ¬ n0 < m), 1 / (|(m : ℝ) - n0| + 1)
            ≤ ∑ m ∈ (Finset.Icc 1 M).filter (fun m => ¬ n0 < m), 1 / ((n1 + 1 - m : ℕ) : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              rw [Finset.mem_filter, Finset.mem_Icc] at hm
              have hle : m ≤ n1 := by omega
              have hc : ((n1 + 1 - m : ℕ) : ℝ) = (n1 : ℝ) + 1 - m := by
                rw [Nat.cast_sub (by omega)]; push_cast; ring
              have hn1n0 : (n1 : ℝ) ≤ n0 := by exact_mod_cast min_le_left n0 M
              have hmle : (m : ℝ) ≤ n1 := by exact_mod_cast hle
              have hpos : (0 : ℝ) < (n1 : ℝ) + 1 - m := by linarith
              rw [hc, abs_of_nonpos (by linarith)]
              apply one_div_le_one_div_of_le hpos
              linarith
          _ ≤ _ := by
              apply sum_inj_le_H_A2
              · intro a ha b hb hab
                simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at ha hb
                omega
              · intro m hm
                rw [Finset.mem_filter, Finset.mem_Icc] at hm
                rw [Finset.mem_Icc]
                omega

/-- The same statement as the LEAF `harm_dist_leaf_A2`, page 263 display (3.3). -/
theorem harm_dist_proof_A2 : ∀ (M : ℕ) (v : ℝ), 0 < v →
    ∑ m ∈ (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / |(m : ℝ) - v|
      ≤ 6 * (1 + Real.log (M + 1)) := by
  intro M v hv
  have h1 := dist_floor_A2 M v hv
  have h2 := harm_H_proof_A2 M
  linarith

/-- Page 263 display (3.3), the two harmonic sums together, PROVED. -/
theorem harm_sums_proof_A2 : ∀ (M : ℕ) (v : ℝ), 0 < v →
    ∑ m ∈ Finset.Icc (1 : ℕ) M, 1 / (m : ℝ) ≤ 1 + Real.log (M + 1) ∧
    ∑ m ∈ (Finset.Icc (1 : ℕ) M).filter (fun m : ℕ => 1 ≤ |(m : ℝ) - v|), 1 / |(m : ℝ) - v|
      ≤ 6 * (1 + Real.log (M + 1)) :=
  fun M v hv => ⟨harm_H_proof_A2 M, harm_dist_proof_A2 M v hv⟩

/-- Page 263 display (3.3), the harmonic sum, the statement of the LEAF
`perron_harmonic_leaf_ps2`, with the two harmonic sums PROVED;
the same statement as `perron_harmonic_leaf_ps2`, PROVED. -/
theorem perron_harmonic_proof_A2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (T v : ℝ),
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
  obtain ⟨hH, hS⟩ := harm_sums_proof_A2 M v hv
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

#print axioms LeanLab.Zhan1991.harm_H_proof_A2
#print axioms LeanLab.Zhan1991.harm_dist_proof_A2
#print axioms LeanLab.Zhan1991.perron_harmonic_proof_A2
