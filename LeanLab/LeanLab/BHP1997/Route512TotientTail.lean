/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, which cites Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, book page 34, display 3.23.
Proof of `Section2MS.leaf_totient_sq_tail512` in Route512Vaughan323.lean.

The elementary fact printed under 3.23, Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, from the mean value
Σ_{q≤R} (q/φ(q))² ≪ R of Route512TotientMean.lean, by partial summation against the
nonincreasing weight 1/max(q,Z)² and a telescoping bound for Σ_q 1/max(q,Z)².
No new definition. Route512Vaughan323.lean imports this file and closes its leaf with
`totient_sq_tail512`.
Burst burst-20261124 session S4. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Route512TotientMean

namespace LeanLab.BHP1997.Section2MS

/-- Partial summation with an invariant: for a nonincreasing nonnegative weight w and
partial sums of a bounded by C n, Σ_{i<R} a(i+1) w(i+1) is at most C Σ_{i<R} w(i+1)
plus the nonpositive boundary term (A(R) - C R) w(R). -/
private lemma v323_abel_le (a w : ℕ → ℝ) (C : ℝ)
    (hA : ∀ n : ℕ, ∑ i ∈ Finset.range n, a (i + 1) ≤ C * n)
    (hw : ∀ n : ℕ, w (n + 1) ≤ w n) :
    ∀ R : ℕ, ∑ i ∈ Finset.range R, a (i + 1) * w (i + 1) ≤
      C * ∑ i ∈ Finset.range R, w (i + 1) +
        (∑ i ∈ Finset.range R, a (i + 1) - C * R) * w R := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := hA R
    have h2 := hw R
    have hprod : (∑ i ∈ Finset.range R, a (i + 1) - C * R) * (w R - w (R + 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    push_cast
    nlinarith [hprod, ih]

/-- Telescoping: Σ_{i<R} 1/max(i+1,Z)² ≤ 4/max(Z,1) - 4/(R + max(Z,1)). -/
private lemma v323_weight_sum (Z : ℝ) (hZ : 0 < Z) :
    ∀ R : ℕ, ∑ i ∈ Finset.range R, 1 / (max ((i + 1 : ℕ) : ℝ) Z) ^ 2 ≤
      4 / max Z 1 - 4 / ((R : ℝ) + max Z 1) := by
  intro R
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ]
    set M := max Z 1 with hM
    have hM1 : 1 ≤ M := le_max_right _ _
    set m := max ((R + 1 : ℕ) : ℝ) Z with hm
    have hmR : ((R : ℝ) + 1) ≤ m := by
      rw [hm]; push_cast; exact le_max_left _ _
    have hmM : M ≤ m := by
      rcases le_total Z 1 with h | h
      · have : M = 1 := max_eq_right h
        rw [this]; linarith [hmR, (Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
      · have : M = Z := max_eq_left h
        rw [this]; exact le_max_right _ _
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hm0 : 0 < m := by linarith
    have key : 1 / m ^ 2 ≤ 4 / ((R : ℝ) + M) - 4 / (((R + 1 : ℕ) : ℝ) + M) := by
      push_cast
      have hA : 0 < (R : ℝ) + M := by linarith
      have hB : 0 < (R : ℝ) + 1 + M := by linarith
      have e : 4 / ((R : ℝ) + M) - 4 / ((R : ℝ) + 1 + M) =
          4 / (((R : ℝ) + M) * ((R : ℝ) + 1 + M)) := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hmR, hmM, hm0]
    linarith

/-- Exact statement of `Section2MS.leaf_totient_sq_tail512`, Vaughan 1981 book page 34
under display 3.23, PROVED from the mean value `totient_ratio_sq_mean512`, with K = 4 C. -/
theorem totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 := by
  obtain ⟨C, hC0, hC⟩ := totient_ratio_sq_mean512
  refine ⟨4 * C, by positivity, fun Z hZ R => ?_⟩
  -- reindex Icc 1 n as range n shifted by one
  have hIcc : ∀ (n : ℕ) (f : ℕ → ℝ), ∑ r ∈ Finset.Icc 1 n, f r =
      ∑ i ∈ Finset.range n, f (i + 1) := by
    intro n f
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
  set a : ℕ → ℝ := fun r => ((r : ℝ) / (Nat.totient r : ℝ)) ^ 2 with ha
  set w : ℕ → ℝ := fun r => 1 / (max (r : ℝ) Z) ^ 2 with hw
  have hA : ∀ n : ℕ, ∑ i ∈ Finset.range n, a (i + 1) ≤ C * n := by
    intro n; rw [← hIcc n a]; exact hC n
  have hwmono : ∀ n : ℕ, w (n + 1) ≤ w n := by
    intro n
    simp only [hw]
    have h0 : 0 < max (n : ℝ) Z := lt_of_lt_of_le hZ (le_max_right _ _)
    have hle : max (n : ℝ) Z ≤ max ((n + 1 : ℕ) : ℝ) Z := by
      apply max_le_max _ le_rfl
      push_cast; linarith
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ h0.le hle 2
  have hw0 : ∀ n : ℕ, 0 ≤ w n := fun n => by simp only [hw]; positivity
  -- step 1: the filtered sum is at most Σ a w
  have step1 : ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
      1 / (Nat.totient r : ℝ) ^ 2 ≤ ∑ r ∈ Finset.Icc 1 R, a r * w r := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun r hr => ?_)
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
    split_ifs with hZr
    · have hmax : max (r : ℝ) Z = r := max_eq_left hZr.le
      simp only [ha, hw, hmax]
      rw [div_pow]
      rcases eq_or_ne (Nat.totient r : ℝ) 0 with h | h
      · rw [h]; simp
      · apply le_of_eq
        field_simp
    · exact mul_nonneg (by simp only [ha]; positivity) (hw0 r)
  -- step 2: partial summation
  have step2 : ∑ r ∈ Finset.Icc 1 R, a r * w r ≤ C * ∑ i ∈ Finset.range R, w (i + 1) := by
    rw [hIcc R (fun r => a r * w r)]
    have h := v323_abel_le a w C hA hwmono R
    have hb : (∑ i ∈ Finset.range R, a (i + 1) - C * R) * w R ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hA R]) (hw0 R)
    linarith
  -- step 3: the weight sum
  have step3 : ∑ i ∈ Finset.range R, w (i + 1) ≤ 4 * min (1 / Z) 1 := by
    have h := v323_weight_sum Z hZ R
    have hM : 0 < max Z 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hpos : 0 ≤ 4 / ((R : ℝ) + max Z 1) := by positivity
    have hmin : 4 / max Z 1 = 4 * min (1 / Z) 1 := by
      rcases le_total Z 1 with hz | hz
      · rw [max_eq_right hz, min_eq_right ((one_le_div hZ).mpr hz)]; norm_num
      · rw [max_eq_left hz, min_eq_left ((div_le_one hZ).mpr hz)]; ring
    simp only [hw]
    linarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ C * (4 * min (1 / Z) 1) := mul_le_mul_of_nonneg_left step3 hC0
    _ = 4 * C * min (1 / Z) 1 := by ring

end LeanLab.BHP1997.Section2MS

#print axioms LeanLab.BHP1997.Section2MS.totient_sq_tail512
