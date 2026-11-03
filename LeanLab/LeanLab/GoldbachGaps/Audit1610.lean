/-
Unit U-1610, run 20261103T0803Z-22341. Refutations of the old statements of `DecompJ205`, spelled
here as Props since the file now holds the repaired forms, and instances.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.GoldbachGaps.DecompJ205

namespace LeanLab.GoldbachGaps.Audit1610
open Real Chebyshev Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

/-- The old `leaf_fejer_asymp`. -/
def OldFejerAsymp : Prop := ∀ K : ℕ → ℕ,
  Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
  Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1)

/-- The old `leaf_sum_R_lower`. -/
def OldSumRLower : Prop := ∀ N K h : ℕ, 0 < h →
  (fejer N (K + h) - fejer N K) / (h : ℝ) ≤ ∑ n ∈ Icc (N - K) (N + K), Rg n

/-- The old `leaf_sum_R_upper`. -/
def OldSumRUpper : Prop := ∀ N K h : ℕ, 0 < h → h ≤ K →
  ∑ n ∈ Icc (N - K) (N + K), Rg n ≤ (fejer N K - fejer N (K - h)) / (h : ℝ)

/-- The old `leaf_sum_R_asymp`. -/
def OldSumRAsymp : Prop := ∀ K : ℕ → ℕ,
  Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1)

lemma zero_ne_lim (h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 1)) : False := by
  have hlim := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) h
  norm_num at hlim

theorem old_fejer_asymp_false : ¬ OldFejerAsymp := by
  intro h
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 1) := by
    simpa using h (fun _ => 0) (by simpa using tendsto_const_nhds)
  exact zero_ne_lim h0

theorem old_sum_R_asymp_false : ¬ OldSumRAsymp := by
  intro h
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 1) := by
    simpa using h (fun _ => 0)
  exact zero_ne_lim h0

lemma Rg_pos {m p : ℕ} (hpm : p < m) (hp : p.Prime) (hq : (m - p).Prime) : 0 < Rg m := by
  have hterm : ∀ i ∈ range m, 0 ≤ (if i.Prime ∧ (m - i).Prime then
      Real.log i * Real.log ((m - i : ℕ) : ℝ) else 0) := by
    intro i _
    split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    · exact le_rfl
  have hle := Finset.single_le_sum hterm (mem_range.mpr hpm)
  rw [if_pos ⟨hp, hq⟩] at hle
  have h1 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h2 : 0 < Real.log ((m - p : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  exact lt_of_lt_of_le (mul_pos h1 h2) hle

lemma fejer_6_3 : fejer 6 3 = Rg 4 + 2 * Rg 5 + 3 * Rg 6 + 2 * Rg 7 + Rg 8 := by
  unfold fejer
  rw [show 2 * 3 + 1 = 7 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma fejer_6_1 : fejer 6 1 = Rg 6 := by
  unfold fejer
  rw [show 2 * 1 + 1 = 3 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma fejer_6_0 : fejer 6 0 = 0 := by
  simp [fejer]

lemma sum_5_7 : ∑ n ∈ Icc (6 - 1) (6 + 1), Rg n = Rg 5 + Rg 6 + Rg 7 := by
  rw [show Icc (6 - 1) (6 + 1) = ({5, 6, 7} : Finset ℕ) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- `N = 6`, `K = 1`, `h = 2`: the quotient is `Rg 5 + Rg 6 + Rg 7 + (Rg 4 + Rg 8)/2`. -/
theorem old_sum_R_lower_false : ¬ OldSumRLower := by
  intro h
  have hb := h 6 1 2 (by norm_num)
  rw [sum_5_7, show 1 + 2 = 3 from rfl, fejer_6_3, fejer_6_1] at hb
  have h4 : 0 < Rg 4 := Rg_pos (p := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 := Rg_nonneg 8
  push_cast at hb
  linarith

/-- `N = 6`, `K = 1`, `h = 1`: the quotient is `Rg 6`. -/
theorem old_sum_R_upper_false : ¬ OldSumRUpper := by
  intro h
  have hb := h 6 1 1 (by norm_num) le_rfl
  rw [sum_5_7, show 1 - 1 = 0 from rfl, fejer_6_1, fejer_6_0] at hb
  have h5 : 0 < Rg 5 := Rg_pos (p := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 := Rg_nonneg 7
  norm_num at hb
  linarith

/-- The hypotheses of `leaf_sum_R_lower` and `leaf_sum_R_upper` hold at `N = 6`, `K = 1`, `h = 1`. -/
theorem sum_R_hypotheses : 0 < (1 : ℕ) ∧ (1 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ 6 := by norm_num

end LeanLab.GoldbachGaps.Audit1610
