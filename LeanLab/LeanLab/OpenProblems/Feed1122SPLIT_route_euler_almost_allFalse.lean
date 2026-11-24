import LeanLab.OpenProblems.SPLIT_route_euler_almost_all

/-!
# Falsifier for `leaf_circle_method_variance` (OpenProblems, SPLIT_route_euler_almost_all)

`leaf_circle_method_variance` in `SPLIT_route_euler_almost_all.lean` quantifies over every
`R : ℕ → ℕ` whose vanishing set on `1 ≤ n` is the non-representable set.  That hypothesis does
not pin the size of `R`.  Take `R` the indicator of the representable `n`, so `R n ≤ 1`.  Any
main term with `m n ≥ c * sqrt n / log n` then gives `(R n - m n) ^ 2 ≥ (m n) ^ 2 / 2 - 1`, and
the second moment over `[1, X]` is at least `c ^ 2 * X * (X - 1) / (4 * (log X) ^ 2) - X`, which
beats `B * X ^ 2 / (log X) ^ 3` for all large `X`.

The leaf is true in spirit only for the counting multiplicity of `leaf_representation_multiplicity`;
the theorem below proves the negation of the leaf's exact statement as written.  No definition
is introduced.  AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab
open scoped Classical

private theorem sum_Icc_pred (X : ℕ) :
    Finset.sum (Finset.Icc 1 X) (fun n => ((n : ℝ) - 1)) = (X : ℝ) * ((X : ℝ) - 1) / 2 := by
  induction X with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The exact statement of `leaf_circle_method_variance` is false: a counterexample is
`R n = if IsEuler (8n+3) then 1 else 0`. -/
theorem leaf_circle_method_variance_false :
    ¬ (∀ R : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
      ∃ (m : ℕ → ℝ) (B c : ℝ), 0 < B ∧ 0 < c ∧
        (∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n) ∧
        ∀ᶠ X : ℕ in Filter.atTop,
          Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
            B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3) := by
  intro h
  set R : ℕ → ℕ := fun n => if IsEuler (8 * n + 3) then 1 else 0 with hRdef
  have hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
    intro n _
    simp only [hRdef]
    split_ifs with hE <;> simp [hE]
  have hR1 : ∀ n : ℕ, (R n : ℝ) ^ 2 ≤ 1 := by
    intro n
    simp only [hRdef]
    split_ifs <;> norm_num
  obtain ⟨m, B, c, hB, hc, hmain, hev⟩ := h R hR
  have hnat : Filter.Tendsto (fun X : ℕ => (X : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hratio : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ 2 / (1 * (X : ℝ) + 0))
      Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hnat
  have hc16 : (0 : ℝ) < c ^ 2 / 16 := by positivity
  have hev2 := hev.and ((hlog.eventually_gt_atTop (16 * B / c ^ 2)).and
    ((hratio.eventually (gt_mem_nhds hc16)).and (Filter.eventually_ge_atTop 2)))
  obtain ⟨X, hvar, hL, hrat, hX2⟩ := hev2.exists
  set L := Real.log (X : ℝ) with hLdef
  have hXr : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hrat' : L ^ 2 < c ^ 2 / 16 * (X : ℝ) := by
    have h0 : L ^ 2 / (1 * (X : ℝ) + 0) < c ^ 2 / 16 := hrat
    rw [one_mul, add_zero, div_lt_iff₀ hXpos] at h0
    exact h0
  -- pointwise lower bound
  have hpt : ∀ n ∈ Finset.Icc 1 X,
      c ^ 2 / (2 * L ^ 2) * ((n : ℝ) - 1) - 1 ≤ ((R n : ℝ) - m n) ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnX⟩ := hn
    have hgen : (m n) ^ 2 / 2 - 1 ≤ ((R n : ℝ) - m n) ^ 2 := by
      have := hR1 n
      nlinarith [sq_nonneg (2 * (R n : ℝ) - m n)]
    rcases Nat.eq_or_lt_of_le hn1 with h1 | h2
    · subst h1
      have : (0 : ℝ) ≤ ((R 1 : ℝ) - m 1) ^ 2 := sq_nonneg _
      simp only [Nat.cast_one, sub_self, mul_zero, zero_sub]
      linarith
    · have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h2
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnr
      have hlogle : Real.log (n : ℝ) ≤ L :=
        Real.log_le_log hnpos (by exact_mod_cast hnX)
      have hm : c * Real.sqrt (n : ℝ) / L ≤ m n :=
        le_trans (div_le_div_of_nonneg_left (by positivity) hlogn hlogle) (hmain n hn1)
      have hbase : 0 ≤ c * Real.sqrt (n : ℝ) / L := by positivity
      have hsq : (c * Real.sqrt (n : ℝ) / L) ^ 2 ≤ (m n) ^ 2 := pow_le_pow_left₀ hbase hm 2
      have hval : (c * Real.sqrt (n : ℝ) / L) ^ 2 = c ^ 2 / L ^ 2 * (n : ℝ) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hnpos.le]
        ring
      have hcl : 0 ≤ c ^ 2 / L ^ 2 := by positivity
      have hlin : c ^ 2 / (2 * L ^ 2) * ((n : ℝ) - 1) ≤ c ^ 2 / L ^ 2 * (n : ℝ) / 2 := by
        have : c ^ 2 / (2 * L ^ 2) = c ^ 2 / L ^ 2 / 2 := by field_simp
        rw [this]
        nlinarith
      linarith
  have hsum : c ^ 2 / (2 * L ^ 2) * ((X : ℝ) * ((X : ℝ) - 1) / 2) - (X : ℝ)
      ≤ Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) := by
    have h1 := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_Icc_pred] at h1
    simpa using h1
  have hmain2 : c ^ 2 / (2 * L ^ 2) * ((X : ℝ) * ((X : ℝ) - 1) / 2) - (X : ℝ)
      ≤ B * (X : ℝ) ^ 2 / L ^ 3 := hsum.trans hvar
  -- clear denominators: multiply by `4 * L ^ 3`
  have hL3 : 0 < L ^ 3 := by positivity
  have hclear : c ^ 2 * L * ((X : ℝ) * ((X : ℝ) - 1)) - 4 * (X : ℝ) * L ^ 3
      ≤ 4 * B * (X : ℝ) ^ 2 := by
    have e1 : (c ^ 2 / (2 * L ^ 2) * ((X : ℝ) * ((X : ℝ) - 1) / 2) - (X : ℝ)) * (4 * L ^ 3)
        = c ^ 2 * L * ((X : ℝ) * ((X : ℝ) - 1)) - 4 * (X : ℝ) * L ^ 3 := by
      field_simp
      ring
    have e2 : (B * (X : ℝ) ^ 2 / L ^ 3) * (4 * L ^ 3) = 4 * B * (X : ℝ) ^ 2 := by
      field_simp
    have := mul_le_mul_of_nonneg_right hmain2 (by positivity : (0 : ℝ) ≤ 4 * L ^ 3)
    rw [e1, e2] at this
    exact this
  -- `X * (X - 1) ≥ X ^ 2 / 2` and `X * L ^ 3 < c ^ 2 * X ^ 2 * L / 16`
  have hXX : (X : ℝ) ^ 2 / 2 ≤ (X : ℝ) * ((X : ℝ) - 1) := by nlinarith
  have hXL : 4 * (X : ℝ) * L ^ 3 ≤ c ^ 2 / 4 * (X : ℝ) ^ 2 * L := by
    have := mul_le_mul_of_nonneg_left hrat'.le (by positivity : (0 : ℝ) ≤ 4 * (X : ℝ) * L)
    nlinarith
  have hcL : 0 ≤ c ^ 2 * L := by positivity
  have hA : c ^ 2 * L * ((X : ℝ) ^ 2 / 2) ≤ c ^ 2 * L * ((X : ℝ) * ((X : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hXX hcL
  have hfin : c ^ 2 / 4 * L * (X : ℝ) ^ 2 ≤ 4 * B * (X : ℝ) ^ 2 := by nlinarith
  have hX2pos : (0 : ℝ) < (X : ℝ) ^ 2 := by positivity
  have hcLB : c ^ 2 / 4 * L ≤ 4 * B := le_of_mul_le_mul_right (by linarith) hX2pos
  have hLB : 16 * B / c ^ 2 < L := hL
  rw [div_lt_iff₀ (by positivity)] at hLB
  nlinarith

end LeanLab.OpenProblems.State1612
