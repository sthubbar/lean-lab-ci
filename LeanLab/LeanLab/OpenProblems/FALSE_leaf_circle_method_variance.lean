/-
FALSE: the LEAF `leaf_circle_method_variance` of SPLIT_route_euler_almost_all.lean, as stated, is
refuted. AI-written Lean code, Claude, unit S8-07 of burst-20261124. Checked only by the Lean
kernel. Euler's 8n + 3 problem and binary Goldbach are OPEN; this refutes only a split leaf.

The leaf quantifies over every `R : ℕ → ℕ` that is nonzero exactly at the representable `n`, a
hypothesis that leaves the size of `R` free. Take `R` the indicator of the representable `n`, so
`R n ≤ 1`. Any main term with `m n ≥ c sqrt n / log n` then gives
`(R n - m n) ^ 2 ≥ m n ^ 2 / 2 - 1 ≥ c ^ 2 n / (2 (log X) ^ 2) - 1` for `n ≤ X`, so the second
moment over `[1, X]` is at least `c ^ 2 X ^ 2 / (4 (log X) ^ 2) - X`, which beats
`B X ^ 2 / (log X) ^ 3` once `log X` is large and `(log X) ^ 3 ≤ X`. The intended leaf needs `R` to
be the list count of `leaf_representation_multiplicity`, of size about `sqrt n / log n`.
-/
import LeanLab.OpenProblems.SPLIT_route_euler_almost_all

namespace LeanLab.OpenProblems.State1612

open scoped Classical

/-- `Σ_{n=1}^X n ≥ X^2/2`, a helper for the refutation below. -/
theorem sum_Icc_natCast_ge_var (X : ℕ) :
    (X : ℝ) ^ 2 / 2 ≤ Finset.sum (Finset.Icc 1 X) (fun n => (n : ℝ)) := by
  induction X with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    nlinarith

/-- FALSE certificate for `leaf_circle_method_variance`: its statement, quantified over all `R`
meeting its hypothesis, fails for the indicator of the representable `n`. -/
theorem leaf_circle_method_variance_false :
    ¬ ∀ (R : ℕ → ℕ), (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
      ∃ (m : ℕ → ℝ) (B c : ℝ), 0 < B ∧ 0 < c ∧
        (∀ n : ℕ, 1 ≤ n → c * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ≤ m n) ∧
        ∀ᶠ X : ℕ in Filter.atTop,
          Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) ≤
            B * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 3 := by
  intro h
  set R : ℕ → ℕ := fun n => if IsEuler (8 * n + 3) then 1 else 0 with hRdef
  have hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
    intro n _
    by_cases he : IsEuler (8 * n + 3) <;> simp [hRdef, he]
  have hR01 : ∀ n, (R n : ℝ) ^ 2 ≤ 1 := by
    intro n; by_cases he : IsEuler (8 * n + 3) <;> simp [hRdef, he]
  obtain ⟨m, B, c, hB, hc, hmain, hvar⟩ := h R hR
  have ev1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 3 ≤ x := by
    have hb := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound one_pos
    filter_upwards [hb, Filter.eventually_ge_atTop 0] with x hx hx0
    simp only [Real.norm_eq_abs, id, one_mul, abs_of_nonneg hx0] at hx
    exact le_trans (le_abs_self _) hx
  have ev1' : ∀ᶠ X : ℕ in Filter.atTop, Real.log (X : ℝ) ^ 3 ≤ X :=
    tendsto_natCast_atTop_atTop.eventually ev1
  set K : ℝ := 4 * (B + 1) / c ^ 2 + 1 + c with hK
  have hKc : c ≤ K := by have : 0 ≤ 4 * (B + 1) / c ^ 2 := by positivity
                         linarith
  have hKB : B + 1 < c ^ 2 * K / 4 := by
    have h1 : 4 * (B + 1) / c ^ 2 < K := by linarith
    have hc2 : 0 < c ^ 2 := by positivity
    rw [div_lt_iff₀ hc2] at h1
    linarith
  have ev2 : ∀ᶠ X : ℕ in Filter.atTop, K ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop K)
  obtain ⟨X, hX1, hX2, hX3⟩ := (hvar.and (ev1'.and ev2)).exists
  set L : ℝ := Real.log (X : ℝ) with hLdef
  have hL : 0 < L := lt_of_lt_of_le hc (le_trans hKc hX3)
  have hX0 : X ≠ 0 := by
    rintro rfl; simp [hLdef] at hL
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX0
  have hcL : c ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hc.le (le_trans hKc hX3) 2
  have hterm : ∀ n ∈ Finset.Icc 1 X,
      c ^ 2 / (2 * L ^ 2) * (n : ℝ) - 1 ≤ ((R n : ℝ) - m n) ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hsq : (m n) ^ 2 / 2 - 1 ≤ ((R n : ℝ) - m n) ^ 2 := by
      nlinarith [hR01 n, sq_nonneg ((R n : ℝ) * 2 - m n)]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      have : c ^ 2 / (2 * L ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      nlinarith [sq_nonneg ((R 1 : ℝ) - m 1)]
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
      have hln : 0 < Real.log n := Real.log_pos (by linarith)
      have hlnL : Real.log n ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hn.2)
      have ha : 0 ≤ c * Real.sqrt n / Real.log n := by positivity
      have hm := hmain n hn.1
      have hm2 : (c * Real.sqrt n / Real.log n) ^ 2 ≤ m n ^ 2 := pow_le_pow_left₀ ha hm 2
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)] at hm2
      have h3 : c ^ 2 * n / L ^ 2 ≤ c ^ 2 * n / Real.log n ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hln.le hlnL 2)
      have h4 : c ^ 2 / (2 * L ^ 2) * (n : ℝ) = (c ^ 2 * n / L ^ 2) / 2 := by
        field_simp
      rw [h4]
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc] at hsum
  simp only [nsmul_eq_mul, mul_one, Nat.add_sub_cancel] at hsum
  have hG := sum_Icc_natCast_ge_var X
  have hlow : c ^ 2 / (2 * L ^ 2) * ((X : ℝ) ^ 2 / 2) - X ≤
      Finset.sum (Finset.Icc 1 X) (fun n => ((R n : ℝ) - m n) ^ 2) := by
    have : c ^ 2 / (2 * L ^ 2) * ((X : ℝ) ^ 2 / 2) ≤
        c ^ 2 / (2 * L ^ 2) * Finset.sum (Finset.Icc 1 X) (fun n => (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    linarith
  have hcomb := le_trans hlow hX1
  -- multiply out by L ^ 3
  have hL3 : 0 < L ^ 3 := by positivity
  have e1 : (c ^ 2 / (2 * L ^ 2) * ((X : ℝ) ^ 2 / 2) - X) * L ^ 3
      = c ^ 2 * L / 4 * (X : ℝ) ^ 2 - X * L ^ 3 := by
    field_simp; ring
  have e2 : B * (X : ℝ) ^ 2 / L ^ 3 * L ^ 3 = B * (X : ℝ) ^ 2 := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hcomb hL3.le
  rw [e1, e2] at hmul
  have hXL : (X : ℝ) * L ^ 3 ≤ (X : ℝ) ^ 2 := by nlinarith
  have hcK : c ^ 2 * K / 4 ≤ c ^ 2 * L / 4 := by
    have := mul_le_mul_of_nonneg_left hX3 (sq_nonneg c); linarith
  have hX2pos : 0 < (X : ℝ) ^ 2 := by positivity
  have h5 : (B + 1) * (X : ℝ) ^ 2 < c ^ 2 * L / 4 * (X : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right (lt_of_lt_of_le hKB hcK) hX2pos
  linarith

-- Faithfulness check: the negated Prop is exactly the type of `leaf_circle_method_variance`.
#check (leaf_circle_method_variance_false leaf_circle_method_variance : False)

end LeanLab.OpenProblems.State1612

#print axioms LeanLab.OpenProblems.State1612.sum_Icc_natCast_ge_var
#print axioms LeanLab.OpenProblems.State1612.leaf_circle_method_variance_false
