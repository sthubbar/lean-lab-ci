/-
P0022, Kaniecki 1995. CLOUD 20261020T2317Z-cloud53, unit U-6774, T1, falsifier of the
U-6765 QUESTION on `Statements.Lemma4`.

`¬ Statements.Lemma4` cannot be proved in Lean without settling RH, since `Lemma4` has the
form `RH → P`. What is proved here: at `a = 2` there is a root `c*` in `[1/2, 1]` of
`(a - 1) c = e^{-c} + e^{-ac}`; there Lean reads `f₅ = 0` and `fK = f₁`, so `Lemma4` together
with RH forces the integral of (8) at `T = e^8`, `σ = 1/2 + c*/4` to be below `4.6 · 10^{-4}`.
mpmath puts that integral above this, see numerics/U6774_falsifier.out, so `Lemma4` would
refute RH: a theorem `Lemma4 → RH → X` is then vacuous.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995.L4F

open LeanLab.Kaniecki1995 Real

/-- `g(c) = (2 - 1) c - e^{-c} - e^{-2c}`, the denominator of `f₅ 2 c`. -/
noncomputable def g (c : ℝ) : ℝ := (2 - 1) * c - Real.exp (-c) - Real.exp (-(2 * c))

theorem g_half_neg : g (1 / 2) < 0 := by
  have h1 : (1 : ℝ) + (-(1 / 2)) ≤ Real.exp (-(1 / 2)) := by
    have := Real.add_one_le_exp (-(1 / 2 : ℝ)); linarith
  have h2 := Real.exp_pos (-(2 * (1 / 2 : ℝ)))
  unfold g; linarith

theorem g_one_pos : 0 < g 1 := by
  have h1 := Real.exp_neg_one_lt_d9
  have h0 := Real.exp_pos (-1)
  have h2 : Real.exp (-(2 * (1 : ℝ))) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp (-1) * Real.exp (-1) < 0.3678794412 * 0.3678794412 := by
    nlinarith
  unfold g; norm_num at h2 ⊢; rw [h2]; nlinarith

/-- A root `c*` of Lemma 3's boundary `(a - 1) c = e^{-c} + e^{-ac}` at `a = 2`. -/
theorem exists_root : ∃ c : ℝ, 1 / 2 ≤ c ∧ c ≤ 1 ∧ g c = 0 := by
  have hcont : ContinuousOn g (Set.Icc (1 / 2) 1) := by
    unfold g; fun_prop
  have := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1) hcont
  obtain ⟨c, ⟨h1, h2⟩, hc⟩ := this ⟨g_half_neg.le, g_one_pos.le⟩
  exact ⟨c, h1, h2, hc⟩

/-- At the root, Lean's `x / 0 = 0` gives `f₅ = 0`. -/
theorem f5_root {c : ℝ} (hc : g c = 0) : f5 2 c = 0 := by
  unfold g at hc; simp [f5, hc]

/-- At the root `fK = f₁`: the bound of `Statements.Lemma4` keeps only `f₁`. -/
theorem fK_root {c : ℝ} (hc : g c = 0) (T α : ℝ) : fK 2 c T α = f1 T := by
  simp [fK, f5_root hc]

theorem exp8_gt : (2980 : ℝ) < Real.exp 8 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 8 < Real.exp 1 ^ 8 := by gcongr
  have h2 : (2980 : ℝ) < 2.7182818283 ^ 8 := by norm_num
  linarith

/-- `f₁(e^8) · 8² / e^8 = 4032 / (e^8 - 7.02)² < 4.6 · 10^{-4}`. -/
theorem rhs_small : f1 (Real.exp 8) * Real.log (Real.exp 8) ^ 2 / Real.exp 8 < 4.6e-4 := by
  have hT := exp8_gt
  set T := Real.exp 8 with hTd
  have hT0 : 0 < T := by linarith
  have hd : 0 < T - 7.02 := by linarith
  have e : f1 T * Real.log T ^ 2 / T = 4032 / (T - 7.02) ^ 2 := by
    rw [hTd, Real.log_exp, ← hTd]
    unfold f1
    rw [hTd, Real.log_exp, ← hTd]
    have h1 : (1 - 7.02 / T) = (T - 7.02) / T := by field_simp
    rw [h1]
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **`Statements.Lemma4` with RH collapses at the root.** If `Lemma4` and RH hold, then for
the root `c*` of `exists_root`, `T = e^8` and `σ = 1/2 + c*/4 ≤ 3/4`, the integral of (8) is
below `4.6 · 10^{-4}`. PROVED, unconditional implication. -/
theorem lemma4_forces_small (h4 : Lemma4) (hRH : RiemannHypothesis) :
    ∃ c : ℝ, 1 / 2 ≤ c ∧ c ≤ 1 ∧ f5 2 c = 0 ∧
      lemma4Int (Real.exp 8) (sig 2 c (Real.exp 8)) < ENNReal.ofReal 4.6e-4 := by
  obtain ⟨c, hc1, hc2, hg⟩ := exists_root
  refine ⟨c, hc1, hc2, f5_root hg, ?_⟩
  have hT := exp8_gt
  have hs : sig 2 c (Real.exp 8) ≤ 3 / 4 := by
    unfold sig; rw [Real.log_exp]; linarith
  have h := h4 hRH 2 c (Real.exp 8) 2 (by linarith) (by linarith) (by norm_num) (by norm_num) hs
  rw [fK_root hg] at h
  refine lt_of_le_of_lt h ?_
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 rhs_small

end LeanLab.Kaniecki1995.L4F

#print axioms LeanLab.Kaniecki1995.L4F.exists_root
#print axioms LeanLab.Kaniecki1995.L4F.fK_root
#print axioms LeanLab.Kaniecki1995.L4F.rhs_small
#print axioms LeanLab.Kaniecki1995.L4F.lemma4_forces_small

