/-
AI wrote this Lean code, Claude, for the Lean Lab, run 20261028T0803Z-11675, unit U-1580.
Faithfulness audit of the four cited deep inputs of the I-0088 threshold after the 2026-10-27
statement fix: `Thm5J`, `Thm6J`, `Thm7J` and `LinearSieveT4 (1/8349) 112 114`.
Source: Bordignon, Starichkova, Ramanujan J. 64 (2024) 1213-1242, Theorem 4 p. 1218,
Theorems 5, 6, 7 pp. 1228, 1231, 1234-1235.

What is proved here:
* `thm5J_imp_not_GRH`: the pre-fix `Thm5J` refutes GRH, the reason for the fix; an alias of
  `Decomp138b.thm5J_excludes_grh`, now stated against the archived `Decomp138b.Thm5JOld`.
* `sieveT4_trivial`: any `LinearSieveT4 ε C₁ C₂` with `0 < ε < 1/63` forces, through the one
  element sequence with no sifting primes, the upper coefficient at least 1 and the lower
  coefficient at most 1, at every s = log D / log 2 in range.
* `sieveT4_not_vacuous`: inside the range the predicate has content: with `ε C₂ < -1` it is false.
  So the ε = 1 vacuity that sank the old leaves is gone and no choice of C makes it vacuous.
* `eps_C2_ge`, `thm7_bracket_ge_three`: the constants a true `LinearSieveT4` admits are bounded
  below, so the unbounded C attacks `Decomp138b.bracket_unbounded`, `Audit138c.b6_negative`,
  `Audit138c.b7_negative` cannot be fed a sieve witness any more.
* `thm5J_hyps_instance`, `thm6J_hyps_instance`, `thm7J_hyps_instance`: every hypothesis of the
  fixed leaves other than GRH and `LinearSieveT4` holds together at the I-0088 parameters.

These are statements about the lab encoding, not claims of an error in the paper.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.Audit138c
namespace LeanLab.BS2022GRH.Audit1580
open Real Finset Classical ChenThresholdGRH

/-- The pre-fix `Thm5J` implies the negation of the lab GRH predicate, the reason for the
2026-10-27 fix. Lab transcription audit, CONDITIONAL ON the archived predicate. -/
theorem thm5J_imp_not_GRH (h5 : Decomp138b.Thm5JOld) : ¬ GRH :=
  Decomp138b.thm5J_excludes_grh h5

/-- The one element sequence `a = 1` at `n = 1`, no sifting primes, `z = 2`: every premise of
Theorem 4 holds, S = X = 1 and R = 0, so the two coefficients straddle 1. -/
theorem sieveT4_trivial {ε C₁ C₂ : ℝ} (hT : LinearSieveT4 ε C₁ C₂) (h0 : 0 < ε)
    (h1 : ε < 1 / 63) (D : ℝ) (hD : 2 ≤ D) :
    (log D / log 2 ≤ 3 →
      1 ≤ 2 * exp eulerMascheroniConstant / (log D / log 2)
        + ε * C₁ * exp 2 * hS (log D / log 2)) ∧
    (4 ≤ D → log D / log 2 ≤ 4 →
      2 * exp eulerMascheroniConstant * log (log D / log 2 - 1) / (log D / log 2)
        - ε * C₂ * exp 2 * hS (log D / log 2) ≤ 1) := by
  have h1D : (1 : ℝ) < D := by linarith
  have H := hT {1} (fun n => if n = 1 then 1 else 0) ∅ ∅ (fun _ _ => 0) 2 D
    (fun n => by split_ifs <;> norm_num)
    (fun n hn => by
      have : n ≠ 1 := by simpa using hn
      simp [this])
    (fun p hp => absurd hp (Set.notMem_empty p))
    (by simp)
    (fun n p hp => absurd hp (Set.notMem_empty p))
    h0 h1 le_rfl
    (by
      intro n u hu1 hu2
      have hlu : 0 < log u := log_pos hu1
      have hlt : log u < log 2 := log_lt_log (by linarith) hu2
      have hr : 1 < log 2 / log u := (one_lt_div hlu).mpr hlt
      simp
      nlinarith)
  simp at H
  simp only [Finset.sum_filter, Finset.sum_singleton] at H
  simp at H
  refine ⟨fun hs => ?_, fun h4 hs => ?_⟩
  · have := H.1 hD hs
    linarith
  · have hz : (2 : ℝ) ^ 2 ≤ D := by norm_num; exact h4
    have := H.2 hz hs
    linarith

/-- Inside its range the sieve predicate is not vacuous: `ε C₂ < -1` refutes it. -/
theorem sieveT4_not_vacuous {ε C₁ C₂ : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 63)
    (hC : ε * C₂ < -1) : ¬ LinearSieveT4 ε C₁ C₂ := by
  intro hT
  have h := (sieveT4_trivial hT h0 h1 4 (by norm_num)).2 le_rfl
  have hs : log (4 : ℝ) / log 2 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
    push_cast
    field_simp
  rw [hs] at h
  have hh : hS 2 = exp (-2) := by simp [hS]
  rw [hh] at h
  have he : exp 2 * exp (-2) = 1 := by rw [← exp_add]; simp
  have : (2 : ℝ) - 1 = 1 := by norm_num
  rw [this, log_one] at h
  have h2 : ε * C₂ * exp 2 * exp (-2) = ε * C₂ := by
    rw [mul_assoc, he, mul_one]
  rw [h2] at h
  norm_num at h
  linarith

/-- A true `LinearSieveT4 ε C₁ C₂` has `ε C₂ ≥ -1`, so `B5J` is bounded above along sieve
witnesses and the unbounded C₂ attack of `Decomp138b.bracket_unbounded` has no witness. -/
theorem eps_C2_ge {ε C₁ C₂ : ℝ} (hT : LinearSieveT4 ε C₁ C₂) (h0 : 0 < ε)
    (h1 : ε < 1 / 63) : -1 ≤ ε * C₂ := by
  by_contra h
  exact sieveT4_not_vacuous (C₁ := C₁) h0 h1 (by linarith) hT

/-- At s = 3/2 − 3α, the s of Theorem 7, p. 1236, a true `LinearSieveT4` gives
`2/(1/2 − α) e^γ + 3 ε C₁ ≥ 3`, so the Theorem 7 main bracket stays positive and the
unbounded C₁ attack of `Audit138c.b7_negative` has no sieve witness. -/
theorem thm7_bracket_ge_three {ε C₁ C₂ α : ℝ} (hT : LinearSieveT4 ε C₁ C₂) (h0 : 0 < ε)
    (h1 : ε < 1 / 63) (hα0 : 0 ≤ α) (hα1 : α < 1 / 16) :
    3 ≤ 2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁ := by
  set s : ℝ := 3 / 2 - 3 * α with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; linarith
  have hs2 : s ≤ 2 := by rw [hsdef]; linarith
  have hD : (2 : ℝ) ≤ (2 : ℝ) ^ s := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
      _ ≤ 2 ^ s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
  have hlog : log ((2 : ℝ) ^ s) / log 2 = s := by
    rw [Real.log_rpow (by norm_num)]
    have : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
    field_simp
  have h := (sieveT4_trivial hT h0 h1 ((2 : ℝ) ^ s) hD).1
  rw [hlog] at h
  have h' := h (by linarith)
  have hh : hS s = exp (-2) := by simp [hS, hs2]
  rw [hh] at h'
  have he : exp 2 * exp (-2) = 1 := by rw [← exp_add]; simp
  have h2 : ε * C₁ * exp 2 * exp (-2) = ε * C₁ := by rw [mul_assoc, he, mul_one]
  rw [h2] at h'
  have hspos : 0 < s := by linarith
  have hk : 2 / (1 / 2 - α) = 3 * (2 / s) := by
    rw [hsdef]
    have : (1 / 2 - α) ≠ 0 := by intro h; linarith
    have : (3 / 2 - 3 * α) ≠ 0 := by intro h; linarith
    field_simp
  rw [hk]
  have : 2 * exp eulerMascheroniConstant / s = 2 / s * exp eulerMascheroniConstant := by ring
  nlinarith

/-- Every hypothesis of the fixed `Thm5J` except GRH and the sieve holds together at the
I-0088 parameters. -/
theorem thm5J_hyps_instance : ∃ n : ℕ,
    epsJ 1500 ≤ 1 / 8349 ∧ (0 : ℝ) < 1 / 8349 ∧ (1 / 8349 : ℝ) < 1 / 63 ∧
    (0 : ℝ) < 0.00256 ∧ (0.00256 : ℝ) < 1 / 8 ∧ (0 : ℝ) < 10 ∧
    Cond19 0.00256 10 1500 (exp (exp 13.375)) ∧ (4e18 : ℝ) ≤ exp (exp 13.375) ∧
    exp (exp 13.375) ≤ (n : ℝ) ∧ Even n := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  exact ⟨n, Cert1575.eps1500.le, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, cond19_13375, X2_ranges.1, hn, hev⟩

/-- The same for the fixed `Thm6J`. -/
theorem thm6J_hyps_instance : ∃ n : ℕ,
    epsJ 1500 ≤ 1 / 8349 ∧ (0 : ℝ) < 1 / 8349 ∧ (1 / 8349 : ℝ) < 1 / 63 ∧
    (0 : ℝ) < 0.00256 ∧ (0.00256 : ℝ) < 1 / 24 ∧ (0 : ℝ) < 10 ∧
    Cond19 0.00256 10 1500 (exp (exp 13.375)) ∧ exp (exp 10) ≤ exp (exp 13.375) ∧
    exp (exp 13.375) ≤ (n : ℝ) ∧ Even n := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  exact ⟨n, Cert1575.eps1500.le, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, cond19_13375, X2_ranges.2, hn, hev⟩

/-- The same for the fixed `Thm7J`, with ε₁ = 10⁻²⁰. -/
theorem thm7J_hyps_instance : ∃ n : ℕ,
    epsJ 1500 ≤ 1 / 8349 ∧ (0 : ℝ) < 1 / 8349 ∧ (1 / 8349 : ℝ) < 1 / 63 ∧
    (0 : ℝ) < 1e-20 ∧ (1e-20 : ℝ) < 1 ∧
    (0 : ℝ) < 0.00256 ∧ (0.00256 : ℝ) < 1 / 16 ∧ (0 : ℝ) < 10 ∧
    Cond25 0.00256 10 1500 (exp (exp 13.375)) ∧ exp (exp 10) ≤ exp (exp 13.375) ∧
    exp (exp 13.375) ≤ (n : ℝ) ∧ Even n := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  exact ⟨n, Cert1575.eps1500.le, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, cond25_13375, X2_ranges.2, hn, hev⟩

end LeanLab.BS2022GRH.Audit1580

#print axioms LeanLab.BS2022GRH.Audit1580.thm5J_imp_not_GRH
#print axioms LeanLab.BS2022GRH.Audit1580.sieveT4_trivial
#print axioms LeanLab.BS2022GRH.Audit1580.sieveT4_not_vacuous
#print axioms LeanLab.BS2022GRH.Audit1580.eps_C2_ge
#print axioms LeanLab.BS2022GRH.Audit1580.thm7_bracket_ge_three
#print axioms LeanLab.BS2022GRH.Audit1580.thm5J_hyps_instance
#print axioms LeanLab.BS2022GRH.Audit1580.thm6J_hyps_instance
#print axioms LeanLab.BS2022GRH.Audit1580.thm7J_hyps_instance
