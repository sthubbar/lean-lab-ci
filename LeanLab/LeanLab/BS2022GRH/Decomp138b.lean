/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
Audit before decomposing Theorem 5, P0021 journal p. 1228.
The paper assumes N even. The sealed Thm5J omits this assumption.
The sealed sieve predicate is vacuous outside its epsilon range.
These are questions about the lab transcription, not claims of a paper error.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Cert1575Closed
namespace LeanLab.BS2022GRH.Decomp138b
open Real Finset Classical ChenThresholdGRH
open U7153

/-- Theorem 5 domain audit, p. 1228. On odd n the sifted set has at most one element. -/
theorem odd_sifted_le_one (n : ℕ) (hn : n % 2 = 1) (hz : 2 < zz n) : SA n ≤ 1 := by
  unfold SA
  have hsub : (Aset n).filter (NoSmallP n (zz n)) ⊆ {n - 2} := by
    intro a ha
    obtain ⟨haA, haS⟩ := mem_filter.mp ha
    obtain ⟨p, hp, rfl⟩ := mem_image.mp haA
    obtain ⟨hpn, hpprime, hpnodiv⟩ := mem_filter.mp hp
    have hp_le : p ≤ n := by have := mem_range.mp hpn; omega
    by_cases hp2 : p = 2
    · simp [hp2]
    · exfalso
      have hpodd := hpprime.eq_two_or_odd.resolve_left hp2
      have hn2 : ¬ 2 ∣ n := by omega
      have hna : 2 ∣ n - p := by omega
      exact haS 2 Nat.prime_two (by exact_mod_cast hz) hn2 hna
  exact (card_le_card hsub).trans (by simp)
/-- Theorem 4 domain audit, p. 1218. Outside the epsilon range the sealed predicate is vacuous. -/
theorem sieve_of_bad_epsilon (ε C₁ C₂ : ℝ) (hε : 1 / 63 ≤ ε) :
    LinearSieveT4 ε C₁ C₂ := by
  intro supp a P Q g z D ha hs hp hq hg he0 he1
  exact False.elim ((not_lt_of_ge hε) he1)

/-- Theorem 5 bracket audit, p. 1228. Negative C₂ makes the bracket unbounded above. -/
theorem bracket_unbounded (α A X N T : ℝ) (hα : α < 1 / 8)
    (hδ : 0 < 1 - 0.62 * log X / X ^ (1 / 16 : ℝ)) :
    ∃ C₂ : ℝ, T < B5J α A 1 C₂ X N := by
  let b := (1 - 0.62 * log X / X ^ (1 / 16 : ℝ)) *
    (3 * exp (8 * α - 2) / (4 - 8 * α))
  have hb : 0 < b := mul_pos hδ (div_pos (by positivity) (by linarith))
  have heq (C₂ : ℝ) : B5J α A 1 C₂ X N = B5J α A 1 0 X N - C₂ * b := by
    unfold B5J b
    ring
  refine ⟨(B5J α A 1 0 X N - T - 1) / b, ?_⟩
  rw [heq, div_mul_cancel₀ _ hb.ne']
  linarith

/-- Theorem 5 transcription audit, p. 1228.
The sealed predicate implies the negation of the lab GRH predicate because epsilon = 1
makes its sieve hypothesis vacuous and C₂ is unrestricted. This is a lab encoding issue. -/
theorem thm5J_excludes_grh (h5 : Thm5J) : ¬ GRH := by
  intro hGRH
  obtain ⟨n, hnEven, hn⟩ := threshold_nonvacuous
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (exp_pos _) hn
  have hn1 : (1 : ℝ) < n := lt_of_lt_of_le (by linarith [X2_ranges.1]) hn
  have hl : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hb : 0 < 8 * (UNfull n * (n : ℝ) / log n ^ 2) := by positivity
  have hdsmall := Cert1567.delta_small Journal.exp13375_ge
  have hd : 0 < 1 - 0.62 * log (exp (exp 13.375)) /
      (exp (exp 13.375)) ^ (1 / 16 : ℝ) := by
    rw [log_exp, ← exp_mul]
    linarith [hdsmall.2]
  obtain ⟨C₂, hC₂⟩ := bracket_unbounded 0.00256 10 (exp (exp 13.375)) n
    ((U7153.SA n : ℝ) / (8 * (UNfull n * n / log n ^ 2))) (by norm_num) hd
  have heps : epsJ 1500 ≤ 1 := by
    have he : epsJ 1500 < 1 / 8349 := Cert1575.eps1500
    linarith
  have h := h5 0.00256 10 1500 1 0 C₂ (exp (exp 13.375)) n hGRH
    (sieve_of_bad_epsilon 1 0 C₂ (by norm_num)) heps (by norm_num) (by norm_num)
    (by norm_num) cond19_13375 X2_ranges.1 hn
  have hrev : (U7153.SA n : ℝ) < 8 * (UNfull n * n / log n ^ 2) *
      B5J 0.00256 10 1 C₂ (exp (exp 13.375)) n := by
    simpa only [mul_comm] using (div_lt_iff₀ hb).mp hC₂
  linarith

/-- A concrete odd parameter instance for the domain audit of Theorem 5. -/
theorem odd_parameters_nonvacuous : 257 % 2 = 1 ∧ (2 : ℝ) < LeanLab.BS2022GRH.U7153.zz 257 := by
  constructor
  · norm_num
  · have he : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
      convert Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 8) (by norm_num) (by norm_num) using 1; norm_num
    have ht := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 256)
      (by norm_num : (256 : ℝ) < 257) (by norm_num : (0 : ℝ) < 1 / 8)
    simpa only [he, LeanLab.BS2022GRH.U7153.zz, Nat.cast_ofNat] using ht

end LeanLab.BS2022GRH.Decomp138b

#print axioms LeanLab.BS2022GRH.Decomp138b.odd_sifted_le_one
#print axioms LeanLab.BS2022GRH.Decomp138b.sieve_of_bad_epsilon
#print axioms LeanLab.BS2022GRH.Decomp138b.bracket_unbounded

#print axioms LeanLab.BS2022GRH.Decomp138b.thm5J_excludes_grh

#print axioms LeanLab.BS2022GRH.Decomp138b.odd_parameters_nonvacuous
