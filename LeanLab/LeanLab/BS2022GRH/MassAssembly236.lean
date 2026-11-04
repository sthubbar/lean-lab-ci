/- AI wrote the Lean code for CODEX task236.
Lemma 14 assembly with the weighted Mertens input explicit. Goldbach is open. -/
import LeanLab.BS2022GRH.MassInputs236
import LeanLab.BS2022GRH.SchoenfeldEnvelope236
import LeanLab.BS2022GRH.Lemma11C164
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The pair cutoff gives the two logarithmic count domains, journal p. 1237. -/
theorem pair_count_domains (n : ℕ) (ε₁ : ℝ) (q : ℕ × ℕ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1)
    (hq : q ∈ pairRange n ε₁) :
    exp 11 ≤ U7153.yy n ∧
    U7153.yy n ≤ (1 + ε₁) * n / ((q.1 : ℝ) * q.2) ∧
    1 < (n : ℝ) / ((q.1 : ℝ) * q.2) := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  have hy0 : 0 < U7153.yy n := rpow_pos_of_pos hn0 _
  have hyexp : exp 11 ≤ U7153.yy n := by
    apply (le_log_iff_exp_le hy0).mp
    rw [U7153.yy, log_rpow hn0]
    linarith
  obtain ⟨_, hp1, hp2, _, _, hyp2, hprod⟩ := mem_filter.mp hq
  have hp1R : (0 : ℝ) < q.1 := by exact_mod_cast hp1.pos
  have hp2R : (0 : ℝ) < q.2 := by exact_mod_cast hp2.pos
  have hqp : (0 : ℝ) < (q.1 : ℝ) * q.2 := mul_pos hp1R hp2R
  have hyq : U7153.yy n < (1 + ε₁) * n / ((q.1 : ℝ) * q.2) := by
    apply lt_of_le_of_lt hyp2
    rw [lt_div_iff₀ hqp]
    nlinarith
  have hq2 : (2 : ℝ) ≤ q.2 := by exact_mod_cast hp2.two_le
  have hqq : (q.1 : ℝ) * q.2 < n := by
    have hmul := mul_le_mul_of_nonneg_left hq2 hqp.le
    have hb : (1 + ε₁) * (n : ℝ) < 2 * n := by nlinarith
    nlinarith
  exact ⟨hyexp, hyq.le, (one_lt_div hqp).mpr hqq⟩

/-- Apply the uniform Schoenfeld count to every admissible pair, journal p. 1237.
CONDITIONAL ON Schoenfeld Corollary 1 and GRH. -/
theorem mass_le_schoenfeld_pair (h1 : PaperInputs148.Lemma1J) (hG : GRH)
    (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    mass n ε₁ ≤ (1 + ε₁) * primeEnvelope (U7153.yy n) * n * pairWeightSum n ε₁ := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  apply mass_le_pairWeight n ε₁ _ hnN hε
  intro q hq
  obtain ⟨hy, hyx, hbase⟩ := pair_count_domains n ε₁ q hn hε hε1 hq
  obtain ⟨_, hp1, hp2, _⟩ := mem_filter.mp hq
  have hp1R : (0 : ℝ) < q.1 := by exact_mod_cast hp1.pos
  have hp2R : (0 : ℝ) < q.2 := by exact_mod_cast hp2.pos
  have hqp : (0 : ℝ) < (q.1 : ℝ) * q.2 := mul_pos hp1R hp2R
  have hx0 : 0 < (1 + ε₁) * (n : ℝ) / ((q.1 : ℝ) * q.2) := by positivity
  have hbase0 : 0 < (n : ℝ) / ((q.1 : ℝ) * q.2) := div_pos hn0 hqp
  have hlogb : 0 < log ((n : ℝ) / ((q.1 : ℝ) * q.2)) := log_pos hbase
  have hlog : log ((n : ℝ) / ((q.1 : ℝ) * q.2)) ≤
      log ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) := by
    apply log_le_log hbase0
    apply div_le_div_of_nonneg_right _ hqp.le
    nlinarith
  have hy0 : 0 < U7153.yy n := rpow_pos_of_pos hn0 _
  have hFy : 0 ≤ primeEnvelope (U7153.yy n) := by
    unfold primeEnvelope normalizedLi
    have hli := li_lower_three_terms (U7153.yy n) hy
    have hly : 0 < log (U7153.yy n) := by
      apply log_pos
      exact (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 11)).trans_le hy
    have hli0 : 0 ≤ liPV (U7153.yy n) := le_trans (by positivity) hli
    positivity
  have hc := prime_count_uniform h1 hG (U7153.yy n)
    ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) hy hyx
  rw [← primeEnvelope_eq _ hy0] at hc
  calc
    PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) ≤ _ := hc
    _ ≤ primeEnvelope (U7153.yy n) * ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) /
        log ((n : ℝ) / ((q.1 : ℝ) * q.2)) :=
      div_le_div_of_nonneg_left (mul_nonneg hFy hx0.le) hlogb hlog
    _ = _ := by ring

/-- Assemble Lemma 14 after the two named published estimates, journal pp. 1237 to 1239.
CONDITIONAL ON Schoenfeld Corollary 1, GRH and the weighted Mertens error. -/
theorem mass_bound_of_inputs (h1 : PaperInputs148.Lemma1J) (hG : GRH)
    (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1)
    (hWeighted : pairWeightSum n ε₁ ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁) :
    mass n ε₁ ≤ massBound n ε₁ := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  have hy0 : 0 < U7153.yy n := rpow_pos_of_pos hn0 _
  have hF : 0 ≤ primeEnvelope (U7153.yy n) := by
    rw [primeEnvelope_eq _ hy0]
    have hyy : exp 11 ≤ U7153.yy n := by
      apply (le_log_iff_exp_le hy0).mp
      rw [U7153.yy, log_rpow hn0]
      linarith [Lemma11C164.log_lower n hn]
    have hli := li_lower_three_terms (U7153.yy n) hyy
    have hlog : 0 < log (U7153.yy n) := by
      rw [U7153.yy, log_rpow hn0]
      exact mul_pos (by norm_num) (log_pos hn1)
    have hli0 : 0 ≤ liPV (U7153.yy n) := le_trans (by positivity) hli
    positivity
  have hC : 0 ≤ (1 + ε₁) * primeEnvelope (U7153.yy n) * n := by positivity
  have hi := outer_integral_eq_cbar (n : ℝ) hn1
  change (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) = _ at hi
  rw [hi] at hWeighted
  calc
    mass n ε₁ ≤ _ := mass_le_schoenfeld_pair h1 hG n ε₁ hn hε hε1
    _ ≤ ((1 + ε₁) * primeEnvelope (U7153.yy n) * n) *
        (LeanLab.ChenExplicit.BJS.cbar / log n + 36 / log n ^ 3 +
          (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁) :=
      mul_le_mul_of_nonneg_left hWeighted hC
    _ = massBound n ε₁ := by
      rw [primeEnvelope_eq _ hy0]
      rfl

end
end LeanLab.BS2022GRH.SliceMass236
#print axioms LeanLab.BS2022GRH.SliceMass236.pair_count_domains
#print axioms LeanLab.BS2022GRH.SliceMass236.mass_le_schoenfeld_pair
#print axioms LeanLab.BS2022GRH.SliceMass236.mass_bound_of_inputs
