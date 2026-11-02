/- AI wrote this Lean code for CODEX task232.
Published analytic inputs for DecompC169b. Goldbach is open. -/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.PublishedInputs232
open Real Finset ChenThresholdGRH

/-- LEAF. Journal Lemma 5 p. 1216, Buthe 2014 display 4.6.
The squarefree count is the Mobius square sum. -/
theorem lemma5_mu : PaperInputs148.Lemma5MuJ := by
  sorry

/-- LEAF. Journal Lemma 5 p. 1216, Ramare 2019 Theorem 3.1.
Keep the reciprocal totient weight rather than replacing it by one. -/
theorem lemma5_phi : PaperInputs148.Lemma5PhiJ := by
  sorry

/-- LEAF. Schoenfeld Corollary 1, journal Lemma 1 p. 1215. -/
theorem lemma1_schoenfeld : PaperInputs148.Lemma1J := by
  sorry

/-- LEAF. Robin Theorem 11, journal Lemma 4 p. 1216. -/
theorem lemma4_robin : PaperInputs148.Lemma4J := by
  sorry

/-- LEAF. Rosser and Schoenfeld 1962 Theorem 18, journal Lemma 2 p. 1215. -/
theorem lemma2_theta : PaperInputs148.Lemma2J := by
  sorry

/-- LEAF. Weighted reciprocal prime sum, journal p. 1234 first display.
Bordignon and Starichkova apply reference 7 Lemma 1 part ii and evaluate the integral. -/
theorem weighted_reciprocal_primes (n : ℕ) (α : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hα : 0 < α) (hα1 : α < 1 / 24) :
    (∑ q ∈ U7153.Qset n,
      (1 : ℝ) / ((q : ℝ) * log ((n : ℝ) ^ (1 / 2 - α) / q))) ≤
      (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / ((1 / 2 - α) * log n) +
        512 / (kA α * log n ^ 3) := by
  sorry

/-- LEAF. Unweighted reciprocal prime interval, journal p. 1234.
Rosser and Schoenfeld reference 16 Theorem 5. The lower endpoint is inclusive. -/
theorem reciprocal_prime_interval (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    (∑ q ∈ U7153.Qset n, (1 : ℝ) / q) ≤ log (8 / 3) + 64 / log n ^ 2 := by
  sorry

/-- A concrete nonempty domain check for the squarefree counting input, p. 1216. -/
theorem lemma5_mu_one_instance :
    ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤
      Lemma5Coeffs138.mMu 1 * 1 := by
  have hcard : ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤ 1 := by
    have h := card_filter_le (Icc 1 ⌊(1 : ℝ)⌋₊) (fun n => Squarefree n)
    norm_num at h ⊢
    exact_mod_cast h
  have hπ : π ^ 2 ≤ (16 : ℝ) := by nlinarith [pi_pos, pi_lt_four]
  have hdiv : (6 : ℝ) / 16 ≤ 6 / π ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hπ
  apply hcard.trans
  norm_num [Lemma5Coeffs138.mMu]
  linarith

/-- A concrete nonempty weighted domain check for Lemma 5, p. 1216. -/
theorem lemma5_phi_two_instance :
    (∑ n ∈ (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient) ≤
      Mphi 2 * log 2 := by
  have hset : (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n) = {1, 2} := by
    ext n
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    norm_num only [Nat.floor_ofNat] 
    constructor
    · intro h
      omega
    · intro h
      rcases h with rfl | rfl
      · norm_num
      · exact ⟨⟨by norm_num, le_rfl⟩, Nat.prime_two.squarefree⟩
  rw [hset]
  norm_num only [sum_insert, mem_singleton, reduceCtorEq, not_false_eq_true, sum_singleton,
    Nat.totient_one, Nat.totient_two, Nat.cast_one, div_one]
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmin : 0 ≤ min (2.44 / (√(2 : ℝ) * log 2)) (11 / (√(2 : ℝ) * log 2 ^ 2)) := by positivity
  have hmul := mul_nonneg hmin hlog.le
  calc
    (2 : ℝ) ≤ log 2 + 1.333 := by linarith [log_two_gt_d9]
    _ ≤ log 2 + 1.333 + min (2.44 / (√(2 : ℝ) * log 2))
        (11 / (√(2 : ℝ) * log 2 ^ 2)) * log 2 := le_add_of_nonneg_right hmul
    _ = _ := by unfold Mphi; field_simp

/-- LEAF. The two logarithmic integral bounds printed in the proof of Lemma 11, p. 1228.
The principal value convention is the existing lab liPV. -/
theorem li_bounds_large (n : ℕ) (hn : exp 11 ≤ (n : ℝ)) :
    (1 + 1 / log (n : ℝ)) * n / log n ≤ liPV n ∧
      liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n := by
  sorry

/-- LEAF. The upper half of journal Lemma 10 at z, pp. 1227 and 1232 display 23.
The lab UNfull convention is retained. This is a non-strict upper estimate. -/
theorem density_upper (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    DecompC169a.density n ≤ 8 * UNfull n / log n *
      (1 + 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) := by
  sorry

end LeanLab.BS2022GRH.PublishedInputs232
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma1_schoenfeld
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma4_robin
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma2_theta

#print axioms LeanLab.BS2022GRH.PublishedInputs232.weighted_reciprocal_primes

#print axioms LeanLab.BS2022GRH.PublishedInputs232.reciprocal_prime_interval

#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu_one_instance
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi_two_instance

#print axioms LeanLab.BS2022GRH.PublishedInputs232.li_bounds_large
#print axioms LeanLab.BS2022GRH.PublishedInputs232.density_upper
