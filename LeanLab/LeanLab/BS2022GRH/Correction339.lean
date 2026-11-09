/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Normalize the coprimality correction in journal display 32, p. 1240.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Bilinear339
import LeanLab.BS2022GRH.Decomp406d

namespace LeanLab.BS2022GRH.Correction339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The divisor cutoff is below square root n, journal p. 1240.
This uses only positivity of A and the large logarithm. -/
theorem Dstar_le_sqrt (n : ℕ) (A : ℝ) (hL : 1 ≤ log (n : ℝ)) (hA : 0 < A) :
    √(n : ℝ) / log n ^ (A + 1) ≤ √(n : ℝ) := by
  exact div_le_self (sqrt_nonneg _) (one_le_rpow hL (by linarith))

/-- The large input makes the double logarithm of square root n exceed one.
This gives room for the correction rounding on p. 1240. -/
theorem log_log_sqrt_ge_one (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    1 ≤ log (log (√(n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  have hs : exp 1 ≤ log (√(n : ℝ)) := by
    rw [log_sqrt hn0.le]
    linarith [exp_one_lt_d9]
  simpa only [log_exp] using log_le_log (exp_pos 1) hs

/-- Uniform omega control on the actual sifting divisor range.
CONDITIONAL ON Robin Lemma 4. Journal p. 1240 below display 32. -/
theorem divisor_omega_le (h4 : PaperInputs148.Lemma4J) (n d : ℕ) (A : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hA : 0 < A) (hd : d ∈ divisors n A) :
    (d.primeFactors.card : ℝ) ≤ 0.69205 * log n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  have hs : (5 : ℝ) ≤ √(n : ℝ) := by
    apply le_sqrt_of_sq_le
    have hh := log_le_sub_one_of_pos hn0
    nlinarith
  have hs0 : 0 < log (√(n : ℝ)) := by rw [log_sqrt hn0.le]; linarith
  have hll := log_log_sqrt_ge_one n hn
  have hd' := SliceRemainder236.divisor_spec hd
  have hds : (d : ℝ) < √(n : ℝ) :=
    hd'.2.2.2.trans_le (Dstar_le_sqrt n A (by linarith) hA)
  calc
    _ ≤ 1.3841 * log (√(n : ℝ)) / log (log (√(n : ℝ))) :=
      Decomp406d.uniform_omega_bound h4 _ d hs hd'.2.2.1 hds
    _ ≤ 1.3841 * log (√(n : ℝ)) := div_le_self (by positivity) hll
    _ = _ := by rw [log_sqrt hn0.le]; ring

/-- The complete coprimality correction fits the printed 0.374 budget.
CONDITIONAL ON the two stated published inputs. Journal p. 1240 display 32.
There is no bilinear estimate in this statement. -/
theorem correction_bound (h4 : PaperInputs148.Lemma4J) (hPhi : PaperInputs148.Lemma5PhiJ)
    (n j : ℕ) (A ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ)) (hA : 0 < A)
    (hε : 0 < ε₁) (hD : 1e8 ≤ √(n : ℝ) / log n ^ (A + 1)) :
    (∑ d ∈ divisors n A, SliceRemainder236.badCount n j d ε₁ / d.totient) ≤
      0.374 * ((1 + ε₁) * (n : ℝ) ^ (7 / 8 : ℝ) * log n ^ 2) := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnN : 0 < n := by exact_mod_cast hn0
  have hL := Lemma11C164.log_lower n hn
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hDs : √(n : ℝ) / log n ^ (A + 1) ≤ √(n : ℝ) :=
    Dstar_le_sqrt n A (by linarith) hA
  have hD0 : 0 < √(n : ℝ) / log n ^ (A + 1) := by positivity
  have hld : 0 ≤ log (√(n : ℝ) / log n ^ (A + 1)) :=
    log_nonneg (by linarith)
  have hlDs : log (√(n : ℝ) / log n ^ (A + 1)) ≤ log n / 2 := by
    simpa only [log_sqrt hn0.le] using log_le_log hD0 hDs
  have hPhiM := Lemma5Coeffs138.Mphi_le1073 _ hD
  have hcoef : Mphi (√(n : ℝ) / log n ^ (A + 1)) *
      log (√(n : ℝ) / log n ^ (A + 1)) ≤ 1.073 * (log n / 2) :=
    mul_le_mul hPhiM hlDs hld (by norm_num)
  have hb : 0 ≤ (1 + ε₁) * (n : ℝ) / U7153.zz n := by unfold U7153.zz; positivity
  have ho : 0 ≤ 0.69205 * log (n : ℝ) := by positivity
  have hs := SliceRemainder236.correction_sum_of_omega_phi n j A ε₁
    (0.69205 * log n) hPhi hnN hε ho (by linarith)
    (fun d hd => divisor_omega_le h4 n d A hn hA hd)
  have he : (n : ℝ) / U7153.zz n = (n : ℝ) ^ (7 / 8 : ℝ) := by
    unfold U7153.zz
    nth_rw 1 [← rpow_one (n : ℝ)]
    rw [← rpow_sub hn0]
    norm_num
  calc
    _ ≤ ((1 + ε₁) * n / U7153.zz n) * (0.69205 * log n) *
        (Mphi (√(n : ℝ) / log n ^ (A + 1)) *
          log (√(n : ℝ) / log n ^ (A + 1))) := by simpa only [mul_assoc] using hs
    _ ≤ ((1 + ε₁) * n / U7153.zz n) * (0.69205 * log n) *
        (1.073 * (log n / 2)) := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hb ho)
    _ ≤ 0.374 * ((1 + ε₁) * (n : ℝ) ^ (7 / 8 : ℝ) * log n ^ 2) := by
      rw [mul_div_assoc, he]
      have ht : 0 ≤ (1 + ε₁) * (n : ℝ) ^ (7 / 8 : ℝ) * log n ^ 2 := by positivity
      nlinarith only [ht]

end
end LeanLab.BS2022GRH.Correction339
#print axioms LeanLab.BS2022GRH.Correction339.Dstar_le_sqrt
#print axioms LeanLab.BS2022GRH.Correction339.log_log_sqrt_ge_one
#print axioms LeanLab.BS2022GRH.Correction339.divisor_omega_le
#print axioms LeanLab.BS2022GRH.Correction339.correction_bound
