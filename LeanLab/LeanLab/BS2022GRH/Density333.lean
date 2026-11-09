/- AI wrote the Lean code for CODEX task333. Goldbach is open.
The density estimate on the full condition 19 domain of Theorem 5.
Journal pp. 1227 to 1229 and Schoenfeld p. 340 display 6.21. -/
import LeanLab.BS2022GRH.Reciprocal333
import LeanLab.BS2022GRH.Density410
import LeanLab.BS2022GRH.Mertens410

namespace LeanLab.BS2022GRH.Density333
open Real Finset ChenThresholdGRH

/-- On the condition 19 logarithmic range, the density lower bound follows
from the prime count input already used in the cardinality and residue steps.
Journal Lemma 10 p. 1227 and Schoenfeld p. 340 display 6.21.
CONDITIONAL ON Lemma1J and GRH. No separate RH reciprocal input is used. -/
theorem density_lower_of_prime_count (h1 : PaperInputs148.Lemma1J)
    (n : ℕ) (hG : GRH) (hn : (4e18 : ℝ) ≤ n) (hev : Even n)
    (hL : 3200 ≤ log (n : ℝ)) :
    8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤
      DecompC169a.density n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hLz : 400 ≤ log (U7153.zz n) := by
    rw [U7153.zz, log_rpow hn0]
    linarith
  have hz400 : exp 400 ≤ U7153.zz n := (le_log_iff_exp_le hz0).mp hLz
  have hz2657 : 2657 ≤ U7153.zz n := by
    have he := pow_div_factorial_le_exp (x := (400 : ℝ)) (by norm_num) 2
    norm_num [Nat.factorial] at he
    linarith
  apply Density410.density_lower_of_mertens n hn hev
  apply Mertens410.ordinary_product_lower_of_reciprocal _ _ (by linarith : 1 < U7153.zz n)
  have h := Reciprocal333.reciprocal_upper_of_prime_count h1 (RH148.rh_of_grh hG)
    (U7153.zz n) hz2657
  unfold PrimeAbel333.reciprocalSum at h
  have he : (3 * log (U7153.zz n) + 4) / (8 * π * √(U7153.zz n)) ≤
      (3 * log (U7153.zz n) + 5) / (8 * π * √(U7153.zz n)) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

end LeanLab.BS2022GRH.Density333

#print axioms LeanLab.BS2022GRH.Density333.density_lower_of_prime_count
