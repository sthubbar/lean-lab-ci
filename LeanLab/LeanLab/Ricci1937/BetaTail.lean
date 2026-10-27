import LeanLab.Ricci1937.Tau23

/-!
Ricci 1937, page 78 formula 1.11 and page 81 formula 2.6.
Elementary majorant for the beta bar tail.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- The positive factorial majorant in the beta bar coefficient. -/
def ricciBetaMajorant (q : ℝ) (b : ℕ) : ℝ :=
  q ^ b * (b : ℝ) ^ (2 * b - 1) / ((2 * b).factorial : ℝ)

/-- The exact ratio of two consecutive factorial majorants. -/
lemma ricciBetaMajorant_succ {b : ℕ} (hb : 1 ≤ b) (q : ℝ) :
    ricciBetaMajorant q (b + 1) = ricciBetaMajorant q b * q *
      (((b : ℝ) + 1) / b) ^ (2 * b - 1) *
      (((b : ℝ) + 1) / (2 * (2 * b + 1))) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hf0 : ((2 * b).factorial : ℝ) ≠ 0 := by positivity
  have hexp : 2 * (b + 1) - 1 = (2 * b - 1) + 2 := by omega
  have hfac : (2 * (b + 1)).factorial = (2 * b + 2) * (2 * b + 1) * (2 * b).factorial := by
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    ring
  unfold ricciBetaMajorant
  rw [hexp, hfac, pow_add, pow_succ, div_pow]
  push_cast
  field_simp
  ring

/-- The exponential estimate in the ratio is uniform in b. -/
lemma ricciBeta_ratio_power {b : ℕ} (hb : 1 ≤ b) :
    (((b : ℝ) + 1) / b) ^ (2 * b - 1) ≤ exp 2 := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbase : ((b : ℝ) + 1) / b ≤ exp (1 / b) := by
    have h := add_one_le_exp (1 / (b : ℝ))
    convert h using 1
    field_simp
    ring
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((b : ℝ) + 1) / b)
    hbase (2 * b - 1)
  have hcast : ((2 * b - 1 : ℕ) : ℝ) ≤ 2 * b := by
    exact_mod_cast (Nat.sub_le (2 * b) 1)
  calc
    (((b : ℝ) + 1) / b) ^ (2 * b - 1) ≤ exp (1 / (b : ℝ)) ^ (2 * b - 1) := hp
    _ = exp (((2 * b - 1 : ℕ) : ℝ) / b) := by rw [← exp_nat_mul]; congr 1; ring
    _ ≤ exp 2 := exp_le_exp.mpr ((div_le_iff₀ hbpos).mpr (by linarith))

/-- A geometric ratio for every tail term after b = 4. -/
theorem ricciBetaMajorant_ratio {b : ℕ} (hb : 4 ≤ b) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 0.413) :
    ricciBetaMajorant q (b + 1) ≤ (0.86 : ℝ) * ricciBetaMajorant q b := by
  have hbR : (4 : ℝ) ≤ b := by exact_mod_cast hb
  have hfac : (((b : ℝ) + 1) / (2 * (2 * b + 1))) ≤ 5 / 18 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have he : exp 2 ≤ (7.39 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    have h := exp_one_lt_d9
    have h0 := exp_pos 1
    nlinarith
  have hpower := ricciBeta_ratio_power (b := b) (by omega)
  have ht0 : 0 ≤ ricciBetaMajorant q b := by unfold ricciBetaMajorant; positivity
  rw [ricciBetaMajorant_succ (by omega)]
  have h1 := mul_le_mul hq (hpower.trans he) (by positivity : (0 : ℝ) ≤
    (((b : ℝ) + 1) / b) ^ (2 * b - 1)) (by norm_num : (0 : ℝ) ≤ 0.413)
  have h2 := mul_le_mul h1 hfac (by positivity : (0 : ℝ) ≤
    ((b : ℝ) + 1) / (2 * (2 * b + 1))) (by norm_num : (0 : ℝ) ≤ 0.413 * 7.39)
  have h3 := mul_le_mul_of_nonneg_left h2 ht0
  nlinarith

/-- Every shifted tail is dominated by a geometric series. -/
lemma ricciBetaMajorant_shift_le {B : ℕ} (hB : 4 ≤ B) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 0.413) (k : ℕ) :
    ricciBetaMajorant q (B + k) ≤ ricciBetaMajorant q B * (0.86 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ricciBetaMajorant q (B + (k + 1)) ≤ (0.86 : ℝ) * ricciBetaMajorant q (B + k) :=
        by simpa only [Nat.add_assoc] using
          ricciBetaMajorant_ratio (b := B + k) (by omega) hq0 hq
      _ ≤ (0.86 : ℝ) * (ricciBetaMajorant q B * (0.86 : ℝ) ^ k) := by gcongr
      _ = ricciBetaMajorant q B * (0.86 : ℝ) ^ (k + 1) := by ring

/-- An explicit bound for the entire positive majorant tail. -/
theorem ricciBetaMajorant_tail_le {B : ℕ} (hB : 4 ≤ B) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 0.413) :
    (∑' k : ℕ, ricciBetaMajorant q (B + k)) ≤ ricciBetaMajorant q B / (1 - 0.86) := by
  have hdom : Summable (fun k : ℕ => ricciBetaMajorant q B * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hsum : Summable (fun k : ℕ => ricciBetaMajorant q (B + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold ricciBetaMajorant; positivity)
      (ricciBetaMajorant_shift_le hB hq0 hq)
  calc
    (∑' k : ℕ, ricciBetaMajorant q (B + k)) ≤
        ∑' k : ℕ, ricciBetaMajorant q B * (0.86 : ℝ) ^ k :=
      hsum.tsum_le_tsum (ricciBetaMajorant_shift_le hB hq0 hq) hdom
    _ = ricciBetaMajorant q B / (1 - 0.86) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(0.86 : ℝ)| < 1)]
      ring

example : (∑' k : ℕ, ricciBetaMajorant (0.4 : ℝ) (13 + k)) ≤
    ricciBetaMajorant (0.4 : ℝ) 13 / (1 - 0.86) :=
  ricciBetaMajorant_tail_le (by norm_num) (by norm_num) (by norm_num)

end
end LeanLab.Ricci1937
