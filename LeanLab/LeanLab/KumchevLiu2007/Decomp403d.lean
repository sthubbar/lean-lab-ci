/-
A concrete limit of transferring the A2 majorant to A3.
Source page 13 display 45 and page 14 display 47.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403c

namespace LeanLab.KumchevLiu2007.Task403d

open Real Complex U1534 Task129c Task292a
open scoped BigOperators

/-- Page 2 display 8. The triangle inequality bounds the reduced Gauss sum by the totient. -/
theorem gaussS_norm_le_totient (q a : ℕ) :
    ‖gaussS q a‖ ≤ (Nat.totient q : ℝ) := by
  have hee (t : ℝ) : ‖ee t‖ = 1 := by simp [ee, Complex.norm_exp]
  unfold gaussS
  calc
    _ ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro x hx
      exact (hee _).le
    _ = _ := by simp [Nat.totient_eq_card_coprime, Nat.coprime_comm]

/-- Page 13 display 45. Applying the triangle inequality gives a coarse bound by the totient. -/
theorem A3_norm_le_totient (n q : ℕ) : ‖A3 n q‖ ≤ (Nat.totient q : ℝ) := by
  by_cases hq : q = 0
  · subst q
    simp [A3]
  have hphi : 0 < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  have hee (t : ℝ) : ‖ee t‖ = 1 := by simp [ee, Complex.norm_exp]
  have hb : ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      gaussS q a ^ 3 * ee (-((a * n : ℕ) : ℝ) / q)‖ ≤ (Nat.totient q : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (Nat.totient q : ℝ) ^ 3 := by
        apply norm_sum_le_of_le
        intro a ha
        rw [norm_mul, norm_pow, hee, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (gaussS_norm_le_totient q a) 3
      _ = _ := by
        simp [Nat.totient_eq_card_coprime, Nat.coprime_comm]
        ring
  unfold A3
  rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Page 13 display 45. The admissible integer 507 has A3 at modulus 13
 equal to minus five eighteenths. This tests a proposed transfer of the lab A2 bound. -/
theorem A3_507_13 : InH3 507 ∧ A3 507 13 = -(5 / 18 : ℂ) := by
  constructor
  · norm_num [InH3]
  · letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have hc : (tripleRoots 13 507).card = 96 := by decide
    rw [A3_prime_count, hc]
    norm_num

/-- Page 14 display 47, a limitation of one lab majorant.
The exact A2 majorant with constant one fails for A3 even on H3. -/
theorem A2_majorant_not_valid_for_A3 :
    ¬ ∀ n q : ℕ, InH3 n → 0 < q → ‖A3 n q‖ ≤ localMajorant q / (q : ℝ) := by
  intro h
  have hb := h 507 13 A3_507_13.1 (by norm_num)
  have hm : localMajorant 13 = 19 / 13 := by
    norm_num [localMajorant, (show Nat.Prime 13 by norm_num).primeFactors]
  rw [A3_507_13.2, hm] at hb
  norm_num [norm_div] at hb

end LeanLab.KumchevLiu2007.Task403d
