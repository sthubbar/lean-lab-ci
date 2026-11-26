/-
Kumchev and Liu 2007, P0088, page 11 Case 1 and page 15 display 52.
The small divisor block has an elementary bound at the upper window edge.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.RoughEdge687
import LeanLab.KumchevLiu2007.Split1122KLLemma34M1

namespace LeanLab.KumchevLiu2007.Task687

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open Split1122KLLemma34M1
open scoped BigOperators

/-- P0088 page 15 display 52: a bounded coefficient gives a short square sum
bounded by its term count times that bound. -/
theorem bounded_short_sum_sq_le (S : Finset ℕ) (c : ℕ → ℂ) (Y t H K : ℝ)
    (hY : 0 < Y) (ht : Y / 4 ≤ t) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hc : ∀ m ∈ S, ‖c m‖ ≤ K) :
    ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
      c m‖ ^ 2 ≤ ((H / Real.sqrt Y + 1) * K) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    _ ≤ ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        ‖c m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        K := Finset.sum_le_sum (fun m hm => hc m (Finset.mem_filter.mp hm).1)
    _ = ((S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card : ℝ) * K := by
      simp [nsmul_eq_mul]
    _ ≤ (H / Real.sqrt Y + 1) * K :=
      mul_le_mul_of_nonneg_right (card_short_squares_le S Y t H hY ht hH) hK

/-- P0088 page 11 Case 1 at the upper window edge: coefficients bounded by
six times P cost at most 288 H squared divided by L to A when H P to four
is at most Y and A is at most twice B. -/
theorem small_block_edge_integral_le (S : Finset ℕ) (c : ℕ → ℂ)
    (Y H L A B : ℝ) (hY : 0 < Y) (hsY : Real.sqrt Y ≤ H)
    (hH4 : H ≤ Y / 4) (hHP : H * (L ^ B) ^ 4 ≤ Y)
    (hL : 1 ≤ L) (hAB : A ≤ 2 * B)
    (hc : ∀ m ∈ S, ‖c m‖ ≤ 6 * L ^ B) :
    (∫ t in Y - 2 * H..Y,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        c m‖ ^ 2) ≤ 288 * H ^ 2 / L ^ A := by
  have hH : 0 ≤ H := (Real.sqrt_nonneg Y).trans hsY
  have hP : 0 < L ^ B := Real.rpow_pos_of_pos (by linarith) B
  have ht := tail_arith H Y L (A + 2 * B) B hY hsY hHP hL (by linarith)
  have hint := short_sum_sq_intervalIntegrable S c H (Y - 2 * H) Y
  calc
    _ ≤ (Y - (Y - 2 * H)) * ((H / Real.sqrt Y + 1) * (6 * L ^ B)) ^ 2 := by
      have hb := intervalIntegral.integral_mono_on (show Y - 2 * H ≤ Y by linarith)
        hint intervalIntegrable_const (fun t ht =>
          bounded_short_sum_sq_le S c Y t H (6 * L ^ B) hY (by linarith [ht.1])
            hH (by positivity) hc)
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hb
    _ = (6 * L ^ B) ^ 2 * ((Y - (Y - 2 * H)) * (H / Real.sqrt Y + 1) ^ 2) := by ring
    _ ≤ (6 * L ^ B) ^ 2 * (8 * H ^ 2 / L ^ (A + 2 * B)) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = 288 * H ^ 2 / L ^ A := by
      rw [Real.rpow_add (by linarith : 0 < L), mul_comm 2 B,
        Real.rpow_mul (by linarith : 0 ≤ L), Real.rpow_two]
      field_simp
      ring

/-- P0088 page 15 display 52: the original rough cofactor coefficient
has modulus at most two on any prime divisor block below the cube cutoff. -/
theorem rough_prime_coefficient_norm_le_two (S : Finset ℕ) (n : ℕ) (z : ℝ)
    (hn : 0 < n) (hz : 0 ≤ z) (hsize : (n : ℝ) < z ^ 3)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n ∧ z ≤ (p : ℝ)) :
    ‖∑ p ∈ S, roughWeight z (n / p)‖ ≤ 2 := by
  have hc := prime_divisor_card_le_two S n z hn hz hsize hS
  calc
    _ ≤ ∑ p ∈ S, ‖roughWeight z (n / p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun p _ => roughWeight_norm_le_one z (n / p))
    _ = (S.card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hc

/-- P0088 page 15 display 52: the upper edge of the original prime block
requires no Type II estimate because its rough cofactor coefficient is bounded. -/
theorem rough_prime_block_edge (S : ℕ → Finset ℕ) (Y H z L A B α : ℝ)
    (hY : 1 ≤ Y) (hz : 0 ≤ z) (hroot : Real.sqrt Y ≤ z ^ 3)
    (hsY : Real.sqrt Y ≤ H) (hH4 : H ≤ Y / 4)
    (hHP : H * (L ^ B) ^ 4 ≤ Y) (hL : 1 ≤ L) (hB : 0 ≤ B) (hAB : A ≤ 2 * B)
    (hS : ∀ n ∈ squareWindow Y, ∀ p ∈ S n, p.Prime ∧ p ∣ n ∧ z ≤ (p : ℝ)) :
    (∫ t in Y - 2 * H..Y,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ S m, roughWeight z (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      288 * H ^ 2 / L ^ A := by
  have hY0 : 0 < Y := by linarith
  apply small_block_edge_integral_le _ _ Y H L A B hY0 hsY hH4 hHP hL hAB
  intro n hn
  rw [norm_mul, show ‖fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 from
    Circle.norm_coe _, mul_one]
  have hnwin := (Finset.mem_filter.mp hn).2
  have hn0 : 0 < n := by
    have hsq := Real.sqrt_pos.mpr hY0
    have : (0 : ℝ) < n := by linarith [hnwin.1]
    exact_mod_cast this
  have hcoeff := rough_prime_coefficient_norm_le_two (S n) n z hn0 hz
    (hnwin.2.trans_le hroot) (hS n hn)
  have hP : 1 ≤ L ^ B := Real.one_le_rpow hL hB
  linarith

end LeanLab.KumchevLiu2007.Task687

#print axioms LeanLab.KumchevLiu2007.Task687.bounded_short_sum_sq_le
#print axioms LeanLab.KumchevLiu2007.Task687.small_block_edge_integral_le

#print axioms LeanLab.KumchevLiu2007.Task687.rough_prime_coefficient_norm_le_two
#print axioms LeanLab.KumchevLiu2007.Task687.rough_prime_block_edge
