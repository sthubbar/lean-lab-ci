/-
An elementary logarithmic consequence of the proved Granville and Ramare input.
Source: P0013 page 7 equations 2.7 and 2.10 and page 23 equation 3.40.
The bound here is log N. It is not the stronger cited 1.00303 q over phi q input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Mobius325
import LeanLab.HelfgottArcs.TypeIPartial325

namespace LeanLab.HelfgottArcs.Mobius325
open Finset

/-- For a decreasing weight with nonnegative final value, endpoint plus variation is its initial value.
Source: P0013 page 23, derived finite Abel input. -/
theorem antitone_variation325 (w : ℕ → ℝ) (N : ℕ) (hw : 0 ≤ w (N - 1))
    (hanti : ∀ i < N - 1, w (i + 1) ≤ w i) :
    |w (N - 1)| + ∑ i ∈ range (N - 1), |w (i + 1) - w i| = w 0 := by
  rw [abs_of_nonneg hw]
  have hh : ∑ i ∈ range (N - 1), |w (i + 1) - w i| = w 0 - w (N - 1) := by
    calc
      _ = ∑ i ∈ range (N - 1), (w i - w (i + 1)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti i (mem_range.mp hi)))]
        ring
      _ = _ := sum_range_sub' w (N - 1)
  rw [hh]
  ring

/-- A decreasing nonnegative weight costs only its initial value in Abel summation.
Source: P0013 page 23, derived finite Abel input. -/
theorem antitone_weighted_bound325 (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ B)
    (hw : 0 ≤ w (N - 1)) (hanti : ∀ i < N - 1, w (i + 1) ≤ w i) :
    ‖∑ i ∈ range N, w i • z i‖ ≤ B * w 0 := by
  have hh := Decomp119.partial_summation_bound325 w z N B hz
  rwa [antitone_variation325 w N hw hanti] at hh

/-- The Granville and Ramare input alone gives a logarithmic envelope for the log weighted sum.
Source: P0013 page 7 equation 2.7 and page 23 equation 3.40, a derived weaker bound. -/
theorem coprime_mobius_log_weight_bound325 (q N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, coprimeMu q n / n * Real.log ((N : ℝ) / n)| ≤ Real.log N := by
  let w : ℕ → ℝ := fun i => Real.log ((N : ℝ) / ((i + 1 : ℕ) : ℝ))
  let z : ℕ → ℂ := fun i => ((coprimeMu q (i + 1) / ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ)
  have hs (f : ℕ → ℝ) (k : ℕ) :
      ∑ n ∈ Icc 1 k, f n = ∑ i ∈ range k, f (i + 1) := by
    simpa [Ico_add_one_right_eq_Icc, Nat.add_comm] using sum_Ico_eq_sum_range f 1 (k + 1)
  have hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ (1 : ℝ) := by
    intro k hk
    change ‖∑ i ∈ range k, ((coprimeMu q (i + 1) / ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ ≤ 1
    have heq := congrArg (fun r : ℝ => (r : ℂ)) (hs (fun n => coprimeMu q n / (n : ℝ)) k)
    simp only [Complex.ofReal_sum] at heq
    rw [← heq, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact coprime_mobius_reciprocal_bound q k
  have hw : 0 ≤ w (N - 1) := by
    change 0 ≤ Real.log ((N : ℝ) / ((N - 1 + 1 : ℕ) : ℝ))
    rw [Nat.sub_add_cancel hN, div_self (by exact_mod_cast (by omega : N ≠ 0))]
    norm_num
  have hanti : ∀ i < N - 1, w (i + 1) ≤ w i := by
    intro i hi
    dsimp [w]
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    exact_mod_cast (by omega : i + 1 ≤ i + 1 + 1)
  have hb := antitone_weighted_bound325 w z N 1 hz hw hanti
  have heq : ∑ i ∈ range N, w i • z i =
      ((∑ n ∈ Icc 1 N, coprimeMu q n / n * Real.log ((N : ℝ) / n) : ℝ) : ℂ) := by
    simp only [w, z, Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    rw [hs]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs] at hb
  simpa [w] using hb

/-- The elementary logarithmic envelope does not reach the cited uniform budget even at q equal to one.
Source: P0013 page 7 equation 2.10, a comparison of upper bounds only. -/
theorem log_envelope_exceeds_cited_budget325 :
    1.00303 * (1 : ℝ) / (Nat.totient 1 : ℝ) < Real.log 4 := by
  norm_num
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  have hh := Real.log_two_gt_d9
  norm_num at *
  linarith

/-- The Granville and Ramare bound also holds with odd support.
Source: P0013 page 23 equation 3.40, with modulus twice q in equation 2.7. -/
theorem odd_coprime_mobius_bound325 (x : ℝ) (q : ℕ) :
    |∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => Odd n ∧ n.Coprime q),
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) / n| ≤ 1 := by
  simpa only [Nat.coprime_mul_iff_right, Nat.coprime_two_right] using
    granville_ramare_10_2 x (2 * q)

/-- The elementary log envelope also respects the odd and coprime restrictions.
Source: P0013 page 23 equation 3.40, a derived weaker bound from equation 2.7. -/
theorem odd_coprime_mobius_log_bound325 (q N : ℕ) (hN : 1 ≤ N) :
    |∑ n ∈ (Icc 1 N).filter (fun n => Odd n ∧ n.Coprime q),
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) / n * Real.log ((N : ℝ) / n)| ≤
        Real.log N := by
  simpa only [sum_filter, coprimeMu, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, Nat.coprime_mul_iff_right, Nat.coprime_two_right,
    ite_div, zero_div, ite_mul, zero_mul] using
      coprime_mobius_log_weight_bound325 (2 * q) N hN

example := antitone_variation325 (fun _ => (1 : ℝ)) 8 (by norm_num) (by intros; norm_num)
example := antitone_weighted_bound325 (fun _ => (1 : ℝ)) (fun _ => (1 : ℂ)) 8 8
  (by intro k hk; simpa using (show (k : ℝ) ≤ 8 by exact_mod_cast hk))
  (by norm_num) (by intros; norm_num)
example := coprime_mobius_log_weight_bound325 6 10 (by norm_num)
example := log_envelope_exceeds_cited_budget325
example := odd_coprime_mobius_bound325 10 3
example := odd_coprime_mobius_log_bound325 3 10 (by norm_num)

end LeanLab.HelfgottArcs.Mobius325
