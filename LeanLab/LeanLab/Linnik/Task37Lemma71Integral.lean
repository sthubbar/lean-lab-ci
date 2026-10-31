/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 21, display 63 and Lemma 7.1.
Connect the finite reflection inequality to the joint Fourier integral.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37Lemma71

namespace LeanLab.Linnik.Task37Lemma71Integral
open Set Real Finset MeasureTheory
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1434Lemma21
open LeanLab.Linnik.Task37Lemma71
open LeanLab.Linnik.LiLiuLemma43 (SA)

noncomputable def F2G (c : ℝ) (L : ℕ) (α : ℝ) : ℂ :=
  Gs L α ^ 2 - c * L * Gs L α

noncomputable def Joint (a b c τ : ℝ) (N1 N L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * (∫ α in Icc (0 : ℝ) 1, ‖Sm N1 N α * F2G c L α‖ ^ 2) +
    τ ^ 2 * (∫ α in Icc (0 : ℝ) 1, ‖Sm N1 N α * FG a b L α‖ ^ 2)

lemma SF2_sum (c : ℝ) (N1 N L R : ℕ) (hR : N + 3 * 2 ^ L < R) (α : ℝ) :
    Sm N1 N α * F2G c L α = SA (range R) (fun n => (f2 c N1 N L n : ℂ)) α := by
  have he : Sm N1 N α * F2G c L α = Sm N1 N α * Gs L α ^ 2 -
      c * L * (Sm N1 N α * Gs L α ^ 1) := by unfold F2G; ring
  rw [he, SG_pow 2 N1 N L R (by omega), SG_pow 1 N1 N L R (by omega)]
  unfold SA f2
  push_cast
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

lemma integral_F2 (c : ℝ) (N1 N L R : ℕ) (hR : N + 3 * 2 ^ L < R) :
    (∫ α in Icc (0 : ℝ) 1, ‖Sm N1 N α * F2G c L α‖ ^ 2) =
      ∑ n ∈ range R, f2 c N1 N L n ^ 2 := by
  simp_rw [SF2_sum c N1 N L R hR]
  exact parseval _ _

lemma integral_F3 (a b : ℝ) (N1 N L R : ℕ) (hL : 1 ≤ L) (hR : N + 3 * 2 ^ L < R) :
    (∫ α in Icc (0 : ℝ) 1, ‖Sm N1 N α * FG a b L α‖ ^ 2) =
      ∑ n ∈ range R, ff a b N1 N L n ^ 2 := by
  simp_rw [SFG_sum a b N1 N L R hL hR]
  exact parseval _ _

/-- Display 63 is exactly the joint finite coefficient second moment. -/
theorem joint_parseval (a b c τ : ℝ) (N1 N L R : ℕ) (hL : 1 ≤ L)
    (hR : N + 3 * 2 ^ L < R) :
    Joint a b c τ N1 N L =
      (L : ℝ) ^ 2 * ∑ n ∈ range R, f2 c N1 N L n ^ 2 +
        τ ^ 2 * ∑ n ∈ range R, ff a b N1 N L n ^ 2 := by
  unfold Joint
  rw [integral_F2 c N1 N L R hR, integral_F3 a b N1 N L R hL hR]

/-- The finite integral inequality in the proof of display 64. -/
theorem lemma71_integral_finite {a b c τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hτ : 0 < τ) (N1 N L : ℕ) (hN : Even N) (hN0 : 0 < N) (hL : 0 < L) :
    let g := fun n => max (f2 c N1 N L n) 0
    let h := fun n => max (ff a b N1 N L n) 0
    ((2 / N) * ((L : ℝ) * ∑ n ∈ UN N, g n + τ * ∑ n ∈ UN N, h n) ^ 2 -
      Joint a b c τ N1 N L) / (2 * τ * L) ≤ r5pp N1 N L := by
  intro g h
  let R := N + 3 * 2 ^ L + 1
  have hR : N + 3 * 2 ^ L < R := by omega
  have hU : UN N ⊆ range R := by
    intro n hn
    simp only [UN, mem_filter, Finset.mem_range] at hn ⊢
    omega
  have h2 := sum_le_sum_of_subset_of_nonneg hU (fun n _ _ => sq_nonneg (f2 c N1 N L n))
  have h3 := sum_le_sum_of_subset_of_nonneg hU (fun n _ _ => sq_nonneg (ff a b N1 N L n))
  have h2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg (L : ℝ))
  have h3' := mul_le_mul_of_nonneg_left h3 (sq_nonneg τ)
  apply le_trans ?_ (lemma71_finite ha hb hc hτ N1 N L hN hN0 hL)
  apply div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ 2 * τ * L)
  rw [joint_parseval a b c τ N1 N L R hL hR]
  linarith

/-- Concrete admissible parameters for the integral inequality. -/
theorem integral_instance :
    let g := fun n => max (f2 0 0 8 1 n) 0
    let h := fun n => max (ff 0 0 0 8 1 n) 0
    ((2 / (8 : ℝ)) * (1 * ∑ n ∈ UN 8, g n + 1 * ∑ n ∈ UN 8, h n) ^ 2 -
      Joint 0 0 0 1 0 8 1) / (2 * 1 * 1) ≤ r5pp 0 8 1 := by
  simpa only [Nat.cast_one, Nat.cast_ofNat] using
    (lemma71_integral_finite (a := 0) (b := 0) (c := 0) (τ := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      0 8 1 (by decide) (by norm_num) (by norm_num))

end LeanLab.Linnik.Task37Lemma71Integral

#print axioms LeanLab.Linnik.Task37Lemma71Integral.SF2_sum
#print axioms LeanLab.Linnik.Task37Lemma71Integral.integral_F2
#print axioms LeanLab.Linnik.Task37Lemma71Integral.integral_F3
#print axioms LeanLab.Linnik.Task37Lemma71Integral.joint_parseval
#print axioms LeanLab.Linnik.Task37Lemma71Integral.lemma71_integral_finite
#print axioms LeanLab.Linnik.Task37Lemma71Integral.integral_instance
