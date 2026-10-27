import LeanLab.RieselVaughan1983.Lemma2Statements

/-!
The finite and infinite forms of equation 3.5 on page 50.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Finset ArithmeticFunction

noncomputable section

lemma summatory_convolution (f h : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ q ∈ Icc 1 N, (f * h) q =
      ∑ d ∈ Icc 1 N, f d * ∑ n ∈ Icc 1 (N / d), h n := by
  simp only [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * h b)]
  calc (∑ q ∈ Icc 1 N, ∑ d ∈ q.divisors, f d * h (q / d)) =
        ∑ d ∈ Icc 1 N, ∑ q ∈ (Icc 1 N).filter (fun q => d ∣ q), f d * h (q / d) := by
          apply sum_comm'
          intro q d
          simp only [mem_filter, mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨hq1, hqN⟩, hdq, hq0⟩
            have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdq (by omega)
            have hdN : d ≤ N := (Nat.le_of_dvd (by omega) hdq).trans hqN
            exact ⟨⟨⟨hq1, hqN⟩, hdq⟩, ⟨hd1, hdN⟩⟩
          · rintro ⟨⟨⟨hq1, hqN⟩, hdq⟩, ⟨hd1, hdN⟩⟩
            exact ⟨⟨hq1, hqN⟩, hdq, by omega⟩
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      rw [mul_sum]
      apply sum_nbij' (fun q => q / d) (fun n => d * n)
      · intro q hq
        obtain ⟨hq, hdq⟩ := mem_filter.mp hq
        have hq1 := (mem_Icc.mp hq).1
        have hqN := (mem_Icc.mp hq).2
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0,
          Nat.div_le_div_right hqN⟩
      · intro n hn
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hmul : n * d ≤ N := (Nat.le_div_iff_mul_le hd0).mp hnN
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩, dvd_mul_right d n⟩
      · intro q hq
        exact Nat.mul_div_cancel' (mem_filter.mp hq).2
      · intro n _
        exact Nat.mul_div_right n hd0
      · intro q _
        rfl

/-- The divisor sum in equation 3.1, with its natural cutoff. -/
def divisorPartial (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) / n

lemma eq35_finite (y : ℝ) :
    S y = ∑ m ∈ Icc 1 ⌊y⌋₊, g m * divisorPartial (y / m) := by
  unfold S
  rw [← g_convolution, summatory_convolution]
  apply sum_congr rfl
  intro m _
  simp only [divisorPartial, Nat.floor_div_natCast, divisorCoeff_apply]

/-- Equation 3.5 without using uniqueness of Dirichlet series. -/
theorem eq35 (y : ℝ) (hy : 1 ≤ y) :
    S y = ∑' m : ℕ, g m * divisorPartial (y / m) := by
  rw [eq35_finite]
  symm
  apply tsum_eq_sum
  intro m hm
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  · have hmN : ⌊y⌋₊ < m := by
      have : ¬ (1 ≤ m ∧ m ≤ ⌊y⌋₊) := by simpa only [mem_Icc] using hm
      omega
    have hym : y < (m : ℝ) := by
      have h := Nat.lt_floor_add_one y
      have hmN' : (⌊y⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hmN
      linarith
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    have hfl : ⌊y / m⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hm0').mpr hym)
    simp [divisorPartial, hfl]

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.summatory_convolution
#print axioms LeanLab.RieselVaughan1983.Lemma2.eq35_finite
#print axioms LeanLab.RieselVaughan1983.Lemma2.eq35
