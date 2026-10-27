import LeanLab.LiuWang2002.Reduction

/-! Positivity and a nonvacuity instance for display 3.9, page 145.
AI wrote the Lean code. Binary Goldbach is open. -/

namespace LeanLab.LiuWang2002.Counting109
open Real Reduction

/-- The weighted prime representation count of display 3.9 is nonnegative. -/
theorem Icount_nonneg (N : ℕ) : 0 ≤ Icount N := by
  unfold Icount
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  split_ifs <;> positivity

/-- Every admissible triple contributes a positive weight to display 3.9. -/
theorem Icount_pos_of_admissible (N a b : ℕ) (hab : Admissible N a b) : 0 < Icount N := by
  classical
  have hsum := hab.1
  have haRange : a ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hbRange : b ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hla : 0 < log (a : ℝ) := log_pos (by exact_mod_cast hab.2.1.one_lt)
  have hlb : 0 < log (b : ℝ) := log_pos (by exact_mod_cast hab.2.2.1.one_lt)
  have hlc : 0 < log ((N - a - b : ℕ) : ℝ) := log_pos (by exact_mod_cast hab.2.2.2.1.one_lt)
  have hw : 0 < log a * log b * log ((N - a - b : ℕ) : ℝ) := mul_pos (mul_pos hla hlb) hlc
  have hin := Finset.single_le_sum (s := Finset.range (N + 1))
    (f := fun j => if Admissible N a j then log a * log j * log ((N - a - j : ℕ) : ℝ) else 0)
    (fun j hj => by split_ifs <;> positivity) hbRange
  rw [if_pos hab] at hin
  have hout := Finset.single_le_sum (s := Finset.range (N + 1))
    (f := fun i => ∑ j ∈ Finset.range (N + 1),
      if Admissible N i j then log i * log j * log ((N - i - j : ℕ) : ℝ) else 0)
    (fun i hi => Finset.sum_nonneg (fun j hj => by split_ifs <;> positivity)) haRange
  exact hw.trans_le (hin.trans hout)

/-- Positivity of display 3.9 is exactly the existence of an admissible triple. -/
theorem Icount_pos_iff (N : ℕ) : 0 < Icount N ↔ ∃ a b : ℕ, Admissible N a b := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    unfold Icount at h
    simp [hno] at h
  · rintro ⟨a, b, hab⟩
    exact Icount_pos_of_admissible N a b hab

/-- A formal nonvacuity instance for display 3.9 is 9 equal to 3 plus 3 plus 3. -/
theorem Icount_nine_pos : 0 < Icount 9 := by
  apply Icount_pos_of_admissible 9 3 3
  norm_num [Admissible]

/-- Above 2000, all primes in an admissible triple are odd, displays 3.9 and Theorem 1. -/
theorem admissible_odd (N a b : ℕ) (hN : (2000 : ℝ) < N) (hab : Admissible N a b) :
    Odd a ∧ Odd b ∧ Odd (N - a - b) := by
  have ho : ∀ p : ℕ, p.Prime → (0.001 : ℝ) * N ≤ p → Odd p := by
    intro p hp hl
    apply hp.odd_of_ne_two
    intro he
    rw [he] at hl
    norm_num at hl
    linarith
  exact ⟨ho a hab.2.1 hab.2.2.2.2.1,
    ho b hab.2.2.1 hab.2.2.2.2.2.1,
    ho (N - a - b) hab.2.2.2.1 hab.2.2.2.2.2.2⟩

/-- Positive weighted count gives the three odd primes of Theorem 1, pages 134 and 174. -/
theorem odd_three_primes_of_Icount_pos (N : ℕ) (hN : exp 3100 ≤ (N : ℝ)) (hI : 0 < Icount N) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ Odd p ∧ Odd q ∧ Odd r ∧ p + q + r = N := by
  obtain ⟨a, b, hab⟩ := (Icount_pos_iff N).mp hI
  have hlarge : (2000 : ℝ) < N := by linarith [Real.add_one_le_exp (3100 : ℝ)]
  obtain ⟨ha, hb, hc⟩ := admissible_odd N a b hlarge hab
  refine ⟨a, b, N - a - b, hab.2.1, hab.2.2.1, hab.2.2.2.1, ha, hb, hc, ?_⟩
  have hh := hab.1
  omega

end LeanLab.LiuWang2002.Counting109

#print axioms LeanLab.LiuWang2002.Counting109.Icount_nonneg
#print axioms LeanLab.LiuWang2002.Counting109.Icount_pos_of_admissible
#print axioms LeanLab.LiuWang2002.Counting109.Icount_pos_iff
#print axioms LeanLab.LiuWang2002.Counting109.Icount_nine_pos

#print axioms LeanLab.LiuWang2002.Counting109.admissible_odd
#print axioms LeanLab.LiuWang2002.Counting109.odd_three_primes_of_Icount_pos
