import LeanLab.RieselVaughan1983.Lemma2PrimeSums

/-! Exact local moment algebra for the displays on page 51.
AI wrote the Lean code. Binary Goldbach is OPEN.
This module does not differentiate the infinite Euler product. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real
noncomputable section

def localFirst (p : ℕ) : ℝ :=
  -(g p + 2 * g (p ^ 2) + 3 * g (p ^ 3)) / localG p * Real.log p

def localSecond (p : ℕ) : ℝ :=
  ((g p + 4 * g (p ^ 2) + 9 * g (p ^ 3)) / localG p -
    ((g p + 2 * g (p ^ 2) + 3 * g (p ^ 3)) / localG p) ^ 2) * Real.log p ^ 2

lemma localG_odd_eq (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    localG p = ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (p : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt h2))
  rw [localG, g_odd_prime p hp h2, g_odd_prime_sq p hp h2, g_odd_prime_cube p hp h2]
  field_simp
  <;> ring

lemma localG_pos (p : ℕ) (hp : p.Prime) : 0 < localG p := by
  by_cases h2 : p = 2
  · subst p; rw [localG_two]; norm_num
  · have hgt : 2 < p := by have := hp.two_le; omega
    rw [localG_odd_eq p hp hgt]
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hgt
    apply div_pos
    · exact sq_pos_of_pos (by linarith)
    · positivity

lemma localFirst_two : localFirst 2 = 3 / 2 * Real.log 2 := by
  norm_num [localFirst, localG_two, g_two, g_four, g_eight]
  <;> ring

lemma localSecond_two : localSecond 2 = -(15 / 4) * Real.log 2 ^ 2 := by
  norm_num [localSecond, localG_two, g_two, g_four, g_eight]
  <;> ring

lemma localFirst_odd (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    localFirst p = 2 * Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (p : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt h2))
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hp.one_lt))
  rw [localFirst, localG_odd_eq p hp h2, g_odd_prime p hp h2,
    g_odd_prime_sq p hp h2, g_odd_prime_cube p hp h2]
  field_simp
  <;> ring

lemma localSecond_odd (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    localSecond p = -(8 * (p : ℝ) ^ 2 - 10 * p + 4) /
      ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) * Real.log p ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (p : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt h2))
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hp.one_lt))
  rw [localSecond, localG_odd_eq p hp h2, g_odd_prime p hp h2,
    g_odd_prime_sq p hp h2, g_odd_prime_cube p hp h2]
  field_simp
  <;> ring

lemma localFirst_prime_indicator (n : ℕ) :
    (if n.Prime then localFirst n else 0) =
      2 * a0Term n + if n = 2 then Real.log 2 / 2 else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]
    by_cases h2 : n = 2
    · subst n; simp [a0Term, localFirst_two, Nat.prime_two]; ring
    · rw [localFirst_odd n hp (by have := hp.two_le; omega)]
      simp [a0Term, hp, h2]
      ring
  · have h2 : n ≠ 2 := by intro h; subst n; exact hp Nat.prime_two
    simp [hp, h2, a0Term]

lemma localSecond_prime_indicator (n : ℕ) :
    (if n.Prime then localSecond n else 0) =
      -a2Term n + if n = 2 then Real.log 2 ^ 2 / 4 else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]
    by_cases h2 : n = 2
    · subst n; simp [a2Term, localSecond_two, Nat.prime_two]; ring
    · rw [localSecond_odd n hp (by have := hp.two_le; omega)]
      simp only [a2Term, if_pos hp, if_neg h2, add_zero]
      ring
  · have h2 : n ≠ 2 := by intro h; subst n; exact hp Nat.prime_two
    simp [hp, h2, a2Term]

lemma localFirst_hasSum :
    HasSum (fun n : ℕ => if n.Prime then localFirst n else 0) A1 := by
  have h := (A0_hasSum.mul_left 2).add (hasSum_ite_eq (2 : ℕ) (Real.log 2 / 2))
  have he := funext localFirst_prime_indicator
  rw [he]
  simpa only [A1, add_comm] using h

lemma localSecond_hasSum :
    HasSum (fun n : ℕ => if n.Prime then localSecond n else 0)
      (Real.log 2 ^ 2 / 4 - A2) := by
  have h := A2_hasSum.neg.add (hasSum_ite_eq (2 : ℕ) (Real.log 2 ^ 2 / 4))
  have he := funext localSecond_prime_indicator
  rw [he]
  simpa only [sub_eq_add_neg, add_comm] using h

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.localG_odd_eq
#print axioms LeanLab.RieselVaughan1983.Lemma2.localG_pos
#print axioms LeanLab.RieselVaughan1983.Lemma2.localFirst_two
#print axioms LeanLab.RieselVaughan1983.Lemma2.localSecond_two
#print axioms LeanLab.RieselVaughan1983.Lemma2.localFirst_odd
#print axioms LeanLab.RieselVaughan1983.Lemma2.localSecond_odd
#print axioms LeanLab.RieselVaughan1983.Lemma2.localFirst_prime_indicator
#print axioms LeanLab.RieselVaughan1983.Lemma2.localSecond_prime_indicator
#print axioms LeanLab.RieselVaughan1983.Lemma2.localFirst_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.localSecond_hasSum
