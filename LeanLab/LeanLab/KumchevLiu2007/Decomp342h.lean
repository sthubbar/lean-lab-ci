/-
Reality of the three-square coefficient on page 13 display 45.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342g
import LeanLab.KumchevLiu2007.Singular129

namespace LeanLab.KumchevLiu2007.Task342h

open Real Complex U1534 Task129c
open scoped BigOperators

/-- Page 2 display 8 and page 13 display 45. The quadratic Gauss sum as a unit character sum. -/
theorem gaussS_zmod (q a : ℕ) [NeZero q] :
    gaussS q a = ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) ((a : ZMod q) * x * x) := by
  classical
  rw [gaussS, Task342a.reduced_sum_zmod]
  apply Finset.sum_congr rfl
  intro x hx
  have he := ee_int_bridge q ((a : ℤ) * (x.val : ℤ) ^ 2)
  convert he using 1 <;> push_cast
  · rfl
  · rw [ZMod.natCast_zmod_val]
    ring

/-- Page 13 display 45. The three-square coefficient in unit character notation. -/
theorem A3_zmod_formula (n q : ℕ) [NeZero q] :
    A3 n q = 1 / (Nat.totient q : ℂ) ^ 3 *
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ZMod.stdAddChar (N := q) (a * x * x)) ^ 3 *
            ZMod.stdAddChar (N := q) (-(a * (n : ZMod q))) := by
  classical
  rw [A3, Task342a.reduced_sum_zmod]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [gaussS_zmod, ZMod.natCast_zmod_val]
  congr 1
  have he := ee_int_bridge q (-((a.val : ℤ) * (n : ℤ)))
  convert he using 1 <;> push_cast
  · ring
  · rw [ZMod.natCast_zmod_val]

/-- Page 13 display 45. Residue negation makes the three-square coefficient real too. -/
theorem A3_conj (n q : ℕ) :
    (starRingEnd ℂ) (A3 n q) = A3 n q := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [A3]
  letI : NeZero q := ⟨hq⟩
  rw [A3_zmod_formula, map_mul, map_div₀, map_one, map_pow, map_natCast, map_sum]
  congr 1
  have hstar (z : ZMod q) : (starRingEnd ℂ) (ZMod.stdAddChar (N := q) z) =
      ZMod.stdAddChar (N := q) (-z) := by
    rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q),
      AddChar.inv_apply]
  simp_rw [map_mul, map_pow, map_sum, hstar]
  refine Finset.sum_bij (fun (a : ZMod q) _ => -a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha b hb hab
    exact neg_injective hab
  · intro a ha
    refine ⟨-a, ?_, neg_neg a⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.neg
  · intro a ha
    simp only [neg_mul, neg_neg]

end LeanLab.KumchevLiu2007.Task342h
