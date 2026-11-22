/-
A diagnostic for the rough weight in P0088 page 11 Lemma 3.4.
Coefficientwise bounds do not preserve cancellation in a complex sum.
This is a failed proof route, not a refutation of the paper estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a

namespace LeanLab.KumchevLiu2007.Task674
open Complex Task556a

/-- Page 4 display 10, diagnostic for page 11 Lemma 3.4: the rough
filter at cutoff three can increase the norm of a complex sum. -/
theorem rough_filter_increases_norm :
    ‖roughWeight 3 6 * (1 : ℂ) + roughWeight 3 7 * (-1 : ℂ)‖ >
      ‖(1 : ℂ) + (-1 : ℂ)‖ := by
  have h6 : roughWeight 3 6 = 0 :=
    roughWeight_eq_zero_of_small_prime Nat.prime_two (by norm_num) (by norm_num)
  have h7 : roughWeight 3 7 = 1 := by
    unfold roughWeight
    apply if_pos
    intro p hp hd
    have he : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp hd
    subst p
    norm_num
  rw [h6, h7]
  norm_num

end LeanLab.KumchevLiu2007.Task674

#print axioms LeanLab.KumchevLiu2007.Task674.rough_filter_increases_norm
