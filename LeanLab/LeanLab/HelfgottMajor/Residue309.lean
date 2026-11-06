import LeanLab.HelfgottMajor.Decomp269a
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Local coefficient audit for P0014 pages 33 and 34, displays 4.6 and 4.7.
The numerator derivative is the simple pole coefficient after division by s squared.
No assertion about the Laurent expansion of a Dirichlet L function is assumed here.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Residue309
open Real

/-- The coefficient change from the scaling factor in display 4.7 on page 33.
The two differentiable factors represent the regularized simple pole factors.
-/
theorem scaled_numerator_derivative (F G : ℂ → ℂ) (a b c d : ℂ)
    (hF : HasDerivAt F a 0) (hG : HasDerivAt G b 0)
    (hF0 : F 0 = c) (hG0 : G 0 = d) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s : ℂ => F s * G s * (x : ℂ) ^ s)
      (a * d + c * b + c * d * (log x : ℂ)) 0 := by
  have hxp := (Complex.hasStrictDerivAt_const_cpow
    (x := (x : ℂ)) (y := (0 : ℂ)) (Or.inl (by exact_mod_cast hx.ne'))).hasDerivAt
  convert (hF.mul hG).mul hxp using 1 <;>
    simp [hF0, hG0, Complex.ofReal_log hx.le] <;> ring

/-- An even nontrivial character has leading coefficient one in the displayed model.
Pages 33 and 34 then require a log x contribution to the scaled numerator derivative.
This is a local model audit and proves no L function expansion.
-/
theorem even_model_derivative (b c : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (fun s : ℂ => (1 + b * s) * (1 + c * s) * (x : ℂ) ^ s) 0 =
      b + c + (log x : ℂ) := by
  have hb : HasDerivAt (fun s : ℂ => 1 + b * s) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).const_add 1
  have hc : HasDerivAt (fun s : ℂ => 1 + c * s) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul c).const_add 1
  simpa using (scaled_numerator_derivative _ _ b c 1 1 hb hc (by simp) (by simp) x hx).deriv

/-- At x equal to exp 1 the simple pole coefficient in the local model differs by one.
This is the concrete source audit instance for display 4.7, page 33.
-/
theorem even_model_witness (b c : ℂ) :
    deriv (fun s : ℂ => (1 + b * s) * (1 + c * s) * (exp 1 : ℂ) ^ s) 0 ≠ b + c := by
  rw [even_model_derivative b c (exp 1) (exp_pos _), log_exp]
  norm_num

end LeanLab.HelfgottMajor.Residue309
