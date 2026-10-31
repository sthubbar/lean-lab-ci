/-
AI wrote this Lean code for CODEX task58.
Exact rational polynomial integration for the remaining nested integral certificates.
Binary Goldbach is open.
-/
import Mathlib

open Real intervalIntegral MeasureTheory

namespace LeanLab.ChenPrimeExceptional.Task58

abbrev Terms := List (ℚ × ℕ)

/-- Evaluate a finite list of rational monomials as a real polynomial. -/
def evalTerms (ts : Terms) (x : ℝ) : ℝ :=
  (ts.map (fun cn => (cn.1 : ℝ) * x ^ cn.2)).sum

/-- Distribute a product without combining equal powers. -/
def mulTerms (as bs : Terms) : Terms :=
  as.flatMap (fun a => bs.map (fun b => (a.1 * b.1, a.2 + b.2)))

/-- A rational polynomial antiderivative with zero constant term. -/
def antiTerms (ts : Terms) : Terms := ts.map (fun cn => (cn.1 / (cn.2 + 1), cn.2 + 1))

/-- Exact rational integral of a finite list of monomials. -/
def massTerms (ts : Terms) (a b : ℚ) : ℚ :=
  (ts.map (fun cn => cn.1 * (b ^ (cn.2 + 1) - a ^ (cn.2 + 1)) / (cn.2 + 1))).sum

@[simp] theorem evalTerms_nil (x : ℝ) : evalTerms [] x = 0 := rfl

@[simp] theorem evalTerms_cons (c : ℚ) (n : ℕ) (ts : Terms) (x : ℝ) :
    evalTerms ((c, n) :: ts) x = (c : ℝ) * x ^ n + evalTerms ts x := rfl

theorem evalTerms_append (as bs : Terms) (x : ℝ) :
    evalTerms (as ++ bs) x = evalTerms as x + evalTerms bs x := by
  simp [evalTerms]

theorem evalTerms_mul (as bs : Terms) (x : ℝ) :
    evalTerms (mulTerms as bs) x = evalTerms as x * evalTerms bs x := by
  induction as with
  | nil => simp [mulTerms, evalTerms]
  | cons a as ih =>
    change evalTerms ((bs.map (fun b => (a.1 * b.1, a.2 + b.2))) ++ mulTerms as bs) x = _
    rw [evalTerms_append, ih]
    have hm : evalTerms (bs.map (fun b => (a.1 * b.1, a.2 + b.2))) x =
        (a.1 : ℝ) * x ^ a.2 * evalTerms bs x := by
      clear ih
      induction bs with
      | nil => simp [evalTerms]
      | cons b bs ihb =>
        rcases b with ⟨bc, bn⟩
        simp only [List.map_cons, evalTerms_cons, ihb, Rat.cast_mul, pow_add, Prod.fst, Prod.snd]
        ring
    rw [hm]
    cases a
    simp only [evalTerms_cons]
    ring

theorem evalTerms_continuous (ts : Terms) : Continuous (evalTerms ts) := by
  induction ts with
  | nil => exact continuous_const
  | cons a ts ih =>
    exact (continuous_const.mul (continuous_id.pow a.2)).add ih

theorem integral_evalTerms (ts : Terms) (a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), evalTerms ts x) = (massTerms ts a b : ℝ) := by
  induction ts with
  | nil => simp [evalTerms, massTerms]
  | cons cn ts ih =>
    have hm : IntervalIntegrable (fun x : ℝ => (cn.1 : ℝ) * x ^ cn.2) volume a b :=
      (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
    have ht : IntervalIntegrable (evalTerms ts) volume a b :=
      (evalTerms_continuous ts).intervalIntegrable _ _
    simp only [List.map_cons, List.sum_cons, massTerms] at ih ⊢
    rw [show (fun x : ℝ => evalTerms (cn :: ts) x) =
        (fun x : ℝ => (cn.1 : ℝ) * x ^ cn.2 + evalTerms ts x) by rfl]
    rw [intervalIntegral.integral_add hm ht, intervalIntegral.integral_const_mul, integral_pow, ih]
    push_cast
    ring

/-- Integrating the monomial antiderivative gives the integral for real endpoints too. -/
theorem integral_evalTerms_real (ts : Terms) (a b : ℝ) :
    (∫ x in a..b, evalTerms ts x) = evalTerms (antiTerms ts) b - evalTerms (antiTerms ts) a := by
  induction ts with
  | nil => simp [evalTerms, antiTerms]
  | cons cn ts ih =>
    have hm : IntervalIntegrable (fun x : ℝ => (cn.1 : ℝ) * x ^ cn.2) volume a b :=
      (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
    have ht : IntervalIntegrable (evalTerms ts) volume a b :=
      (evalTerms_continuous ts).intervalIntegrable _ _
    change (∫ x in a..b, (cn.1 : ℝ) * x ^ cn.2 + evalTerms ts x) = _
    rw [intervalIntegral.integral_add hm ht, intervalIntegral.integral_const_mul, integral_pow, ih]
    simp only [antiTerms, List.map_cons, evalTerms_cons]
    push_cast
    ring


/-- Evaluate the same monomials in the rational field. -/
def evalTermsQ (ts : Terms) (x : ℚ) : ℚ := (ts.map (fun cn => cn.1 * x ^ cn.2)).sum

theorem evalTerms_cast (ts : Terms) (x : ℚ) : evalTerms ts (x : ℝ) = (evalTermsQ ts x : ℝ) := by
  induction ts with
  | nil => simp [evalTerms, evalTermsQ]
  | cons cn ts ih =>
    simp only [evalTermsQ, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
    rw [evalTerms_cons]
    exact congrArg ((cn.1 : ℝ) * (x : ℝ) ^ cn.2 + ·) ih

end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_nil
#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_cons
#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_append
#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_mul
#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.integral_evalTerms
#print axioms LeanLab.ChenPrimeExceptional.Task58.integral_evalTerms_real

#print axioms LeanLab.ChenPrimeExceptional.Task58.evalTerms_cast
