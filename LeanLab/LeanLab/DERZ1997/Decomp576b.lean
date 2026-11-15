import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Elementary Backlund pairing estimates for Trudgian arXiv:1206.1844v4.
These are the algebraic steps in pages 5 and 6, displays 3.7 and 3.11.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576b

/-- Backlund's paired distance product on the left of the Jensen centre.
Trudgian page 5, display 3.7. The reflection inequality is retained explicitly.
-/
theorem paired_distance_left576 {η x y : ℝ} (hη : 0 ≤ η)
    (hx : 1 / 2 ≤ x) (hxc : x ≤ 1 + η) (hy : y ≤ 1 / 2)
    (hpair : 1 - x ≤ y) :
    |1 + η - x| * |1 + η - y| ≤ (1 / 2 + η) ^ 2 := by
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 + η - x),
    abs_of_nonneg (by linarith : 0 ≤ 1 + η - y)]
  have hprod : (1 + η - x) * (1 + η - y) ≤ (1 + η - x) * (η + x) := by
    gcongr
    linarith
  nlinarith [sq_nonneg (x - 1 / 2)]

/-- Backlund's paired distance product on the right of the Jensen centre.
Trudgian page 5, display 3.8, before fixing the outer endpoint.
-/
theorem paired_distance_right576 {η x y σ : ℝ} (hη : 0 ≤ η)
    (hx : 1 + η ≤ x) (hxσ : x ≤ σ) (hy : y ≤ 1 / 2)
    (hpair : 1 - x ≤ y) :
    |1 + η - x| * |1 + η - y| ≤ σ ^ 2 - σ - η * (1 + η) := by
  rw [abs_of_nonpos (by linarith : 1 + η - x ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ 1 + η - y)]
  have hp : (-(1 + η - x)) * (1 + η - y) ≤ (x - 1 - η) * (η + x) := by
    have heq : -(1 + η - x) = x - 1 - η := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hmono : x ^ 2 - x ≤ σ ^ 2 - σ := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ σ - x)
      (by linarith : 0 ≤ σ + x - 1)]
  nlinarith

/-- The product bound for a reflected pair yields two log-radius weights.
Trudgian page 6, display 3.11. Both distances are positive, so no central zero
is hidden by the totalized real logarithm.
-/
theorem paired_jensen_weight576 {r a d e : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < d) (he : 0 < e) (hprod : d * e ≤ a ^ 2) :
    2 * Real.log r ≤ Real.log (r * a / d) + Real.log (r * a / e) := by
  have hratio : r ^ 2 ≤ (r * a / d) * (r * a / e) := by
    have heq : (r * a / d) * (r * a / e) = r ^ 2 * a ^ 2 / (d * e) := by ring
    rw [heq, le_div_iff₀ (mul_pos hd he)]
    nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg r)]
  have hlog := Real.log_le_log (sq_pos_of_pos hr) hratio
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hlog
  simpa using hlog

/-- The two distance cases agree at Backlund's chosen endpoint.
Trudgian page 5, displays 3.7 and 3.8 and the sentence following them.
-/
theorem paired_distance576 {η x y : ℝ} (hη : 0 ≤ η)
    (hx : 1 / 2 ≤ x) (hxσ : x ≤ 1 / 2 + Real.sqrt 2 * (1 / 2 + η))
    (hy : y ≤ 1 / 2) (hpair : 1 - x ≤ y) :
    |1 + η - x| * |1 + η - y| ≤ (1 / 2 + η) ^ 2 := by
  by_cases hxc : x ≤ 1 + η
  · exact paired_distance_left576 hη hx hxc hy hpair
  · have h := paired_distance_right576 hη (le_of_not_ge hxc) hxσ hy hpair
    have hs :
        (1 / 2 + Real.sqrt 2 * (1 / 2 + η)) ^ 2 -
          (1 / 2 + Real.sqrt 2 * (1 / 2 + η)) - η * (1 + η) =
            (1 / 2 + η) ^ 2 := by
      calc
        _ = ((Real.sqrt 2) ^ 2 - 1) * (1 / 2 + η) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rwa [hs] at h

/-- Every unpaired right zero has distance at most the base radius.
Trudgian page 5, sentence after display 3.8.
-/
theorem unpaired_distance576 {η x : ℝ} (hη : 0 ≤ η)
    (hx : 1 / 2 ≤ x) (hxσ : x ≤ 1 / 2 + Real.sqrt 2 * (1 / 2 + η)) :
    |1 + η - x| ≤ 1 / 2 + η := by
  have hs : Real.sqrt 2 ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have ha : 0 ≤ 1 / 2 + η := by linarith
  have hm := mul_le_mul_of_nonneg_right hs ha
  rw [abs_le]
  constructor <;> linarith

/-- The finite paired product in Backlund's Jensen lower bound.
Trudgian page 5, display 3.3. The indexing sets record paired and unpaired zeros.
-/
theorem backlund_product576 {ι κ : Type*} (P : Finset ι) (U : Finset κ)
    {η : ℝ} (hη : 0 ≤ η) (x y : ι → ℝ) (u : κ → ℝ)
    (hx : ∀ i ∈ P, 1 / 2 ≤ x i ∧ x i ≤ 1 / 2 + Real.sqrt 2 * (1 / 2 + η))
    (hy : ∀ i ∈ P, y i ≤ 1 / 2 ∧ 1 - x i ≤ y i)
    (hu : ∀ i ∈ U, 1 / 2 ≤ u i ∧ u i ≤ 1 / 2 + Real.sqrt 2 * (1 / 2 + η)) :
    (∏ i ∈ P, |1 + η - x i| * |1 + η - y i|) *
      (∏ i ∈ U, |1 + η - u i|) ≤ (1 / 2 + η) ^ (2 * P.card + U.card) := by
  have hp : (∏ i ∈ P, |1 + η - x i| * |1 + η - y i|) ≤
      ∏ _i ∈ P, (1 / 2 + η) ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact paired_distance576 hη (hx i hi).1 (hx i hi).2 (hy i hi).1 (hy i hi).2
  have hu' : (∏ i ∈ U, |1 + η - u i|) ≤ ∏ _i ∈ U, (1 / 2 + η) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      exact unpaired_distance576 hη (hu i hi).1 (hu i hi).2
  have hm := mul_le_mul hp hu' (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
  simpa only [Finset.prod_const, ← pow_mul, ← pow_add] using hm

/-- The finite logarithmic Jensen weight supplied by paired and unpaired distances.
Trudgian page 6, display 3.9, with arbitrary finite indexing sets.
-/
theorem backlund_log_weight576 {ι κ : Type*} (P : Finset ι) (U : Finset κ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (d e : ι → ℝ) (u : κ → ℝ)
    (hd : ∀ i ∈ P, 0 < d i) (he : ∀ i ∈ P, 0 < e i)
    (hp : ∀ i ∈ P, d i * e i ≤ a ^ 2)
    (hu : ∀ i ∈ U, 0 < u i ∧ u i ≤ a) :
    (2 * (P.card : ℝ) + (U.card : ℝ)) * Real.log r ≤
      (∑ i ∈ P, (Real.log (r * a / d i) + Real.log (r * a / e i))) +
        ∑ i ∈ U, Real.log (r * a / u i) := by
  have hP := Finset.sum_le_sum (s := P) (fun i hi =>
    paired_jensen_weight576 hr ha (hd i hi) (he i hi) (hp i hi))
  have hU : (∑ _i ∈ U, Real.log r) ≤ ∑ i ∈ U, Real.log (r * a / u i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.log_le_log hr
    rw [le_div_iff₀ (hu i hi).1]
    exact mul_le_mul_of_nonneg_left (hu i hi).2 hr.le
  have h := add_le_add hP hU
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  nlinarith

/-- A quadratic upper envelope for the negative cosine part in the Jensen mean.
Trudgian page 8, display 4.7. This derived envelope avoids a piecewise integral.
-/
theorem jensen_quadratic_envelope576 {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    max (-c) 0 ≤ (1 - c) ^ 2 / 4 := by
  rw [max_le_iff]
  constructor
  · nlinarith [sq_nonneg (1 + c)]
  · positivity

/-- The radius ratio twelve sevenths leaves room below a quarter-log coefficient.
Trudgian pages 8 and 9, displays 4.7 and 4.12. The numerator comes from the
quadratic cosine envelope with radius nine sevenths. This is a derived loose budget.
-/
theorem jensen_coefficient_budget576 :
    3 * (9 / 7 : ℝ) / (32 * Real.log (12 / 7 : ℝ)) ≤ 0.25 := by
  have hlog0 : 0 < Real.log (12 / 7 : ℝ) := Real.log_pos (by norm_num)
  have hlow := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 7)
  norm_num at hlow
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * Real.log (12 / 7 : ℝ))]
  nlinarith

end LeanLab.DERZ1997.Decomp576b
