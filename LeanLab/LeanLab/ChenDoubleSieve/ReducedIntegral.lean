import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# The reciprocal kernel remaining after two I1 integrations

Source: https://arxiv.org/pdf/0705.1652, page 22, Lemma 5.1.
This file evaluates the reduced scalar integral. The Fubini bridge from the
three dimensional integral is a separate obligation.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Reduced

/-- The scalar reciprocal kernel on the ordered I1 simplex. -/
def reducedVolume (a b : ℝ) : ℝ :=
  ∫ u in a..b, log (u / a) * log (b / u) / u ^ 2

/-- A closed antiderivative for the reduced kernel. -/
def primitive (a b u : ℝ) : ℝ :=
  let v := log u - log a
  let L := log b - log a
  (v ^ 2 + (2 - L) * v + (2 - L)) / u

/-- The antiderivative is exact on positive arguments. -/
theorem primitive_deriv {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    HasDerivAt (primitive a b) (log (u / a) * log (b / u) / u ^ 2) u := by
  have hv := (Real.hasDerivAt_log hu.ne').sub_const (log a)
  have hp := (((hv.pow 2).add (hv.const_mul (2 - (log b - log a)))).add_const
    (2 - (log b - log a))).div (hasDerivAt_id u) hu.ne'
  convert hp using 1
  · rfl
  · dsimp
    rw [log_div hu.ne' ha.ne', log_div hb.ne' hu.ne']
    field_simp
    ring

/-- Exact evaluation of the reduced kernel integral. -/
theorem reducedVolume_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    reducedVolume a b = (log (b / a) - 2) / a + (log (b / a) + 2) / b := by
  have hb : 0 < b := ha.trans_le hab
  have hci : ContinuousOn (fun u => log (u / a) * log (b / u) / u ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.log
        · exact continuousOn_id.div_const a
        · intro u hu; exact ne_of_gt (div_pos (ha.trans_le hu.1) ha)
      · apply ContinuousOn.log
        · apply ContinuousOn.div continuousOn_const continuousOn_id
          intro u hu; exact (ha.trans_le hu.1).ne'
        · intro u hu; exact ne_of_gt (div_pos hb (ha.trans_le hu.1))
    · exact continuousOn_id.pow 2
    · intro u hu; exact pow_ne_zero 2 (ha.trans_le hu.1).ne'
  have heq := integral_eq_sub_of_hasDerivAt
    (fun u hu => primitive_deriv ha hb (by rw [uIcc_of_le hab] at hu; exact ha.trans_le hu.1))
    hci.intervalIntegrable
  change reducedVolume a b = primitive a b b - primitive a b a at heq
  rw [heq]
  simp only [primitive, sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, zero_add,
    log_div hb.ne' ha.ne']
  field_simp
  ring

/-- The form in Wu's s and s prime parameters. -/
theorem reducedVolume_parameters {s sp : ℝ} (hs : 0 < s) (hssp : s ≤ sp) :
    reducedVolume (1 / sp) (1 / s) = (sp + s) * log (sp / s) - 2 * (sp - s) := by
  have hsp : 0 < sp := hs.trans_le hssp
  rw [reducedVolume_eq (one_div_pos.mpr hsp) (one_div_le_one_div_of_le hs hssp)]
  have he : (1 / s) / (1 / sp) = sp / s := by field_simp
  rw [he]
  field_simp
  ring

/-- Nonnegative parameters give a nonnegative reduced volume. -/
theorem reducedVolume_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ reducedVolume a b := by
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  have hu0 := ha.trans_le hu.1
  apply div_nonneg _ (sq_nonneg u)
  apply mul_nonneg
  · exact log_nonneg ((le_div_iff₀ ha).mpr (by simpa using hu.1))
  · exact log_nonneg ((le_div_iff₀ hu0).mpr (by simpa using hu.2))

end LeanLab.ChenDoubleSieve.Wu04Reduced

#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.primitive_deriv
#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.reducedVolume_eq
#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.reducedVolume_parameters
#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.reducedVolume_nonneg
