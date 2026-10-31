/-
AI wrote this Lean code for CODEX task58.
Accelerated enclosure for the IB1 integral in the lab model of P0039 equation 3.9.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Series
import LeanLab.ChenPrimeExceptional.Task58Integrands

open Real Finset intervalIntegral MeasureTheory Set

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The reciprocal factor after the change of variable q equals one minus three t. -/
def reciprocalKernel (q : ℝ) : ℝ := 1 / (1 - q) + 1 / (2 + q)

/-- The reciprocal polynomial used for the accelerated certificate. -/
def reciprocalPoly (q : ℝ) : ℝ := geomPoly 70 q + geomPoly 70 (-q / 2) / 2

/-- The transformed density kernel. -/
def massKernel (q : ℝ) : ℝ := log (1 + q) * reciprocalKernel q

/-- The polynomial density kernel. -/
def massPoly (q : ℝ) : ℝ := logPoly 60 q * reciprocalPoly q

theorem reciprocalPoly_error {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (7 / 10)) :
    |reciprocalPoly q - reciprocalKernel q| ≤ (3 / 20000000000 : ℝ) := by
  have hqabs : |q| ≤ 7 / 10 := by rw [abs_of_nonneg hq.1]; exact hq.2
  have hqabs' : |(-q / 2)| ≤ 7 / 10 := by
    rw [abs_div, abs_neg, abs_of_nonneg hq.1]
    norm_num
    linarith [hq.2]
  have h1 := geomPoly70_error hqabs
  have h2 := geomPoly70_error hqabs'
  have he : reciprocalPoly q - reciprocalKernel q =
      (geomPoly 70 q - 1 / (1 - q)) +
      (geomPoly 70 (-q / 2) - 1 / (1 - (-q / 2))) / 2 := by
    unfold reciprocalPoly reciprocalKernel
    have hratio : (1 : ℝ) / (1 - (-q / 2)) / 2 = 1 / (2 + q) := by
      rw [div_div]
      congr 1
      ring
    rw [sub_div, hratio]
    ring
  rw [he]
  have htri := abs_add_le (geomPoly 70 q - 1 / (1 - q))
    ((geomPoly 70 (-q / 2) - 1 / (1 - (-q / 2))) / 2)
  rw [abs_div] at htri
  norm_num at htri
  simp only [one_div] at h1 h2 ⊢
  linarith

theorem reciprocalKernel_bounds {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (7 / 10)) :
    0 ≤ reciprocalKernel q ∧ reciprocalKernel q ≤ 4 := by
  have h1 : 0 < 1 - q := by linarith [hq.2]
  have h2 : 0 < 2 + q := by linarith [hq.1]
  have h3 : 1 / (1 - q) ≤ (10 / 3 : ℝ) := by
    rw [div_le_iff₀ h1]
    linarith [hq.2]
  have h4 : 1 / (2 + q) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ h2]
    linarith [hq.1]
  unfold reciprocalKernel
  exact ⟨add_nonneg (by positivity) (by positivity), by linarith⟩

theorem logPoly60_abs_le_one {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (7 / 10)) :
    |logPoly 60 q| ≤ 1 := by
  have h := logPoly60_error hq.1 hq.2
  rw [abs_le] at h
  have h0 := log_nonneg (show 1 ≤ 1 + q by linarith [hq.1])
  have h1 := log_le_sub_one_of_pos (show 0 < 1 + q by linarith [hq.1])
  apply abs_le.mpr
  constructor <;> linarith [hq.2]

/-- The complete transformed density has a uniform polynomial enclosure. -/
theorem massPoly_error {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) (7 / 10)) :
    |massPoly q - massKernel q| ≤ (1 / 100000000 : ℝ) := by
  have hL := logPoly60_abs_le_one hq
  have hR := reciprocalPoly_error hq
  have hlog := logPoly60_error hq.1 hq.2
  have hg := reciprocalKernel_bounds hq
  have hgabs : |reciprocalKernel q| ≤ 4 := by rw [abs_of_nonneg hg.1]; exact hg.2
  have hlog' : |logPoly 60 q - log (1 + q)| ≤ (2 / 1000000000 : ℝ) := by
    rw [abs_sub_comm]
    exact hlog
  have he : massPoly q - massKernel q =
      logPoly 60 q * (reciprocalPoly q - reciprocalKernel q) +
      (logPoly 60 q - log (1 + q)) * reciprocalKernel q := by
    unfold massPoly massKernel
    ring
  rw [he]
  calc
    _ ≤ |logPoly 60 q * (reciprocalPoly q - reciprocalKernel q)| +
        |(logPoly 60 q - log (1 + q)) * reciprocalKernel q| := abs_add_le _ _
    _ = |logPoly 60 q| * |reciprocalPoly q - reciprocalKernel q| +
        |logPoly 60 q - log (1 + q)| * |reciprocalKernel q| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (3 / 20000000000 : ℝ) + (2 / 1000000000 : ℝ) * 4 :=
      add_le_add (mul_le_mul hL hR (abs_nonneg _) (by norm_num))
        (mul_le_mul hlog' hgabs (abs_nonneg _) (by norm_num))
    _ ≤ _ := by norm_num

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.reciprocalPoly_error
#print axioms LeanLab.ChenPrimeExceptional.Task58.reciprocalKernel_bounds
#print axioms LeanLab.ChenPrimeExceptional.Task58.logPoly60_abs_le_one
#print axioms LeanLab.ChenPrimeExceptional.Task58.massPoly_error
