import LeanLab.ExceptionalSet.Decomp464j
import LeanLab.ExceptionalSet.Decomp371d
import LeanLab.ExceptionalSet.Decomp404b

/-!
The integrability step in the generic Fourier fold.
Source: P0082 page 356, first proof display of Lemma 1.
The existing fold_of_integrable theorem already proves the actual exchange.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446b

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (eC ftR hcheck norm_eC)

/-- LEAF. P0082 page 356, integrability needed for the first proof display
of Lemma 1. Compact Fourier support must control a merely periodic L1
factor. This leaf asserts only product integrability, without modulation,
periodization or a Fourier coefficient identity. -/
theorem leaf_product_integrable (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) :
    Integrable (fun α : ℝ => h α * K α) := by
  exact Decomp464j.product_integrable_supplied h K hper hh hK hcont hsupp

/-- Assembly. P0082 page 356, first proof display of Lemma 1.
This is the exact existing Decomp371d.leaf_fold statement. The integral
exchange itself is reused from the proved fold_of_integrable theorem. -/
theorem fold_assembly (h K : ℝ → ℂ) (hper : Function.Periodic h 1)
    (hh : IntervalIntegrable h volume 0 1) (hK : Integrable K) (hcont : Continuous K)
    (hsupp : ∀ α : ℝ, 1 < |α| → ftR K α = 0) (v : ℝ) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1,
        h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  have hg := leaf_product_integrable h K hper hh hK hcont hsupp
  have he : Continuous (fun α : ℝ => eC (-(α * v))) := by
    unfold eC
    fun_prop
  apply Decomp404b.fold_of_integrable h K hper v
  exact hg.mul_bdd he.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun α => (norm_eC (-(α * v))).le))

/-- Assembly. P0082 page 356, full Lemma 1. The new product integrability
leaf and the inherited generic Poisson leaf are the only open inputs. -/
theorem lemma1_supplied : LeanLab.ExceptionalSet.U1539.Lemma1 := by
  intro h K hper hh hK hcont hsupp v
  have hg0 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * (⌊v⌋ : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  have hg1 : IntervalIntegrable (fun α : ℝ => h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) volume 0 1 := by
    apply hh.mul_continuousOn
    unfold eC
    fun_prop
  calc
    _ = ∫ α in (0 : ℝ)..1,
        (h α * eC (-(α * (⌊v⌋ : ℝ)))) * ftR K (Int.fract v) +
          (h α * eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ)))) * ftR K (Int.fract v - 1) := by
      rw [fold_assembly h K hper hh hK hcont hsupp v]
      apply intervalIntegral.integral_congr
      intro α hα
      dsimp only
      rw [Decomp371d.leaf_poisson K hK hcont hsupp v α]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (hg0.mul_const (ftR K (Int.fract v)))
        (hg1.mul_const (ftR K (Int.fract v - 1))),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      unfold hcheck
      ring

end LeanLab.ExceptionalSet.Decomp446b
