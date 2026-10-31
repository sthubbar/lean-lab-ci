import LeanLab.ChenDoubleSieve.ReducedIntegral
import LeanLab.ChenDoubleSieve.SigmaCertificate

/-!
# Exact interval certificates for the five reduced I1 kernels

Source: https://arxiv.org/pdf/0705.1652, page 22 and page 30, Table 1 rows 5 to 9.
These bounds certify the scalar reduced integrals only. The I1 Fubini bridge is separate.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000

noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04Reduced
open Wu04Integral (logLower logUpper logLowerQ logUpperQ logLowerQ_cast logUpperQ_cast)

/-- Exact rational s and s prime parameters for the five I1 rows. -/
def tableS : Fin 5 → ℚ := ![26/10, 27/10, 28/10, 29/10, 3]
def tableSp : Fin 5 → ℚ := ![358/100, 347/100, 334/100, 319/100, 3]

/-- Certified endpoints at scale one trillion. -/
def volumeLo : Fin 5 → ℚ :=
  ![16681376280/1000000000000, 8070405252/1000000000000, 2797533417/1000000000000, 438995008/1000000000000, 0/1000000000000]
def volumeHi : Fin 5 → ℚ :=
  ![16681376281/1000000000000, 8070405253/1000000000000, 2797533418/1000000000000, 438995009/1000000000000, 0/1000000000000]

def lowerVolumeQ (i : Fin 5) : ℚ :=
  (tableSp i + tableS i) * logLowerQ 10 (tableSp i / tableS i) - 2 * (tableSp i - tableS i)
def upperVolumeQ (i : Fin 5) : ℚ :=
  (tableSp i + tableS i) * logUpperQ 10 (tableSp i / tableS i) - 2 * (tableSp i - tableS i)

/-- All five logarithm enclosure computations are exact rational checks. -/
theorem reduced_certificate :
    (∀ i : Fin 5, 0 < tableS i ∧ tableS i ≤ tableSp i) ∧
    (∀ i : Fin 5, volumeLo i ≤ lowerVolumeQ i ∧ upperVolumeQ i ≤ volumeHi i) := by
  decide +kernel

/-- Rigorous interval bounds for all five actual reduced integrals. -/
theorem reducedTable_bounds (i : Fin 5) :
    (volumeLo i : ℝ) ≤ reducedVolume (1 / (tableSp i : ℝ)) (1 / (tableS i : ℝ)) ∧
    reducedVolume (1 / (tableSp i : ℝ)) (1 / (tableS i : ℝ)) ≤ (volumeHi i : ℝ) := by
  have hs0 : (0 : ℝ) < tableS i := by exact_mod_cast (reduced_certificate.1 i).1
  have hssp : (tableS i : ℝ) ≤ tableSp i := by exact_mod_cast (reduced_certificate.1 i).2
  have hsp0 : (0 : ℝ) < tableSp i := hs0.trans_le hssp
  rw [reducedVolume_parameters hs0 hssp]
  have hlog := Wu04Integral.log_bounds 10 (y := (tableSp i : ℝ) / (tableS i : ℝ))
    ((le_div_iff₀ hs0).mpr (by simpa using hssp))
  have hL : (volumeLo i : ℝ) ≤ (lowerVolumeQ i : ℝ) := by
    exact_mod_cast (reduced_certificate.2 i).1
  have hU : (upperVolumeQ i : ℝ) ≤ (volumeHi i : ℝ) := by
    exact_mod_cast (reduced_certificate.2 i).2
  have hLc : (lowerVolumeQ i : ℝ) =
      ((tableSp i : ℝ) + (tableS i : ℝ)) * logLower 10 ((tableSp i : ℝ) / (tableS i : ℝ)) -
        2 * ((tableSp i : ℝ) - (tableS i : ℝ)) := by
    simp [lowerVolumeQ]
  have hUc : (upperVolumeQ i : ℝ) =
      ((tableSp i : ℝ) + (tableS i : ℝ)) * logUpper 10 ((tableSp i : ℝ) / (tableS i : ℝ)) -
        2 * ((tableSp i : ℝ) - (tableS i : ℝ)) := by
    simp [upperVolumeQ]
  rw [hLc] at hL
  rw [hUc] at hU
  constructor
  · exact hL.trans (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog.1 (by linarith)) _)
  · exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog.2 (by linarith)) _).trans hU

end LeanLab.ChenDoubleSieve.Wu04Reduced

#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.reduced_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04Reduced.reducedTable_bounds
