import LeanLab.ChenDoubleSieve.Decomp587f
import LeanLab.ChenDoubleSieve.Task587Row3NineSupply

/-!
A compact phi leaf for Wu 2004 Lemma 5.2 page 26, D2,9.
Source: https://arxiv.org/abs/0705.1652, Table 1 row four page 30.
The unbounded tail is supplied by an exact polynomial certificate.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row four page 30.
Only the compact phi interval from two through fourteen fifths remains.
The spatial domain is 25/89 at most t at most u at most v at most 2/5.
Certify the Buchstab profile on this compact parameter interval and integrate
reciprocal polynomial majorants with exact ordered monomial moments.
This piece contains no supremum and no unbounded phi tail. -/
theorem r3Nine_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (14 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤
      (12408337 / 1000000000 : ℝ) := by
  by_cases hs : φ ≤ (13 / 5 : ℝ)
  · exact r3Nine_short hω hz hφ hs
  · exact r3Nine_integral_early_tail hω (le_of_not_ge hs)

/-- The exact original I2_r3_9 statement follows from the compact leaf and the proved tail.
Wu 2004 Lemma 5.2 page 26, Table 1 row four page 30.
CONDITIONAL ON r3Nine_compact. -/
theorem I2_r3_9_from_compact {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 0 ≤ (12408337/1000000000 : ℝ) := by
  have hb : buchstabSup ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) ≤
      (12408337 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) 2,
        2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      by_cases ht : φ ≤ (14 / 5 : ℝ)
      · exact r3Nine_compact hω hz hφ ht
      · exact r3Nine_integral_tail hω (le_of_not_ge ht)
  convert hb using 1 <;> norm_num [I2, tableParams]

end LeanLab.ChenDoubleSieve.Task587
