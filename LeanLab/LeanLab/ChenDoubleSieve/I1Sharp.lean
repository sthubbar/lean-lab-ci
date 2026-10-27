import LeanLab.ChenDoubleSieve.I1Numerics
import LeanLab.ChenDoubleSieve.BuchstabSharp

/-!
# Sharper I1 bounds under the defining Buchstab equations

Source: https://arxiv.org/pdf/0705.1652, pages 9 and 22 and Table 1 on page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open MeasureTheory Set
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Functional

theorem I1_integral_le_sharp {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp φ : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) (hφ : 2 ≤ φ) :
    buchstabIntegral ω 1 (fun _ => 1 / sp) (fun _ => 1 / s) φ ≤
      (5671433/10000000 : ℝ) * reciprocalIntegral s sp := by
  have hi := I1_integrable hω hs hsp hφ
  have hk := (reciprocal_integrable (s := s) hsp).const_mul (5671433/10000000 : ℝ)
  have hd := (domain_isCompact (fun _ : Fin 3 => 1 / sp) (fun _ => 1 / s)).measurableSet
  have hm := MeasureTheory.setIntegral_mono_on hi hk hd (fun x hx => by
    have hw := Wu04Buchstab.buchstab_le_5671433 hω (Wu04Functional.I1_argument_ge_two hs hsp hφ hx)
    have hp := denominator_pos hsp hx
    have hh := div_le_div_of_nonneg_right hw hp.le
    simpa only [reciprocal, mul_one_div] using hh)
  simpa [buchstabIntegral, reciprocalIntegral, MeasureTheory.integral_const_mul] using hm

/-- The supremum I1 obeys the same uniform bound.
CONDITIONAL ON IsBuchstab only. -/
theorem I1_le_sharp {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) :
    I1 ω s sp ≤ (5671433/10000000 : ℝ) * reciprocalIntegral s sp := by
  apply csSup_le
  · exact ⟨buchstabIntegral ω 1 (fun _ => 1 / sp) (fun _ => 1 / s) 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, hφ, rfl⟩
    exact I1_integral_le_sharp hω hs hsp hφ


/-- Rounded sharper uniform I1 enclosures. -/
def upperI1Sharp : Fin 5 → ℚ := ![9460730793/1000000000000, 4577076268/1000000000000, 1586602335/1000000000000, 248973079/1000000000000, 0/1000000000000]

theorem upperI1Sharp_certificate : ∀ i : Fin 5,
    (5671433/10000000 : ℚ) * Wu04Reduced.volumeHi i ≤ upperI1Sharp i := by decide +kernel

/-- Actual sharper I1 bounds, CONDITIONAL ON IsBuchstab only. -/
theorem I1_table_upper_sharp {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω) (i : Fin 5) :
    Wu04Functional.I1 ω (Wu04Reduced.tableS i : ℝ) (Wu04Reduced.tableSp i : ℝ) ≤ (upperI1Sharp i : ℝ) := by
  have hs : (5/2 : ℝ) ≤ Wu04Reduced.tableS i := by
    have hh : ((5/2 : ℚ) : ℝ) ≤ (Wu04Reduced.tableS i : ℝ) := by exact_mod_cast (numerical_parameters i).1
    push_cast at hh
    exact hh
  have hp : (0 : ℝ) < Wu04Reduced.tableSp i := by exact_mod_cast (numerical_parameters i).2.1
  have hsp : (Wu04Reduced.tableS i : ℝ) ≤ Wu04Reduced.tableSp i := by exact_mod_cast (numerical_parameters i).2.2
  have hr := reciprocal_reduction (by linarith : (0 : ℝ) < Wu04Reduced.tableS i) hsp
  have hI := I1_le_sharp hω hs hp
  rw [hr] at hI
  have hv := (Wu04Reduced.reducedTable_bounds i).2
  have hc := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 5671433/10000000)
  have hb : (5671433/10000000 : ℝ) * (Wu04Reduced.volumeHi i : ℝ) ≤ (upperI1Sharp i : ℝ) := by
    have hh : (((5671433/10000000 : ℚ) * Wu04Reduced.volumeHi i : ℚ) : ℝ) ≤ (upperI1Sharp i : ℝ) := by
      exact_mod_cast upperI1Sharp_certificate i
    push_cast at hh
    exact hh
  exact hI.trans (hc.trans hb)

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_integral_le_sharp

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_le_sharp

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.upperI1Sharp_certificate

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_table_upper_sharp
