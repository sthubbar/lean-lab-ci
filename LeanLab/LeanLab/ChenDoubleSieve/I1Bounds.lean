import LeanLab.ChenDoubleSieve.BuchstabBounds
import LeanLab.ChenDoubleSieve.XiKernelBounds
import LeanLab.ChenDoubleSieve.ReducedIntegral

/-!
# Integrability and uniform domination for Wu's I1

Source: https://arxiv.org/pdf/0705.1652, page 22, Lemma 5.1.
The comparison with the reduced scalar integral is a named separate obligation.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Functional (domain IsBuchstab buchstabIntegral I1)

/-- Every ordered finite dimensional box is compact. -/
theorem domain_isCompact {n : ℕ} (lo hi : Fin n → ℝ) : IsCompact (domain lo hi) := by
  have he : domain lo hi = Icc lo hi ∩ {x | Monotone x} := by
    ext x
    simp only [domain, mem_setOf_eq, mem_inter_iff, mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨hm, hx⟩
      exact ⟨⟨fun j => (hx j).1, fun j => (hx j).2⟩, hm⟩
    · rintro ⟨⟨hlo, hhi⟩, hm⟩
      exact ⟨hm, fun j => ⟨hlo j, hhi j⟩⟩
  rw [he]
  exact isCompact_Icc.inter_right isClosed_monotone

/-- The reciprocal kernel on the three dimensional ordered domain. -/
def reciprocal (x : Fin 3 → ℝ) : ℝ := 1 / ((∏ j, x j) * x 1)

/-- The integral of that kernel before the Fubini reduction. -/
def reciprocalIntegral (s sp : ℝ) : ℝ :=
  ∫ x in domain (fun _ : Fin 3 => 1 / sp) (fun _ => 1 / s), reciprocal x

/-- Denominators are positive throughout the I1 domain. -/
theorem denominator_pos {s sp : ℝ} (hsp : 0 < sp) {x : Fin 3 → ℝ}
    (hx : x ∈ domain (fun _ => 1 / sp) (fun _ => 1 / s)) :
    0 < (∏ j, x j) * x 1 := by
  have hp (j : Fin 3) : 0 < x j := (one_div_pos.mpr hsp).trans_le (hx.2 j).1
  exact mul_pos (Finset.prod_pos (fun j hj => hp j)) (hp 1)

/-- The reciprocal kernel is integrable on every positive I1 box. -/
theorem reciprocal_integrable {s sp : ℝ} (hsp : 0 < sp) :
    IntegrableOn reciprocal (domain (fun _ => 1 / sp) (fun _ => 1 / s)) volume := by
  apply ContinuousOn.integrableOn_compact (domain_isCompact _ _)
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  exact (denominator_pos hsp hx).ne'

/-- Each Buchstab integrand is integrable under its defining continuity assumption. -/
theorem I1_integrable {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp φ : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) (hφ : 2 ≤ φ) :
    IntegrableOn (fun x : Fin 3 → ℝ =>
      ω ((φ - ∑ j, x j) / x 1) / ((∏ j, x j) * x 1))
      (domain (fun _ => 1 / sp) (fun _ => 1 / s)) volume := by
  apply ContinuousOn.integrableOn_compact (domain_isCompact _ _)
  have harg : ContinuousOn (fun x : Fin 3 → ℝ => (φ - ∑ j, x j) / x 1)
      (domain (fun _ => 1 / sp) (fun _ => 1 / s)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact ne_of_gt ((one_div_pos.mpr hsp).trans_le (hx.2 1).1)
  have hc : ContinuousOn (fun x : Fin 3 → ℝ => ω ((φ - ∑ j, x j) / x 1))
      (domain (fun _ => 1 / sp) (fun _ => 1 / s)) := by
    apply hω.1.comp harg
    intro x hx
    change 1 ≤ (φ - ∑ j, x j) / x 1
    linarith [Wu04Functional.I1_argument_ge_two hs hsp hφ hx]
  apply ContinuousOn.div hc (by fun_prop)
  intro x hx
  exact (denominator_pos hsp hx).ne'

/-- The global Buchstab bound dominates every phi in the defining supremum.
CONDITIONAL ON IsBuchstab, with no numerical integral hypothesis. -/
theorem I1_integral_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp φ : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) (hφ : 2 ≤ φ) :
    buchstabIntegral ω 1 (fun _ => 1 / sp) (fun _ => 1 / s) φ ≤
      Wu04Buchstab.C * reciprocalIntegral s sp := by
  have hi := I1_integrable hω hs hsp hφ
  have hk := (reciprocal_integrable (s := s) hsp).const_mul Wu04Buchstab.C
  have hd := (domain_isCompact (fun _ : Fin 3 => 1 / sp) (fun _ => 1 / s)).measurableSet
  have hm := MeasureTheory.setIntegral_mono_on hi hk hd (fun x hx => by
    have hw := Wu04Buchstab.buchstab_le_567144 hω (Wu04Functional.I1_argument_ge_two hs hsp hφ hx)
    have hp := denominator_pos hsp hx
    have hh := div_le_div_of_nonneg_right hw hp.le
    simpa only [reciprocal, Wu04Buchstab.C, mul_one_div] using hh)
  simpa [buchstabIntegral, reciprocalIntegral, MeasureTheory.integral_const_mul] using hm

/-- The supremum I1 obeys the same uniform bound.
CONDITIONAL ON IsBuchstab only. -/
theorem I1_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) :
    I1 ω s sp ≤ Wu04Buchstab.C * reciprocalIntegral s sp := by
  apply csSup_le
  · exact ⟨buchstabIntegral ω 1 (fun _ => 1 / sp) (fun _ => 1 / s) 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, hφ, rfl⟩
    exact I1_integral_le hω hs hsp hφ

/-- The exact Fubini conversion still needed for the scalar numerical certificates. -/
def ReciprocalReduction (s sp : ℝ) : Prop :=
  reciprocalIntegral s sp = Wu04Reduced.reducedVolume (1 / sp) (1 / s)

/-- The scalar certificates become I1 bounds once the reduction is proved.
CONDITIONAL ON IsBuchstab and ReciprocalReduction. -/
theorem I1_le_reduced {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp : ℝ}
    (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp) (hr : ReciprocalReduction s sp) :
    I1 ω s sp ≤ Wu04Buchstab.C * Wu04Reduced.reducedVolume (1 / sp) (1 / s) := by
  rw [← hr]
  exact I1_le hω hs hsp

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.domain_isCompact
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.denominator_pos
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.reciprocal_integrable
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_integrable
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_integral_le
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_le
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_le_reduced
