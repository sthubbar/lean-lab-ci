import LeanLab.ChenDoubleSieve.I1Sharp
import LeanLab.ChenDoubleSieve.BuchstabTail

/-!
# A tail saving in the I1 integral

Source: https://arxiv.org/pdf/0705.1652, page 22, Lemma 5.1.
The smaller ordered simplex uses the proved Buchstab bound above three.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Functional

/-- Every point in the smaller simplex has Buchstab argument at least three. -/
theorem I1_argument_ge_three {sp φ : ℝ} (hsp : 0 < sp) (hφ : 2 ≤ φ)
    {x : Fin 3 → ℝ} (hx : x ∈ domain (fun _ => 1/sp) (fun _ => 1/(3 : ℝ))) :
    3 ≤ (φ - ∑ j, x j) / x 1 := by
  have hp : 0 < x 1 := (one_div_pos.mpr hsp).trans_le (hx.2 1).1
  rw [le_div_iff₀ hp]
  have h0 := (hx.2 0).2
  have h1 := (hx.2 1).2
  have h2 := (hx.2 2).2
  simp only [Fin.sum_univ_succ] at *
  norm_num at h0 h1 h2 ⊢
  linarith

/-- The pointwise tail saving survives integration uniformly in phi.
CONDITIONAL ON IsBuchstab only. -/
theorem I1_integral_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp φ : ℝ}
    (hs : (5/2 : ℝ) ≤ s) (hs3 : s ≤ 3) (hsp : 0 < sp) (hφ : 2 ≤ φ) :
    buchstabIntegral ω 1 (fun _ => 1/sp) (fun _ => 1/s) φ ≤
      (5671433/10000000 : ℝ) * reciprocalIntegral s sp -
      (11433/10000000 : ℝ) * reciprocalIntegral 3 sp := by
  let D := domain (fun _ : Fin 3 => 1/sp) (fun _ => 1/s)
  let E := domain (fun _ : Fin 3 => 1/sp) (fun _ => 1/(3 : ℝ))
  have hD : MeasurableSet D := (domain_isCompact _ _).measurableSet
  have hE : MeasurableSet E := (domain_isCompact _ _).measurableSet
  have hsub : E ⊆ D := by
    intro x hx
    refine ⟨hx.1, fun j => ⟨(hx.2 j).1, (hx.2 j).2.trans ?_⟩⟩
    exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < s) hs3
  have hg : Integrable (E.indicator reciprocal) volume :=
    (integrable_indicator_iff hE).mpr (reciprocal_integrable hsp)
  have hgD := hg.integrableOn (s := D)
  have hi := I1_integrable hω hs hsp hφ
  have hk := (reciprocal_integrable (s := s) hsp).const_mul (5671433/10000000 : ℝ)
  have hm := setIntegral_mono_on (hi.add (hgD.const_mul (11433/10000000 : ℝ))) hk hD (fun x hx => by
    dsimp only [Pi.add_apply]
    have hp := denominator_pos hsp hx
    by_cases he : x ∈ E
    · rw [indicator_of_mem he]
      have hw := Wu04Buchstab.buchstab_le_566 hω (I1_argument_ge_three hsp hφ he)
      have hd := div_le_div_of_nonneg_right hw hp.le
      dsimp [reciprocal]
      calc _ ≤ (566/1000 : ℝ) / ((∏ j, x j) * x 1) + (11433/10000000 : ℝ) * (1 / ((∏ j, x j) * x 1)) := add_le_add hd le_rfl
           _ = _ := by ring
    · rw [indicator_of_notMem he]
      have hw := Wu04Buchstab.buchstab_le_5671433 hω (Wu04Functional.I1_argument_ge_two hs hsp hφ hx)
      have hd := div_le_div_of_nonneg_right hw hp.le
      simpa only [reciprocal, mul_zero, add_zero, mul_one_div] using hd)
  dsimp only [Pi.add_apply] at hm
  rw [MeasureTheory.integral_add hi (hgD.const_mul (11433/10000000 : ℝ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    setIntegral_indicator hE] at hm
  have hinter : (domain (fun _ : Fin 3 => 1/sp) (fun _ => 1/s)) ∩ E = E :=
    Set.inter_eq_right.mpr hsub
  rw [hinter] at hm
  change buchstabIntegral ω 1 (fun _ => 1/sp) (fun _ => 1/s) φ +
    (11433/10000000 : ℝ) * reciprocalIntegral 3 sp ≤
    (5671433/10000000 : ℝ) * reciprocalIntegral s sp at hm
  linarith

/-- The supremum has the same saving, CONDITIONAL ON IsBuchstab only. -/
theorem I1_le_tail {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s sp : ℝ}
    (hs : (5/2 : ℝ) ≤ s) (hs3 : s ≤ 3) (hsp : 0 < sp) :
    I1 ω s sp ≤ (5671433/10000000 : ℝ) * reciprocalIntegral s sp -
      (11433/10000000 : ℝ) * reciprocalIntegral 3 sp := by
  apply csSup_le
  · exact ⟨buchstabIntegral ω 1 (fun _ => 1/sp) (fun _ => 1/s) 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, hφ, rfl⟩
    exact I1_integral_tail hω hs hs3 hsp hφ

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_argument_ge_three
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_integral_tail
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.I1_le_tail
