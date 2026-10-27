import LeanLab.ChenDoubleSieve.I1Bounds

/-!
# The Fubini reduction of Wu's reciprocal I1 kernel

Source: https://arxiv.org/pdf/0705.1652, page 22, Lemma 5.1.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04I1
open Wu04Functional (domain)

/-- Integrate the middle coordinate first in three dimensional Euclidean space. -/
theorem integral_middle (f : (Fin 3 → ℝ) → ℝ) (hf : Integrable f volume) :
    (∫ x : Fin 3 → ℝ, f x) =
      ∫ u : ℝ, ∫ x : Fin 2 → ℝ, f ![x 0, u, x 1] := by
  let e : ℝ × (Fin 2 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (1 : Fin 3)).symm
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (1 : Fin 3)).symm _
  have hi : Integrable (fun p => f (e p)) volume :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr hf
  rw [← hem.integral_comp' f]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  congr 1
  ext j
  fin_cases j <;> simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth] <;> rfl

/-- Fixing the middle coordinate leaves a rectangular box. -/
theorem domain_middle {a b u : ℝ} (hu : u ∈ Icc a b) (x : Fin 2 → ℝ) :
    ![x 0, u, x 1] ∈ domain (fun _ => a) (fun _ => b) ↔ x ∈ Icc ![a, u] ![u, b] := by
  constructor
  · intro hx
    have hm0 := hx.1 (show (0 : Fin 3) ≤ 1 by decide)
    have hm1 := hx.1 (show (1 : Fin 3) ≤ 2 by decide)
    have hx0 := hx.2 0
    have hx2 := hx.2 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hm0 hm1 hx0 hx2
    constructor <;> intro j <;> fin_cases j <;> simp_all
  · rintro ⟨hlo, hhi⟩
    have h0 := hlo 0
    have h1 := hlo 1
    have h2 := hhi 0
    have h3 := hhi 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2 h3
    constructor
    · rw [Fin.monotone_iff_le_succ]
      intro j
      fin_cases j <;> simp_all
    · intro j
      fin_cases j <;> simp_all <;> linarith

/-- Integrating the two reciprocal coordinates gives the logarithmic factors. -/
theorem reciprocal_box {a b u : ℝ} (ha : 0 < a) (hu : u ∈ Icc a b) :
    (∫ x : Fin 2 → ℝ in Icc ![a, u] ![u, b], 1 / (x 0 * x 1 * u ^ 2)) =
      log (u / a) * log (b / u) / u ^ 2 := by
  have hu0 : 0 < u := ha.trans_le hu.1
  have hb0 : 0 < b := hu0.trans_le hu.2
  have hleft : (∫ v in Icc a u, (1 : ℝ) / v) = log (u / a) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1]
    simpa only [one_div, log_div hu0.ne' ha.ne'] using integral_inv_of_pos ha hu0
  have hright : (∫ v in Icc u b, (1 : ℝ) / v) = log (b / u) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.2]
    simpa only [one_div, log_div hb0.ne' hu0.ne'] using integral_inv_of_pos hu0 hb0
  have heq : (∫ x : Fin 2 → ℝ in Icc ![a, u] ![u, b], ∏ j, (1 : ℝ) / x j) =
      log (u / a) * log (b / u) := by
    rw [← pi_univ_Icc]
    change (∫ x, ∏ j, (1 : ℝ) / x j ∂(Measure.pi (fun _ : Fin 2 => volume)).restrict
      (Set.univ.pi (fun j : Fin 2 => Icc (![a, u] j) (![u, b] j)))) = _
    rw [Measure.restrict_pi_pi, integral_fin_nat_prod_eq_prod]
    simpa [Fin.prod_univ_succ] using congrArg₂ (· * ·) hleft hright
  have hfun : (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1 * u ^ 2)) =
      fun x => (1 / u ^ 2) * ∏ j, (1 : ℝ) / x j := by
    funext x
    simp [Fin.prod_univ_succ, one_div]
  rw [hfun, MeasureTheory.integral_const_mul, heq]
  ring

/-- The exact three dimensional reciprocal kernel equals the reduced scalar integral. -/
theorem reciprocal_reduction {s sp : ℝ} (hs : 0 < s) (hssp : s ≤ sp) :
    ReciprocalReduction s sp := by
  have hsp : 0 < sp := hs.trans_le hssp
  let a : ℝ := 1 / sp
  let b : ℝ := 1 / s
  let D : Set (Fin 3 → ℝ) := domain (fun _ => a) (fun _ => b)
  have ha : 0 < a := one_div_pos.mpr hsp
  have hab : a ≤ b := one_div_le_one_div_of_le hs hssp
  have hD : MeasurableSet D := (domain_isCompact _ _).measurableSet
  have hf : Integrable (D.indicator reciprocal) volume :=
    (integrable_indicator_iff hD).mpr (reciprocal_integrable hsp)
  have hm := integral_middle (D.indicator reciprocal) hf
  rw [MeasureTheory.integral_indicator hD] at hm
  have hinner (u : ℝ) : (∫ x : Fin 2 → ℝ, D.indicator reciprocal ![x 0, u, x 1]) =
      (Icc a b).indicator (fun u => log (u / a) * log (b / u) / u ^ 2) u := by
    by_cases hu : u ∈ Icc a b
    · have heq : (fun x : Fin 2 → ℝ => D.indicator reciprocal ![x 0, u, x 1]) =
          (Icc ![a, u] ![u, b]).indicator (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1 * u ^ 2)) := by
        funext x
        have hx := domain_middle hu x
        by_cases hbox : x ∈ Icc ![a, u] ![u, b]
        · rw [indicator_of_mem (hx.mpr hbox), indicator_of_mem hbox]
          simp only [reciprocal, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Fin.prod_univ_zero, mul_one]
          norm_num
          ring
        · rw [indicator_of_notMem (fun hd => hbox (hx.mp hd)), indicator_of_notMem hbox]
      rw [heq, MeasureTheory.integral_indicator measurableSet_Icc, reciprocal_box ha hu, indicator_of_mem hu]
    · have hz : ∀ x : Fin 2 → ℝ, D.indicator reciprocal ![x 0, u, x 1] = 0 := by
        intro x
        apply indicator_of_notMem
        intro hx
        apply hu
        simpa using hx.2 1
      simp only [hz, MeasureTheory.integral_zero, indicator_of_notMem hu]
  simp_rw [hinner] at hm
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab] at hm
  exact hm

end LeanLab.ChenDoubleSieve.Wu04I1

#print axioms LeanLab.ChenDoubleSieve.Wu04I1.integral_middle
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.domain_middle
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.reciprocal_box
#print axioms LeanLab.ChenDoubleSieve.Wu04I1.reciprocal_reduction
