import LeanLab.ChenDoubleSieve.Decomp350h

/-!
Supply for the sealed F14 leaf using a logarithmic numerical problem.
Source: https://arxiv.org/pdf/0705.1652, pages 41 and 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task350
open Task275 Wu04Functional

/-- The F14 integrand is dominated by the sharp constant majorant.
Source: page 41 equation 10.12 and page 42 use of Lemma 2.10.
CONDITIONAL ON the explicitly supplied pointwise bound. -/
theorem fourfold14_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {c a b : ℝ} {weight : ℝ → ℝ}
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hw : ContinuousOn weight (Icc kappa1 kappa2))
    (hwpos : ∀ t ∈ Icc kappa1 kappa2, 0 < weight t)
    (hc : ∀ u : ℝ, 7 / 2 ≤ u → ω u ≤ c) :
    fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) a b (fun _ => kappa2) weight ≤
      logMajorant c (fun _ => kappa2) (fun t => 1 / 2 - 2 * kappa1 - t) a b weight := by
  apply fourfold_le_logMajorant hω hab ha hb (by fun_prop) (by fun_prop) hw _ _ hwpos _ hc
  · intro t ht
    norm_num [kappa2]
  · intro t ht
    norm_num [kappa1, kappa2] at *
    linarith
  · intro t1 ht1 t2 ht2 t3 ht3 t4 ht4
    convert fourfold14_argument t1 t2 t3 t4
      (by linarith [ht1.1, ht2.1, ha, show (0 : ℝ) < kappa1 by norm_num [kappa1]])
      (ht1.2.trans hb) ht2.2 ht4.2 using 1 <;> norm_num

/-- LEAF. Wu 2004 page 42 numerical display F14, after page 41 equation 10.12.
The fourth integral and the squared reciprocal middle coordinate are removed.
The two dimensional logarithmic quadrature has a positive polynomial enclosure. -/
theorem elementary_F14_upper :
    36 / 5 * twofoldMajorant (280761 / 500000) (fun _ => kappa2)
      (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10) (fun t => t * (1 - t)) +
    8 * twofoldMajorant (280761 / 500000) (fun _ => kappa2)
      (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2 id ≤ 0.182860 := by
  exact F14_elementary_upper_clean

/-- The threefold F14 quadrature follows from the two dimensional leaf.
The elementary quadrature is supplied by a clean rational polynomial proof. -/
theorem logarithmic_F14_upper :
    36 / 5 * logMajorant (280761 / 500000) (fun _ => kappa2) (fun t => 1 / 2 - 2 * kappa1 - t)
      kappa1 (1 / 10) (fun t => t * (1 - t)) +
    8 * logMajorant (280761 / 500000) (fun _ => kappa2) (fun t => 1 / 2 - 2 * kappa1 - t)
      (1 / 10) kappa2 id ≤ 0.182860 := by
  have hfirst := logMajorant_eq_twofold (c := (280761 / 500000 : ℝ))
    (lower := fun _ => kappa2) (last := fun t => 1 / 2 - 2 * kappa1 - t)
    (a := kappa1) (b := 1 / 10)
    (by norm_num [kappa1]) le_rfl (by norm_num [kappa2])
    (by fun_prop) (by fun_prop)
    (by intro t ht; norm_num [kappa2])
    (by intro t ht; norm_num [kappa1, kappa2] at ht ⊢; linarith [ht.2])
    (fun t => t * (1 - t))
  have hsecond := logMajorant_eq_twofold (c := (280761 / 500000 : ℝ))
    (lower := fun _ => kappa2) (last := fun t => 1 / 2 - 2 * kappa1 - t)
    (a := 1 / 10) (b := kappa2)
    (by norm_num [kappa2]) (by norm_num [kappa1]) le_rfl
    (by fun_prop) (by fun_prop)
    (by intro t ht; norm_num [kappa2])
    (by intro t ht; norm_num [kappa1, kappa2] at ht ⊢; linarith [ht.2]) id
  rw [hfirst, hsecond]
  exact elementary_F14_upper

/-- Exact supply for numerical_F14 from the proved sharp Buchstab tail
and the certified elementary quadrature. No OPEN input remains. -/
theorem numerical_F14_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 11 ≤ 0.182860 := by
  have hfirst := fourfold14_upper (ω := ω) hω
    (a := kappa1) (b := 1 / 10) (weight := fun t => t * (1 - t))
    (by norm_num [kappa1]) le_rfl (by norm_num [kappa2]) (by fun_prop)
    (by
      intro t ht
      apply mul_pos
      · exact lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1
      · norm_num [kappa2] at ht
        linarith [ht.2])
    (fun u hu => buchstab_tail_upper hω hu)
  have hsecond := fourfold14_upper (ω := ω) hω
    (a := 1 / 10) (b := kappa2) (weight := id)
    (by norm_num [kappa2]) (by norm_num [kappa1]) le_rfl (by fun_prop)
    (by
      intro t ht
      exact lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1)
    (fun u hu => buchstab_tail_upper hω hu)
  change 36 / 5 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10) (fun _ => kappa2)
      (fun t => t * (1 - t)) +
    8 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2 (fun _ => kappa2) id ≤ 0.182860
  linarith only [hfirst, hsecond, logarithmic_F14_upper]

end LeanLab.ChenDoubleSieve.Task350
