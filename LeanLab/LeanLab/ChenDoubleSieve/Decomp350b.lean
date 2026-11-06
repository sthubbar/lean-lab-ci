import LeanLab.ChenDoubleSieve.Decomp350g

/-!
Supply for the sealed F13 leaf using a logarithmic numerical problem.
Source: https://arxiv.org/pdf/0705.1652, pages 41 and 42.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task350
open Task275 Wu04Functional

/-- The F13 integrand is dominated by the sharp constant majorant.
Source: page 41 equation 10.12 and page 42 use of Lemma 2.10.
CONDITIONAL ON the explicitly supplied pointwise bound. -/
theorem fourfold13_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    {c a b : ℝ} {weight : ℝ → ℝ}
    (hab : a ≤ b) (ha : kappa1 ≤ a) (hb : b ≤ kappa2)
    (hw : ContinuousOn weight (Icc kappa1 kappa2))
    (hwpos : ∀ t ∈ Icc kappa1 kappa2, 0 < weight t)
    (hc : ∀ u : ℝ, 7 / 2 ≤ u → ω u ≤ c) :
    fourfold ω (fun _ => kappa2) a b id weight ≤
      logMajorant c id (fun _ => kappa2) a b weight := by
  apply fourfold_le_logMajorant hω hab ha hb (by fun_prop) (by fun_prop) hw _ _ hwpos _ hc
  · intro t ht
    exact lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1
  · intro t ht
    exact ht.2
  · intro t1 ht1 t2 ht2 t3 ht3 t4 ht4
    convert fourfold13_argument t1 t2 t3 t4
      (by linarith [ht1.1, ht2.1, ha, show (0 : ℝ) < kappa1 by norm_num [kappa1]])
      (ht1.2.trans hb) ht2.2 ht3.2 ht4.2 using 1 <;> norm_num

/-- LEAF. Wu 2004 page 42 numerical display F13, after page 41 equation 10.12.
Both inner logarithmic integrals have been evaluated exactly.
The single elementary integrals are bounded by a ten term polynomial certificate. -/
theorem elementary_F13_upper :
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ),
      ((280761 / 1000000 : ℝ) *
        ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) /
          (t * (1 - t))) +
    8 * (∫ t in (1 / 10 : ℝ)..kappa2,
      ((280761 / 1000000 : ℝ) *
        ((log (kappa2 / t) ^ 2 - 2 * log (kappa2 / t) + 2) / t - 2 / kappa2)) / t)
      ≤ 0.023310 := by
  exact F13_elementary_upper_clean

/-- The threefold F13 quadrature follows from the one dimensional leaf.
The elementary numerical input has a clean proof. -/
theorem logarithmic_F13_upper :
    36 / 5 * logMajorant (280761 / 500000) id (fun _ => kappa2)
      kappa1 (1 / 10) (fun t => t * (1 - t)) +
    8 * logMajorant (280761 / 500000) id (fun _ => kappa2)
      (1 / 10) kappa2 id ≤ 0.023310 := by
  rw [logMajorant13_eq (by norm_num [kappa1]) le_rfl (by norm_num [kappa2]),
    logMajorant13_eq (by norm_num [kappa2]) (by norm_num [kappa1]) le_rfl]
  convert elementary_F13_upper using 1 <;> norm_num

/-- Exact supply for numerical_F13 from the proved sharp Buchstab tail
and the certified elementary quadrature. No OPEN input remains. -/
theorem numerical_F13_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    integralTerms F f ω 10 ≤ 0.023310 := by
  have hfirst := fourfold13_upper (ω := ω) hω
    (a := kappa1) (b := 1 / 10) (weight := fun t => t * (1 - t))
    (by norm_num [kappa1]) le_rfl (by norm_num [kappa2]) (by fun_prop)
    (by
      intro t ht
      apply mul_pos
      · exact lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1
      · norm_num [kappa2] at ht
        linarith [ht.2])
    (fun u hu => buchstab_tail_upper hω hu)
  have hsecond := fourfold13_upper (ω := ω) hω
    (a := 1 / 10) (b := kappa2) (weight := id)
    (by norm_num [kappa2]) (by norm_num [kappa1]) le_rfl (by fun_prop)
    (by
      intro t ht
      exact lt_of_lt_of_le (by norm_num [kappa1] : (0 : ℝ) < kappa1) ht.1)
    (fun u hu => buchstab_tail_upper hω hu)
  change 36 / 5 * fourfold ω (fun _ => kappa2) kappa1 (1 / 10) id
      (fun t => t * (1 - t)) +
    8 * fourfold ω (fun _ => kappa2) (1 / 10) kappa2 id id ≤ 0.023310
  linarith only [hfirst, hsecond, logarithmic_F13_upper]

end LeanLab.ChenDoubleSieve.Task350
