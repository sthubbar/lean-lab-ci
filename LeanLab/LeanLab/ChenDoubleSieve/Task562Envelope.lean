import LeanLab.ChenDoubleSieve.Task562Volume

/-!
A rational kernel and a small corner error for Wu 2004 Lemma 5.2, page 26, D2,16.
Source: https://arxiv.org/pdf/0705.1652, Table 1 row four page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- The exact rational kernel at phi two in D2,16 of row four.
Wu 2004 page 26, using the initial formula of Lemma 2.10 page 9. -/
def r3Base (x : Fin 4 → ℝ) : ℝ := 1 / ((∏ j, x j) * (2 - ∑ j, x j))

/-- The remaining mass parameter stays positive on the full row four domain.
Wu 2004 page 26, derived endpoint bound. -/
theorem r3_sum_gap_pos {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    0 < 2 - ∑ j, x j := by
  have hs : ∑ j, x j ≤ ∑ _ : Fin 4, (2 / 5 : ℝ) :=
    sum_le_sum fun j _ => (hx.2 j).2
  norm_num at hs
  linarith

/-- At phi two the initial Buchstab argument is at most 91/50.
Wu 2004 pages 9 and 26, derived corner bound. -/
theorem r3_argument_two_upper {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    (2 - ∑ j, x j) / x 2 ≤ (91 / 50 : ℝ) := by
  apply argument_le_of_box (2 : Fin 4) (lo := fun _ => (100 / 291 : ℝ))
    (hi := fun _ => (2 / 5 : ℝ)) (P := 2) (by norm_num)
    ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩
    (lt_of_lt_of_le (by norm_num) (hx.2 2).1) le_rfl
  norm_num [Fin.sum_univ_succ]

/-- The rational kernel is integrable on the full ordered domain.
Wu 2004 page 26, derived compact-domain fact. -/
theorem r3Base_integrable : IntegrableOn r3Base
    (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro x hx
  exact (mul_pos (prod_pos fun j _ => lt_of_lt_of_le (by norm_num) (hx.2 j).1)
    (r3_sum_gap_pos hx)).ne'

/-- The Buchstab kernel at phi two equals the rational kernel everywhere on this domain.
Wu 2004 pages 9 and 26, with no quadrature input. -/
theorem r3_kernel_two {ω : ℝ → ℝ} (hω : IsBuchstab ω) {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    ω ((2 - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) = r3Base x := by
  have hx2 : 0 < x 2 := lt_of_lt_of_le (by norm_num) (hx.2 2).1
  have hprod : 0 < ∏ j, x j := prod_pos fun j _ => lt_of_lt_of_le (by norm_num) (hx.2 j).1
  rw [hω.2.1 _ (r3_16_argument_ge_one le_rfl hx)
    ((r3_argument_two_upper hx).trans (by norm_num))]
  unfold r3Base
  field_simp [hx2.ne', hprod.ne', (r3_sum_gap_pos hx).ne']

/-- Any excess of the uniform Buchstab envelope over the phi two value is supported
in the small chamber whose coordinates are at most 227/625.
Wu 2004 pages 9 and 26, derived envelope localization. -/
theorem r3_omega_envelope {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    ω ((φ - ∑ j, x j) / x 2) ≤ 1 / ((2 - ∑ j, x j) / x 2) +
      (domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (227 / 625 : ℝ))).indicator
        (fun _ => (5671433 / 10000000 : ℝ) - 50 / 91) x := by
  have hx2 : 0 < x 2 := lt_of_lt_of_le (by norm_num) (hx.2 2).1
  have hu0 : 0 < (2 - ∑ j, x j) / x 2 := div_pos (r3_sum_gap_pos hx) hx2
  have huφ : (2 - ∑ j, x j) / x 2 ≤ (φ - ∑ j, x j) / x 2 :=
    div_le_div_of_nonneg_right (by linarith) hx2.le
  have hw := buchstab_le_from_lower hω hz hu0 huφ
  have hr : (50 / 91 : ℝ) ≤ 1 / ((2 - ∑ j, x j) / x 2) := by
    have hh := one_div_le_one_div_of_le hu0 (r3_argument_two_upper hx)
    norm_num at hh
    simpa only [one_div_div] using hh
  by_cases he : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (227 / 625 : ℝ))
  · rw [indicator_of_mem he]
    apply hw.trans
    apply max_le <;> linarith
  · rw [indicator_of_notMem he, add_zero]
    have hx3 : (227 / 625 : ℝ) < x 3 := by
      by_contra hn
      apply he
      refine ⟨hx.1, fun j => ⟨(hx.2 j).1, ?_⟩⟩
      exact (hx.1 (show j ≤ 3 by omega)).trans (le_of_not_gt hn)
    have hs : (3 * (100 / 291 : ℝ)) + 227 / 625 ≤ ∑ j, x j := by
      have h0 := (hx.2 0).1
      have h1 := (hx.2 1).1
      have h2 := (hx.2 2).1
      simp only [Fin.sum_univ_succ] at *
      norm_num at *
      linarith
    have hcorn : (5671433 / 10000000 : ℝ) * (2 - ∑ j, x j) ≤ x 2 := by
      have h2 := (hx.2 2).1
      nlinarith
    have hc : (5671433 / 10000000 : ℝ) ≤ 1 / ((2 - ∑ j, x j) / x 2) := by
      rw [le_div_iff₀ hu0]
      rw [← mul_div_assoc, div_le_iff₀ hx2]
      simpa using hcorn
    exact hw.trans (max_le le_rfl hc)

/-- The localized error in the full kernel has one rational constant cap.
Wu 2004 pages 9 and 26, derived pointwise envelope. -/
theorem r3_kernel_envelope {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2) ≤ r3Base x +
      (domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (227 / 625 : ℝ))).indicator
        (fun _ => ((5671433 / 10000000 : ℝ) - 50 / 91) / (100 / 291 : ℝ) ^ 5) x := by
  have hxpos (j : Fin 4) : 0 < x j := lt_of_lt_of_le (by norm_num) (hx.2 j).1
  have hp : 0 < ∏ j, x j := prod_pos fun j _ => hxpos j
  have hd : 0 < (∏ j, x j) * x 2 := mul_pos hp (hxpos 2)
  have hprod : (100 / 291 : ℝ) ^ 4 ≤ ∏ j, x j := by
    have hh := prod_le_prod₀ (s := (univ : Finset (Fin 4)))
      (f := fun _ => (100 / 291 : ℝ)) (g := x) (by intros; norm_num)
      (fun j _ => (hx.2 j).1)
    norm_num at hh ⊢
    exact hh
  have hdlo : (100 / 291 : ℝ) ^ 5 ≤ (∏ j, x j) * x 2 := by
    calc (100 / 291 : ℝ) ^ 5 = (100 / 291 : ℝ) ^ 4 * (100 / 291 : ℝ) := by ring
      _ ≤ (∏ j, x j) * x 2 := mul_le_mul hprod (hx.2 2).1 (by norm_num) hp.le
  have hcancel : (1 / ((2 - ∑ j, x j) / x 2)) / ((∏ j, x j) * x 2) = r3Base x := by
    unfold r3Base
    field_simp [(hxpos 2).ne', hp.ne', (r3_sum_gap_pos hx).ne']
  have hw := r3_omega_envelope hω hz hφ hx
  by_cases he : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (227 / 625 : ℝ))
  · rw [indicator_of_mem he] at hw ⊢
    calc _ ≤ (1 / ((2 - ∑ j, x j) / x 2) +
        ((5671433 / 10000000 : ℝ) - 50 / 91)) / ((∏ j, x j) * x 2) :=
          div_le_div_of_nonneg_right hw hd.le
      _ = r3Base x + ((5671433 / 10000000 : ℝ) - 50 / 91) / ((∏ j, x j) * x 2) := by
          rw [add_div, hcancel]
      _ ≤ _ := by
          have hq : ((5671433 / 10000000 : ℝ) - 50 / 91) / ((∏ j, x j) * x 2) ≤
              ((5671433 / 10000000 : ℝ) - 50 / 91) / (100 / 291 : ℝ) ^ 5 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdlo
          exact add_le_add le_rfl hq
  · rw [indicator_of_notMem he, add_zero] at hw ⊢
    exact (div_le_div_of_nonneg_right hw hd.le).trans_eq hcancel

/-- The possible gain over the rational phi two kernel contributes less than
23/1000000000 to the entire integral, uniformly for phi at least two.
Wu 2004 page 26, D2,16, derived exact-volume error estimate. -/
theorem r3_integral_envelope {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) :
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)),
      ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)) ≤
    (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) +
      (23 / 1000000000 : ℝ) := by
  let D := domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))
  let E := domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (227 / 625 : ℝ))
  let c : ℝ := ((5671433 / 10000000 : ℝ) - 50 / 91) / (100 / 291 : ℝ) ^ 5
  have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
  have hE : MeasurableSet E := (Wu04I1.domain_isCompact _ _).measurableSet
  have hsub : E ⊆ D := by
    intro x hx
    exact ⟨hx.1, fun j => ⟨(hx.2 j).1, (hx.2 j).2.trans (by norm_num)⟩⟩
  have hg : Integrable (E.indicator (fun _ => c)) volume :=
    (integrableOn_const (Wu04I1.domain_isCompact _ _).measure_lt_top.ne).integrable_indicator hE
  have hm := setIntegral_mono_on (r3_16_integrable hω hφ)
    (r3Base_integrable.add hg.integrableOn) hD (fun x hx => r3_kernel_envelope hω hz hφ hx)
  simp only [Pi.add_apply] at hm
  rw [MeasureTheory.integral_add r3Base_integrable hg.integrableOn,
    setIntegral_indicator hE, inter_eq_right.mpr hsub, setIntegral_const, smul_eq_mul] at hm
  have hv : volume.real E = ((227 / 625 : ℝ) - 100 / 291) ^ 4 / 24 := by
    convert ordered_volume 4 (by norm_num : (100 / 291 : ℝ) ≤ 227 / 625) using 1 <;>
      norm_num [E, Nat.factorial]
  have hcert : volume.real E * c ≤ (23 / 1000000000 : ℝ) := by
    rw [hv]
    norm_num [c]
  linarith

/-- The original supremum is bounded by one rational integral plus the corner budget.
Wu 2004 page 26, D2,16 at Table 1 row four page 30. -/
theorem r3_sup_envelope {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 7 ≤
      (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) +
        (23 / 1000000000 : ℝ) := by
  have h : buchstabSup ω 2 (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)) ≤
      (∫ x in domain (fun _ : Fin 4 => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)), r3Base x) +
        (23 / 1000000000 : ℝ) := by
    apply csSup_le
    · exact ⟨buchstabIntegral ω 2 (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ)) 2,
        2, le_rfl, rfl⟩
    · rintro v ⟨φ, hφ, rfl⟩
      exact r3_integral_envelope hω hz hφ
  convert h using 1 <;> norm_num [I2, tableParams]

end LeanLab.ChenDoubleSieve.Task562
