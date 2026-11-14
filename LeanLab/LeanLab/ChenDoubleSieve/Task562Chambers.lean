import LeanLab.ChenDoubleSieve.Task562Volume

/-!
Ordered cell covers for Wu 2004 Lemma 5.2, page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- A finite cover by ordered boxes uses the actual chamber volumes rather than the
surrounding rectangular volumes. Wu 2004 page 26, derived quadrature tool. -/
theorem integral_le_chamber_cover {d : ℕ} {ι : Type*} (s : Finset ι)
    (D : Set (Fin d → ℝ)) (hD : MeasurableSet D)
    (f : (Fin d → ℝ) → ℝ) (lo hi : ι → Fin d → ℝ) (C V : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hV : ∀ i ∈ s, volume.real (domain (lo i) (hi i)) ≤ V i)
    (hcover : ∀ x ∈ D, ∃ i ∈ s, x ∈ domain (lo i) (hi i) ∧ f x ≤ C i) :
    (∫ x in D, f x) ≤ ∑ i ∈ s, C i * V i := by
  let g : ι → (Fin d → ℝ) → ℝ := fun i => (domain (lo i) (hi i)).indicator (fun _ => C i)
  have hgi (i : ι) : Integrable (g i) volume :=
    (integrableOn_const (Wu04I1.domain_isCompact _ _).measure_lt_top.ne).integrable_indicator
      (Wu04I1.domain_isCompact _ _).measurableSet
  have hg0 (i : ι) (hi' : i ∈ s) (x : Fin d → ℝ) : 0 ≤ g i x :=
    indicator_nonneg (fun _ _ => hC i hi') _
  have hgs : Integrable (fun x => ∑ i ∈ s, g i x) volume :=
    integrable_finsetSum _ (fun i _ => hgi i)
  have hpoint : ∀ x ∈ D, f x ≤ ∑ i ∈ s, g i x := by
    intro x hx
    obtain ⟨i, hi', hbox, hf⟩ := hcover x hx
    calc f x ≤ C i := hf
      _ = g i x := by simp only [g, indicator_of_mem hbox]
      _ ≤ ∑ i ∈ s, g i x := single_le_sum (fun j hj => hg0 j hj x) hi'
  have hval (i : ι) (hi' : i ∈ s) : (∫ x, g i x) ≤ C i * V i := by
    change (∫ x, (domain (lo i) (hi i)).indicator (fun _ => C i) x) ≤ _
    rw [integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
      setIntegral_const, smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hV i hi') (hC i hi')
  by_cases hfi : IntegrableOn f D volume
  · calc (∫ x in D, f x) ≤ ∫ x in D, ∑ i ∈ s, g i x :=
          setIntegral_mono_on hfi hgs.integrableOn hD hpoint
      _ ≤ ∫ x, ∑ i ∈ s, g i x :=
          setIntegral_le_integral hgs (Filter.Eventually.of_forall
            (fun x => sum_nonneg fun i hi' => hg0 i hi' x))
      _ = ∑ i ∈ s, ∫ x, g i x := integral_finsetSum _ (fun i _ => hgi i)
      _ ≤ ∑ i ∈ s, C i * V i := sum_le_sum hval
  · rw [integral_undef hfi]
    exact sum_nonneg fun i hi' => mul_nonneg (hC i hi') ((measureReal_nonneg).trans (hV i hi'))

/-- Local Buchstab caps and certified chamber volumes give a bound on the full supremum.
Wu 2004 page 26, derived finite certificate rule. -/
theorem buchstabSup_le_chamber_cover {ω : ℝ → ℝ} {n : ℕ} {ι : Type*} (s : Finset ι)
    (lo hi : Fin (n + 2) → ℝ) (L H : ι → Fin (n + 2) → ℝ) (C V : ι → ℝ)
    (hL : ∀ i ∈ s, ∀ j, 0 < L i j) (hC : ∀ i ∈ s, 0 ≤ C i)
    (hV : ∀ i ∈ s, volume.real (domain (L i) (H i)) ≤ V i)
    (hcover : ∀ x ∈ domain lo hi, ∃ i ∈ s, x ∈ Icc (L i) (H i))
    (hcap : ∀ φ : ℝ, 2 ≤ φ → ∀ i ∈ s, ∀ x ∈ domain lo hi,
      x ∈ Icc (L i) (H i) → ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) ≤ C i) :
    buchstabSup ω n lo hi ≤
      ∑ i ∈ s, C i / ((∏ j, L i j) * L i ⟨n, by omega⟩) * V i := by
  have hcoef (i : ι) (hi' : i ∈ s) : 0 ≤ C i / ((∏ j, L i j) * L i ⟨n, by omega⟩) :=
    div_nonneg (hC i hi') (mul_pos (prod_pos fun j _ => hL i hi' j) (hL i hi' _)).le
  apply csSup_le
  · exact ⟨buchstabIntegral ω n lo hi 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, hφ, rfl⟩
    unfold buchstabIntegral
    apply integral_le_chamber_cover s (domain lo hi) (Wu04I1.domain_isCompact _ _).measurableSet
      _ L H _ V hcoef hV
    intro x hx
    obtain ⟨i, hi', hbox⟩ := hcover x hx
    exact ⟨i, hi', ⟨hx.1, fun j => ⟨hbox.1 j, hbox.2 j⟩⟩,
      kernel_le_on_box (L i) (H i) x (hL i hi') hbox (hC i hi') (hcap φ hφ i hi' x hx hbox)⟩

/-- The homogeneous ordered-box bound includes the exact factorial saving.
Wu 2004 page 26, especially D2,9 and D2,16. -/
theorem buchstabSup_le_ordered_box {ω : ℝ → ℝ} {n : ℕ} {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C)
    (hcap : ∀ φ : ℝ, 2 ≤ φ → ∀ x ∈ domain (fun _ : Fin (n + 2) => a) (fun _ => b),
      ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) ≤ C) :
    buchstabSup ω n (fun _ => a) (fun _ => b) ≤
      C / a ^ (n + 3) * ((b - a) ^ (n + 2) / (n + 2).factorial) := by
  have h := buchstabSup_le_chamber_cover ({()} : Finset Unit)
    (fun _ : Fin (n + 2) => a) (fun _ => b) (fun _ _ => a) (fun _ _ => b)
    (fun _ => C) (fun _ => (b - a) ^ (n + 2) / (n + 2).factorial)
    (by intros; exact ha) (by intros; exact hC)
    (by intros; exact (ordered_volume (n + 2) hab).le)
    (by intro x hx; exact ⟨(), by simp, fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩)
    (by intro φ hφ i hi' x hx hbox; exact hcap φ hφ x hx)
  simpa [pow_succ] using h

/-- A certified ordered single-box bound for the smallest open integral.
This improves the rectangular bound but remains above its original target.
Wu 2004 Lemma 5.2 page 26, D2,16 at Table 1 row four page 30. -/
theorem I2_r3_16_ordered_upper {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 7 ≤ (274098817 / 3125000000000 : ℝ) := by
  have h := buchstabSup_le_ordered_box (ω := ω) (n := 2)
    (a := (100 / 291 : ℝ)) (b := (2 / 5 : ℝ)) (C := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro φ hφ x hx; exact extended_buchstab_le_one hω hz _)
  norm_num at h
  convert h using 1 <;> norm_num [I2, tableParams]

end LeanLab.ChenDoubleSieve.Task562
