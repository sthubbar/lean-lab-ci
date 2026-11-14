import LeanLab.ChenDoubleSieve.Burst9Psi2Panels
import LeanLab.ChenDoubleSieve.BuchstabTail

/-!
Finite box covers for Wu 2004 Lemma 5.2, page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- A finite box cover bounds an integral by the sum of the box volumes times their
nonnegative pointwise bounds. Wu 2004 page 26, derived quadrature tool. -/
theorem integral_le_box_cover {d : ℕ} {ι : Type*} (s : Finset ι)
    (D : Set (Fin d → ℝ)) (hD : MeasurableSet D)
    (f : (Fin d → ℝ) → ℝ) (lo hi : ι → Fin d → ℝ) (C : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i) (hle : ∀ i ∈ s, ∀ j, lo i j ≤ hi i j)
    (hcover : ∀ x ∈ D, ∃ i ∈ s, x ∈ Icc (lo i) (hi i) ∧ f x ≤ C i) :
    (∫ x in D, f x) ≤ ∑ i ∈ s, C i * ∏ j, (hi i j - lo i j) := by
  let g : ι → (Fin d → ℝ) → ℝ := fun i => (Icc (lo i) (hi i)).indicator (fun _ => C i)
  have hgi (i : ι) : Integrable (g i) volume := by
    exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hg0 (i : ι) (hi' : i ∈ s) (x : Fin d → ℝ) : 0 ≤ g i x := by
    exact indicator_nonneg (fun _ _ => hC i hi') _
  have hgs : Integrable (fun x => ∑ i ∈ s, g i x) volume :=
    integrable_finsetSum _ (fun i _ => hgi i)
  have hnonneg : ∀ x, 0 ≤ ∑ i ∈ s, g i x :=
    fun x => sum_nonneg fun i hi' => hg0 i hi' x
  have hpoint : ∀ x ∈ D, f x ≤ ∑ i ∈ s, g i x := by
    intro x hx
    obtain ⟨i, hi', hbox, hf⟩ := hcover x hx
    calc f x ≤ C i := hf
      _ = g i x := by simp only [g, indicator_of_mem hbox]
      _ ≤ ∑ i ∈ s, g i x := single_le_sum (fun j hj => hg0 j hj x) hi'
  have hval (i : ι) (hi' : i ∈ s) :
      (∫ x, g i x) = C i * ∏ j, (hi i j - lo i j) := by
    rw [show g i = (Icc (lo i) (hi i)).indicator (fun _ => C i) from rfl,
      integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul]
    have hv : volume.real (Icc (lo i) (hi i)) = ∏ j, (hi i j - lo i j) := by
      rw [Measure.real, Real.volume_Icc_pi, ENNReal.toReal_prod]
      exact prod_congr rfl fun j _ => ENNReal.toReal_ofReal (sub_nonneg.mpr (hle i hi' j))
    rw [hv, mul_comm]
  by_cases hfi : IntegrableOn f D volume
  · calc (∫ x in D, f x) ≤ ∫ x in D, ∑ i ∈ s, g i x :=
          setIntegral_mono_on hfi hgs.integrableOn hD hpoint
      _ ≤ ∫ x, ∑ i ∈ s, g i x :=
          setIntegral_le_integral hgs (Filter.Eventually.of_forall hnonneg)
      _ = ∑ i ∈ s, C i * ∏ j, (hi i j - lo i j) := by
          rw [integral_finsetSum _ (fun i _ => hgi i)]
          exact sum_congr rfl hval
  · rw [integral_undef hfi]
    exact sum_nonneg fun i hi' => mul_nonneg (hC i hi')
      (prod_nonneg fun j _ => sub_nonneg.mpr (hle i hi' j))


/-- Corner bounds certify a lower bound for the Buchstab argument on a box and on a
phi interval. Wu 2004 page 26, derived interval arithmetic. -/
theorem argument_ge_of_box {d : ℕ} (k : Fin d) {lo hi x : Fin d → ℝ}
    {a P φ : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc lo hi) (hxk : 0 < x k)
    (hφ : P ≤ φ) (hcorner : a * hi k + ∑ j, hi j ≤ P) :
    a ≤ (φ - ∑ j, x j) / x k := by
  rw [le_div_iff₀ hxk]
  have hs : ∑ j, x j ≤ ∑ j, hi j := sum_le_sum fun j _ => hx.2 j
  have hm := mul_le_mul_of_nonneg_left (hx.2 k) ha
  linarith

/-- Corner bounds also certify an upper argument bound on a compact phi interval.
Wu 2004 page 26, derived interval arithmetic. -/
theorem argument_le_of_box {d : ℕ} (k : Fin d) {lo hi x : Fin d → ℝ}
    {b P φ : ℝ} (hb : 0 ≤ b) (hx : x ∈ Icc lo hi) (hxk : 0 < x k)
    (hφ : φ ≤ P) (hcorner : P ≤ b * lo k + ∑ j, lo j) :
    (φ - ∑ j, x j) / x k ≤ b := by
  rw [div_le_iff₀ hxk]
  have hs : ∑ j, lo j ≤ ∑ j, x j := sum_le_sum fun j _ => hx.1 j
  have hm := mul_le_mul_of_nonneg_left (hx.1 k) hb
  linarith

/-- An argument lower bound combines the exact initial formula with the proved global
Buchstab enclosure. Wu 2004 Lemma 2.10 page 9, used in Lemma 5.2 page 26. -/
theorem buchstab_le_from_lower {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    (hz : ZeroBelowOne ω) {a u : ℝ} (ha : 0 < a) (hu : a ≤ u) :
    ω u ≤ max (1 / a) (5671433 / 10000000 : ℝ) := by
  by_cases hu1 : u < 1
  · rw [hz u hu1]
    exact (one_div_pos.mpr ha).le.trans (le_max_left _ _)
  · by_cases hu2 : u ≤ 2
    · rw [hω.2.1 u (le_of_not_gt hu1) hu2]
      exact (one_div_le_one_div_of_le ha hu).trans (le_max_left _ _)
    · exact (Wu04Buchstab.buchstab_le_5671433 hω (le_of_not_ge hu2)).trans
        (le_max_right _ _)

/-- A box enclosure for a Buchstab kernel with a local nonnegative cap on omega.
Wu 2004 page 26, all dimensions in the I2 family. -/
theorem kernel_le_on_box {ω : ℝ → ℝ} {n : ℕ} (lo hi x : Fin (n + 2) → ℝ)
    {φ C : ℝ} (hlo : ∀ j, 0 < lo j) (hx : x ∈ Icc lo hi) (hC : 0 ≤ C)
    (hωC : ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) ≤ C) :
    ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩) ≤
      C / ((∏ j, lo j) * lo ⟨n, by omega⟩) := by
  have hP : 0 < (∏ j, lo j) * lo ⟨n, by omega⟩ :=
    mul_pos (prod_pos fun j _ => hlo j) (hlo _)
  have hD : (∏ j, lo j) * lo ⟨n, by omega⟩ ≤ (∏ j, x j) * x ⟨n, by omega⟩ :=
    mul_le_mul (prod_le_prod₀ (fun j _ => (hlo j).le) (fun j _ => hx.1 j)) (hx.1 _)
      (hlo _).le (prod_nonneg fun j _ => (hlo j).le.trans (hx.1 j))
  exact (div_le_div_of_nonneg_right hωC (hP.trans_le hD).le).trans
    (div_le_div_of_nonneg_left hC hP hD)

/-- A finite covering certificate gives a bound uniform in phi, hence a bound for the
supremum in Wu 2004 page 26. Overlapping boxes are allowed. -/
theorem buchstabSup_le_box_cover {ω : ℝ → ℝ} {n : ℕ} {ι : Type*} (s : Finset ι)
    (lo hi : Fin (n + 2) → ℝ) (L H : ι → Fin (n + 2) → ℝ) (C : ι → ℝ)
    (hL : ∀ i ∈ s, ∀ j, 0 < L i j)
    (hle : ∀ i ∈ s, ∀ j, L i j ≤ H i j) (hC : ∀ i ∈ s, 0 ≤ C i)
    (hcover : ∀ x ∈ domain lo hi, ∃ i ∈ s, x ∈ Icc (L i) (H i))
    (hcap : ∀ φ : ℝ, 2 ≤ φ → ∀ i ∈ s, ∀ x ∈ domain lo hi,
      x ∈ Icc (L i) (H i) → ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) ≤ C i) :
    buchstabSup ω n lo hi ≤
      ∑ i ∈ s, C i / ((∏ j, L i j) * L i ⟨n, by omega⟩) * ∏ j, (H i j - L i j) := by
  apply csSup_le
  · exact ⟨buchstabIntegral ω n lo hi 2, 2, le_rfl, rfl⟩
  · rintro v ⟨φ, hφ, rfl⟩
    unfold buchstabIntegral
    have hcoef (i : ι) (hi' : i ∈ s) :
        0 ≤ C i / ((∏ j, L i j) * L i ⟨n, by omega⟩) :=
      div_nonneg (hC i hi')
        (mul_pos (prod_pos fun j _ => hL i hi' j) (hL i hi' _)).le
    apply integral_le_box_cover s (domain lo hi) (Wu04I1.domain_isCompact _ _).measurableSet
      _ L H _ hcoef hle
    intro x hx
    obtain ⟨i, hi', hbox⟩ := hcover x hx
    exact ⟨i, hi', hbox, kernel_le_on_box (L i) (H i) x (hL i hi') hbox
      (hC i hi') (hcap φ hφ i hi' x hx hbox)⟩

/-- The smallest four dimensional row has no arguments below one.
Wu 2004 page 26, D2,16 for Table 1 row four on page 30. -/
theorem r3_16_argument_ge_one {φ : ℝ} (hφ : 2 ≤ φ) {x : Fin 4 → ℝ}
    (hx : x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :
    1 ≤ (φ - ∑ j, x j) / x 2 := by
  apply argument_ge_of_box (2 : Fin 4) (lo := fun _ => (100 / 291 : ℝ))
    (hi := fun _ => (2 / 5 : ℝ)) (P := 2) (by norm_num)
    ⟨fun j => (hx.2 j).1, fun j => (hx.2 j).2⟩
    (lt_of_lt_of_le (by norm_num) (hx.2 2).1) hφ
  norm_num [Fin.sum_univ_succ]

/-- The row four D2,16 integrand is integrable for every phi at least two.
Wu 2004 page 26, continuity suffices since the argument is at least one. -/
theorem r3_16_integrable {ω : ℝ → ℝ} (hω : IsBuchstab ω) {φ : ℝ} (hφ : 2 ≤ φ) :
    IntegrableOn (fun x : Fin 4 → ℝ =>
      ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2))
      (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) volume := by
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  have hpos : ∀ x ∈ domain (fun _ => (100 / 291 : ℝ)) (fun _ : Fin 4 => (2 / 5 : ℝ)),
      ∀ j, 0 < x j := by
    intro x hx j
    exact lt_of_lt_of_le (by norm_num) (hx.2 j).1
  have harg : ContinuousOn (fun x : Fin 4 → ℝ => (φ - ∑ j, x j) / x 2)
      (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => (hpos x hx 2).ne')
  have hc : ContinuousOn (fun x : Fin 4 → ℝ => ω ((φ - ∑ j, x j) / x 2))
      (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) := by
    apply hω.1.comp harg
    intro x hx
    exact r3_16_argument_ge_one hφ hx
  apply hc.div (by fun_prop)
  intro x hx
  exact (mul_pos (prod_pos fun j _ => hpos x hx j) (hpos x hx 2)).ne'

/-- A concrete unit box instantiates the finite cover tool.
Wu 2004 page 26, derived quadrature sanity instance. -/
theorem box_cover_instance :
    (∫ x in Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => (1 : ℝ)), (1 : ℝ)) ≤ 1 := by
  have h := integral_le_box_cover ({()} : Finset Unit)
    (Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => (1 : ℝ))) measurableSet_Icc
    (fun _ => (1 : ℝ)) (fun _ _ => 0) (fun _ _ => 1) (fun _ => 1)
    (by intros; norm_num) (by intros; norm_num)
    (by intro x hx; exact ⟨(), by simp, hx, le_rfl⟩)
  simpa using h

/-- Both spatial pieces contain points in the interior of the original parameter range.
Wu 2004 page 26, D2,16 at Table 1 row four page 30. -/
theorem r3_16_split_witnesses :
    (fun _ : Fin 4 => (9 / 25 : ℝ)) ∈
      (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) ∩
        {x : Fin 4 → ℝ | x 2 ≤ (541 / 1455 : ℝ)} ∧
    (fun _ : Fin 4 => (39 / 100 : ℝ)) ∈
      (domain (fun _ => (100 / 291 : ℝ)) (fun _ => (2 / 5 : ℝ))) \
        {x : Fin 4 → ℝ | x 2 ≤ (541 / 1455 : ℝ)} := by
  constructor
  · exact ⟨⟨monotone_const, by intro j; norm_num⟩, by norm_num⟩
  · exact ⟨⟨monotone_const, by intro j; norm_num⟩, by norm_num⟩

end LeanLab.ChenDoubleSieve.Task562
