import LeanLab.ChenDoubleSieve.Task562Boxes

/-!
Ordered chamber volumes for Wu 2004 Lemma 5.2, page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- Splitting off the first coordinate preserves product volume.
Wu 2004 page 26, derived Fubini tool for ordered chambers. -/
theorem integral_first {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ u : ℝ, ∫ x : Fin n → ℝ, f (Fin.cons u x) := by
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1))).symm
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).symm _
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
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero']

/-- A slice of an ordered chamber is an ordered chamber in one lower dimension.
Wu 2004 page 26, derived domain identity. -/
theorem domain_cons {n : ℕ} {a b u : ℝ} (hu : u ∈ Icc a b) (x : Fin n → ℝ) :
    Fin.cons u x ∈ domain (fun _ => a) (fun _ => b) ↔
      x ∈ domain (fun _ => u) (fun _ => b) := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      simpa using hx.1 (Fin.succ_le_succ_iff.mpr hij)
    · intro j
      have hlow := hx.1 (Fin.zero_le j.succ)
      have hhigh := (hx.2 j.succ).2
      simpa using And.intro hlow hhigh
  · intro hx
    constructor
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact le_rfl
        · exact (hx.2 j).1
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact False.elim (by simpa using hij)
        · exact hx.1 (Fin.succ_le_succ_iff.mp hij)
    · intro j
      refine Fin.cases hu (fun j => ?_) j
      exact ⟨hu.1.trans (hx.2 j).1, (hx.2 j).2⟩

/-- The integral of one on the ordered n dimensional chamber is the box volume divided
by n factorial. Wu 2004 page 26, derived exact chamber volume. -/
theorem ordered_const_integral (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin n => a) (fun _ => b), (1 : ℝ)) =
      (b - a) ^ n / n.factorial := by
  induction n generalizing a b with
  | zero =>
    have he : domain (fun _ : Fin 0 => a) (fun _ => b) =
        Icc (fun _ => a) (fun _ => b) := by
      ext x
      simp [domain, Monotone]
    rw [he, setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc_pi]
    simp
  | succ n ih =>
    let D := domain (fun _ : Fin (n + 1) => a) (fun _ => b)
    have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
    have hf : Integrable (D.indicator (fun _ => (1 : ℝ))) volume :=
      (integrableOn_const (Wu04I1.domain_isCompact _ _).measure_lt_top.ne).integrable_indicator hD
    have hm := integral_first (D.indicator (fun _ => (1 : ℝ))) hf
    rw [MeasureTheory.integral_indicator hD] at hm
    have hinner (u : ℝ) : (∫ x : Fin n → ℝ, D.indicator (fun _ => (1 : ℝ)) (Fin.cons u x)) =
        (Icc a b).indicator (fun u => (b - u) ^ n / n.factorial) u := by
      by_cases hu : u ∈ Icc a b
      · have heq : (fun x : Fin n → ℝ => D.indicator (fun _ => (1 : ℝ)) (Fin.cons u x)) =
            (domain (fun _ : Fin n => u) (fun _ => b)).indicator (fun _ => (1 : ℝ)) := by
          funext x
          by_cases hx : x ∈ domain (fun _ : Fin n => u) (fun _ => b)
          · rw [indicator_of_mem ((domain_cons hu x).mpr hx), indicator_of_mem hx]
          · rw [indicator_of_notMem (fun h => hx ((domain_cons hu x).mp h)),
              indicator_of_notMem hx]
        rw [heq, MeasureTheory.integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
          ih hu.2, indicator_of_mem hu]
      · have hz (x : Fin n → ℝ) : D.indicator (fun _ => (1 : ℝ)) (Fin.cons u x) = 0 := by
          apply indicator_of_notMem
          intro hx
          exact hu (by simpa using hx.2 0)
        simp only [hz, integral_zero, indicator_of_notMem hu]
    simp_rw [hinner] at hm
    rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab] at hm
    change (∫ x in D, (1 : ℝ)) = _
    rw [hm, intervalIntegral.integral_div]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) b]
    rw [integral_pow]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

/-- The ordered chamber has one over n factorial of the volume of its surrounding cube.
Wu 2004 page 26, derived exact volume for quadrature cells. -/
theorem ordered_volume (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    volume.real (domain (fun _ : Fin n => a) (fun _ => b)) =
      (b - a) ^ n / n.factorial := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using ordered_const_integral n hab

/-- The ordered unit chamber in four dimensions has positive volume one over twenty four.
Wu 2004 page 26, D2,16 geometry sanity instance. -/
theorem ordered_volume_four_instance :
    volume.real (domain (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (1 : ℝ))) = 1 / 24 := by
  norm_num [ordered_volume 4 (by norm_num : (0 : ℝ) ≤ 1)]

/-- Even the ordered-volume correction does not make the single-box cap-one bound
small enough for I2_r3_16. This is a limitation of that bound, not a negation of the leaf.
Wu 2004 page 26, D2,16 and Table 1 row four page 30. -/
theorem ordered_single_box_r3_16_too_weak :
    (1 / (100 / 291 : ℝ) ^ 5) * (((2 / 5 : ℝ) - 100 / 291) ^ 4 / 24) >
      (21601 / 500000000 : ℝ) := by
  norm_num

/-- Even the smaller tail cap with the single-box lower denominator is too weak.
Wu 2004 page 26, derived negative certificate for this quadrature route alone. -/
theorem tail_single_box_r3_16_too_weak :
    ((566 / 1000 : ℝ) / (100 / 291 : ℝ) ^ 5) *
      (((2 / 5 : ℝ) - 100 / 291) ^ 4 / 24) > (21601 / 500000000 : ℝ) := by
  norm_num

end LeanLab.ChenDoubleSieve.Task562
