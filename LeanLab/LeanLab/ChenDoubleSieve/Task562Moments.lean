import LeanLab.ChenDoubleSieve.Task562Volume

/-!
Exact monomial integration on the ordered chambers in Wu 2004 Lemma 5.2, page 26.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task562
open Wu04Functional

/-- Product of successive partial degree sums plus their coordinate counts.
Wu 2004 page 26, derived exact monomial denominator for ordered integration. -/
def momentDenom : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 1
  | n + 1, k => momentDenom n (Fin.init k) * ((∑ j, k j) + n + 1)

/-- Every monomial moment denominator is positive.
Wu 2004 page 26, derived finite certificate arithmetic. -/
theorem momentDenom_pos (n : ℕ) (k : Fin n → ℕ) : 0 < momentDenom n k := by
  induction n with
  | zero => simp [momentDenom]
  | succ n ih =>
    exact Nat.mul_pos (ih (Fin.init k)) (by omega)

/-- Splitting off the last coordinate preserves product volume.
Wu 2004 page 26, derived Fubini tool for monomial moments. -/
theorem integral_last {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = ∫ u : ℝ, ∫ x : Fin n → ℝ, f (Fin.snoc x u) := by
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
  have hem : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm _
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
    Fin.insertNth_last']

/-- Fixing the last coordinate gives the smaller ordered chamber below it.
Wu 2004 page 26, derived slicing identity. -/
theorem domain_snoc {n : ℕ} {a b u : ℝ} (hu : u ∈ Icc a b) (x : Fin n → ℝ) :
    Fin.snoc x u ∈ domain (fun _ => a) (fun _ => b) ↔
      x ∈ domain (fun _ => a) (fun _ => u) := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      simpa using hx.1 (Fin.castSucc_le_castSucc_iff.mpr hij)
    · intro j
      have hlow := (hx.2 j.castSucc).1
      have hhigh := hx.1 (Fin.le_last j.castSucc)
      simpa using And.intro hlow hhigh
  · intro hx
    constructor
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simpa using hx.1 (Fin.castSucc_le_castSucc_iff.mp hij)
        · simpa using (hx.2 i).2
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact False.elim (by simpa using hij)
        · exact le_rfl
    · intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa using And.intro (hx.2 j).1 ((hx.2 j).2.trans hu.2)
      · simpa using hu

/-- The exact shifted monomial moment on an ordered chamber.
Wu 2004 page 26, derived polynomial quadrature rule. -/
theorem ordered_shifted_monomial (n : ℕ) (k : Fin n → ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin n => a) (fun _ => b), ∏ j, (x j - a) ^ k j) =
      (b - a) ^ ((∑ j, k j) + n) / momentDenom n k := by
  induction n generalizing a b with
  | zero => simpa [momentDenom] using ordered_const_integral 0 hab
  | succ n ih =>
    let D := domain (fun _ : Fin (n + 1) => a) (fun _ => b)
    have hD : MeasurableSet D := (Wu04I1.domain_isCompact _ _).measurableSet
    have hpoly : IntegrableOn (fun x : Fin (n + 1) → ℝ => ∏ j, (x j - a) ^ k j) D volume := by
      apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
      fun_prop
    have hf := hpoly.integrable_indicator hD
    have hm := integral_last (D.indicator (fun x => ∏ j, (x j - a) ^ k j)) hf
    rw [integral_indicator hD] at hm
    have hinner (u : ℝ) :
        (∫ x : Fin n → ℝ, D.indicator (fun x => ∏ j, (x j - a) ^ k j) (Fin.snoc x u)) =
        (Icc a b).indicator (fun u => (u - a) ^ ((∑ j : Fin (n + 1), k j) + n) /
          momentDenom n (Fin.init k)) u := by
      by_cases hu : u ∈ Icc a b
      · have heq : (fun x : Fin n → ℝ => D.indicator (fun x => ∏ j, (x j - a) ^ k j) (Fin.snoc x u)) =
            fun x => (domain (fun _ : Fin n => a) (fun _ => u)).indicator
              (fun x => ∏ j, (x j - a) ^ (Fin.init k) j) x * (u - a) ^ k (Fin.last n) := by
          funext x
          by_cases hx : x ∈ domain (fun _ : Fin n => a) (fun _ => u)
          · rw [indicator_of_mem ((domain_snoc hu x).mpr hx), indicator_of_mem hx]
            simp [Fin.prod_univ_castSucc, Fin.init]
          · rw [indicator_of_notMem (fun h => hx ((domain_snoc hu x).mp h)), indicator_of_notMem hx]
            simp
        rw [heq, MeasureTheory.integral_mul_const,
          integral_indicator (Wu04I1.domain_isCompact _ _).measurableSet,
          ih (Fin.init k) hu.1, indicator_of_mem hu]
        rw [div_mul_eq_mul_div, ← pow_add]
        congr 2
        rw [Fin.sum_univ_castSucc]
        simp [Fin.init]
        omega
      · have hz (x : Fin n → ℝ) : D.indicator (fun x => ∏ j, (x j - a) ^ k j) (Fin.snoc x u) = 0 := by
          apply indicator_of_notMem
          intro hx
          exact hu (by simpa using hx.2 (Fin.last n))
        simp only [hz, integral_zero, indicator_of_notMem hu]
    simp_rw [hinner] at hm
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab] at hm
    change (∫ x in D, ∏ j, (x j - a) ^ k j) = _
    rw [hm, intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ ((∑ j, k j) + n)) a,
      integral_pow]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero _), sub_zero, momentDenom,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [div_div]
    congr 1
    ring

/-- The product of four coordinates integrates to one over 384 on the ordered unit chamber.
Wu 2004 page 26, derived nonzero monomial moment instance. -/
theorem ordered_monomial_four_instance :
    (∫ x in domain (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (1 : ℝ)), ∏ j, x j) = 1 / 384 := by
  have h := ordered_shifted_monomial 4 (fun _ => 1) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num [momentDenom, Fin.sum_univ_succ, Fin.init] at h
  simpa using h

end LeanLab.ChenDoubleSieve.Task562
