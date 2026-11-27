import LeanLab.ExceptionalSet.SPLIT_leaf_mvt_threshold
import LeanLab.ExceptionalSet.SPLIT_leaf_karW_display8

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539
open Classical

/-! ### Helpers for the integral-count identity -/

private theorem eC_zero' : eC 0 = 1 := by
  unfold eC
  simp

private theorem eC_add' (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [show 2 * ↑Real.pi * Complex.I * ↑(a + b)
      = 2 * ↑Real.pi * Complex.I * ↑a + 2 * ↑Real.pi * Complex.I * ↑b by
    push_cast
    ring]
  rw [Complex.exp_add]

private theorem eC_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eC_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, eC_add', ih]

private theorem star_eC' (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := (eC_neg x).symm

private theorem star_eC_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (starRingEnd ℂ) (eC (∑ i ∈ s, f i)) = eC (∑ i ∈ s, -f i) := by
  rw [star_eC', ← Finset.sum_neg_distrib]

/-! ### Norms -/

/-- `‖z‖^(2b) = ((z * conj z)^b).re`: the `2b`-th power of the modulus is the real part of
the `b`-th power of `z * conj z`. -/
private theorem norm_pow_eq (z : ℂ) (B : ℕ) :
    ‖z‖ ^ (2 * B) = ((z * (starRingEnd ℂ) z) ^ B).re := by
  have h : z * (starRingEnd ℂ) z = ((Complex.normSq z : ℝ) : ℂ) := Complex.mul_conj z
  rw [h, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.normSq_eq_norm_sq, ← pow_mul]

/-! ### Reindexing `Finset.Icc 1 P` as `Fin P` -/

private theorem sum_range_succ_eq_sum_Icc_one (P : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : ∑ i ∈ Finset.range P, f (i + 1) = ∑ x ∈ Finset.Icc 1 P, f x := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    simpa using hab
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b - 1, Finset.mem_range.mpr (by omega), ?_⟩
    show b - 1 + 1 = b
    omega
  · intro a _
    rfl

private theorem sum_Icc_one_eq_sum_fin (P : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ x ∈ Finset.Icc 1 P, f x = ∑ i : Fin P, f (i.val + 1) := by
  rw [← sum_range_succ_eq_sum_Icc_one P f]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) P).symm

/-! ### The character integral on `[0,1]` -/

private theorem integral_exp_char_Ioc (m : ℤ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, eC (x * (m : ℝ)) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hm : m = 0
  · subst hm
    simp [eC]
  · have h2 : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      apply mul_ne_zero
      · rw [show (2 * (↑Real.pi : ℂ)) = ↑(2 * Real.pi) by push_cast; ring]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      · exact Complex.I_ne_zero
    have hc : (2 * ↑Real.pi * Complex.I * (m : ℝ) : ℂ) ≠ 0 := mul_ne_zero h2 (by
      rw [show ((m : ℝ) : ℂ) = ((m : ℂ)) by push_cast; ring]
      exact_mod_cast hm)
    have hcongr : Set.EqOn (fun x : ℝ => eC (x * (m : ℝ)))
        (fun x : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ((m : ℝ) : ℂ)) * (x : ℂ)))
        (Set.uIcc 0 1) := by
      intro x _
      dsimp only
      unfold eC
      rw [show 2 * ↑Real.pi * Complex.I * (↑(x * (m : ℝ)) : ℂ)
          = (2 * ↑Real.pi * Complex.I * ((m : ℝ) : ℂ)) * (x : ℂ) by push_cast; ring]
    rw [intervalIntegral.integral_congr hcongr, integral_exp_mul_complex hc]
    have hexp : Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ)) = 1 := by
      rw [show 2 * ↑Real.pi * Complex.I * (m : ℂ)
          = (m : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    simp [hexp, hm]

private theorem integral_exp_char_Icc (m : ℤ) :
    ∫ x in Set.Icc (0 : ℝ) 1, eC (x * (m : ℝ)) = if m = 0 then 1 else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact integral_exp_char_Ioc m


/-! ### The character integral on the cube -/

section mvt_helpers

open MeasureTheory

private theorem continuous_char (n : ℕ) (M : Fin n → ℝ) :
    Continuous fun α : Fin n → ℝ => eC (∑ j : Fin n, α j * M j) := by
  unfold eC
  fun_prop

private theorem integrable_char (n : ℕ) (M : Fin n → ℤ) :
    Integrable (fun α : Fin n → ℝ => eC (∑ j : Fin n, α j * (M j : ℝ))) (Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (continuous_char n (fun j => (M j : ℝ))).aestronglyMeasurable
  · filter_upwards with α
    rw [norm_eC]

private theorem integrable_sum_char {n : ℕ} {ι : Type*} [Fintype ι] (D : ι → Fin n → ℤ) :
    Integrable (fun α : Fin n → ℝ => ∑ y : ι, eC (∑ j : Fin n, α j * (D y j : ℝ))) (Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  refine Integrable.of_bound ?_ ((Fintype.card ι : ℕ) : ℝ) ?_
  · apply Continuous.aestronglyMeasurable
    exact continuous_finsetSum _ (fun y _ => continuous_char n (fun j => (D y j : ℝ)))
  · filter_upwards with α
    calc ‖∑ y : ι, eC (∑ j : Fin n, α j * (D y j : ℝ))‖
        ≤ ∑ y : ι, ‖eC (∑ j : Fin n, α j * (D y j : ℝ))‖ := norm_sum_le _ _
      _ = ∑ _y : ι, (1 : ℝ) := by simp [norm_eC]
      _ = ((Fintype.card ι : ℕ) : ℝ) := by simp

/-- The integral of one character over the unit cube: `1` if all the coefficients vanish,
`0` otherwise. -/
private theorem integral_prod_char (n : ℕ) (M : Fin n → ℤ) :
    (∫ α, eC (∑ j : Fin n, α j * (M j : ℝ)) ∂(Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
      = if (∀ j, M j = 0) then 1 else 0 := by
  have hF : ∀ α : Fin n → ℝ, eC (∑ j : Fin n, α j * (M j : ℝ))
      = ∏ j : Fin n, eC (α j * (M j : ℝ)) := by
    intro α
    rw [eC_sum' Finset.univ (fun j => α j * (M j : ℝ))]
  simp only [hF]
  rw [integral_fintype_prod_eq_prod (f := fun j x => eC (x * (M j : ℝ)))]
  simp only [integral_exp_char_Icc]
  have h := Finset.prod_boole (M₀ := ℂ) (s := Finset.univ) (p := fun j : Fin n => M j = 0)
  simpa using h

/-- The product of two characters, one from each side of the pairing. -/
private theorem eC_pair_mul' {n : ℕ} (A C : Fin n → ℤ) (α : Fin n → ℝ) :
    eC (∑ j : Fin n, α j * (A j : ℝ)) * eC (∑ j : Fin n, α j * (-(C j : ℝ)))
      = eC (∑ j : Fin n, α j * ((A j - C j : ℤ) : ℝ)) := by
  rw [← eC_add', ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- The `B`-fold product of paired characters is one character with the summed coefficients. -/
private theorem eC_prod_pairs {n P B : ℕ} (A C : Fin P → Fin n → ℤ) (α : Fin n → ℝ)
    (x y : Fin B → Fin P) :
    (∏ i : Fin B, eC (∑ j : Fin n, α j * (A (x i) j : ℝ))) *
        (∏ i : Fin B, eC (∑ j : Fin n, α j * (-(C (y i) j : ℝ))))
      = eC (∑ j : Fin n, α j * ((∑ i : Fin B, (A (x i) j - C (y i) j) : ℤ) : ℝ)) := by
  rw [← Finset.prod_mul_distrib]
  have h1 : ∀ i : Fin B, eC (∑ j : Fin n, α j * (A (x i) j : ℝ)) *
        eC (∑ j : Fin n, α j * (-(C (y i) j : ℝ)))
      = eC (∑ j : Fin n, α j * ((A (x i) j - C (y i) j : ℤ) : ℝ)) :=
    fun i => eC_pair_mul' (fun j => A (x i) j) (fun j => C (y i) j) α
  simp only [h1]
  rw [← eC_sum' Finset.univ
    (fun i : Fin B => ∑ j : Fin n, α j * ((A (x i) j - C (y i) j : ℤ) : ℝ))]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  congr 1
  exact (map_sum (Int.castRingHom ℝ) (fun i : Fin B => (A (x i) j - C (y i) j)) Finset.univ).symm

set_option maxHeartbeats 2000000 in
/-- The `B`-th power of a product of two exponential sums, as the integral of a double sum of
characters. -/
private theorem integral_pair_pow_C (n P B : ℕ) (A C : Fin P → Fin n → ℤ) :
    (∫ α, (((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))) ^ B ∂(Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
    = ∑ x : Fin B → Fin P, ∑ y : Fin B → Fin P,
        if (∀ j : Fin n, (∑ i : Fin B, (A (x i) j - C (y i) j)) = 0) then (1 : ℂ) else 0 := by
  have hpt : ∀ α : Fin n → ℝ,
      (((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))) ^ B
      = ∑ x : Fin B → Fin P, ∑ y : Fin B → Fin P,
          eC (∑ j : Fin n, α j * ((∑ i : Fin B, (A (x i) j - C (y i) j) : ℤ) : ℝ)) := by
    intro α
    rw [mul_pow, Fintype.sum_pow, Fintype.sum_pow, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
      (fun y _ => eC_prod_pairs (n := n) (P := P) (B := B) A C α x y))
  simp only [hpt]
  rw [integral_finsetSum Finset.univ
    (fun x _ => integrable_sum_char (ι := Fin B → Fin P)
      (D := fun (y : Fin B → Fin P) (j : Fin n) => ∑ i : Fin B, (A (x i) j - C (y i) j)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum Finset.univ
    (fun y _ => integrable_char n (M := fun j : Fin n => ∑ i : Fin B, (A (x i) j - C (y i) j)))]
  exact Finset.sum_congr rfl (fun y _ =>
    integral_prod_char n (fun j => ∑ i : Fin B, (A (x i) j - C (y i) j)))

set_option maxHeartbeats 2000000 in
/-- The same identity for the real part. -/
private theorem integral_pair_pow_real (n P B : ℕ) (A C : Fin P → Fin n → ℤ) :
    (∫ α, ((((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))) ^ B).re ∂(Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
    = ∑ x : Fin B → Fin P, ∑ y : Fin B → Fin P,
        if (∀ j : Fin n, ∑ i : Fin B, A (x i) j = ∑ i : Fin B, C (y i) j)
          then (1 : ℝ) else 0 := by
  have hInt : Integrable (fun α : Fin n → ℝ => ((((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))) ^ B)) (Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine Integrable.of_bound ?_ ((P : ℝ) ^ (2 * B)) ?_
    · apply Continuous.aestronglyMeasurable
      apply Continuous.pow
      apply Continuous.mul
      · exact continuous_finsetSum _ (fun i _ => continuous_char n (fun j => (A i j : ℝ)))
      · exact continuous_finsetSum _ (fun i _ => continuous_char n (fun j => -(C i j : ℝ)))
    · filter_upwards with α
      rw [norm_pow]
      have h1 : ‖∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))‖ ≤ (P : ℝ) := by
        calc ‖∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))‖
            ≤ ∑ i : Fin P, ‖eC (∑ j : Fin n, α j * (A i j : ℝ))‖ := norm_sum_le _ _
          _ = ∑ _i : Fin P, (1 : ℝ) := by simp [norm_eC]
          _ = (P : ℝ) := by simp
      have h2 : ‖∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))‖ ≤ (P : ℝ) := by
        calc ‖∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))‖
            ≤ ∑ i : Fin P, ‖eC (∑ j : Fin n, α j * (-(C i j : ℝ)))‖ := norm_sum_le _ _
          _ = ∑ _i : Fin P, (1 : ℝ) := by simp [norm_eC]
          _ = (P : ℝ) := by simp
      have hmul : ‖((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))‖ ≤ (P : ℝ) * P := by
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) * (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(C i j : ℝ)))))‖ ^ B
          ≤ ((P : ℝ) * P) ^ B := pow_le_pow_left₀ (norm_nonneg _) hmul B
        _ = (P : ℝ) ^ (2 * B) := by rw [mul_pow, ← pow_add, two_mul]
  have hstep := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) Complex.reCLM hInt
  simp only [Complex.reCLM_apply] at hstep
  rw [hstep]
  rw [integral_pair_pow_C n P B A C]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc : ((∀ j : Fin n, (∑ i : Fin B, (A (x i) j - C (y i) j)) = 0)
      ↔ (∀ j : Fin n, ∑ i : Fin B, A (x i) j = ∑ i : Fin B, C (y i) j)) := by
    refine forall_congr' (fun j => ?_)
    rw [Finset.sum_sub_distrib, sub_eq_zero]
  by_cases h : (∀ j : Fin n, ∑ i : Fin B, A (x i) j = ∑ i : Fin B, C (y i) j)
  · rw [if_pos (hc.mpr h), if_pos h]
    simp
  · rw [if_neg (fun hh => h (hc.mp hh)), if_neg h]
    simp

end mvt_helpers

private theorem sum_range_eq_sum_fin (P : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : ∑ i ∈ Finset.range P, f i = ∑ x : Fin P, f x.val := by
  rw [Finset.sum_range, Fin.sum_univ_eq_sum_range f P]

/-- The unit-cube moment is the count of pairs of k-tuples with equal power sums.
This is the general integral-count identity used for the zero coefficient J_k(0).
Source: Karacuba 1971 p. 246, with the proved character orthogonality of p. 243. -/
theorem karJ0_integral_count (n k M : ℕ) :
    (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k))
      = karJ0 n k M := by
  classical
  set A : Fin (M + 1) → Fin n → ℤ :=
    fun i j => ((i : ℕ) : ℤ) ^ ((j : ℕ) + 1) with hA
  have hS : ∀ α : Fin n → ℝ,
      (∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1)))
        = ∑ i : Fin (M + 1), eC (∑ j : Fin n, α j * (A i j : ℝ)) := by
    intro α
    rw [sum_range_eq_sum_fin]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hA]
    simp only
    push_cast
    ring
  have hcov : ∀ α : Fin n → ℝ,
      ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)
        = (((∑ i : Fin (M + 1), eC (∑ j : Fin n, α j * (A i j : ℝ))) *
            (∑ i : Fin (M + 1), eC (∑ j : Fin n, α j * (-(A i j : ℝ))))) ^ k).re := by
    intro α
    rw [hS α, norm_pow_eq]
    have hstar : (starRingEnd ℂ) (∑ i : Fin (M + 1), eC (∑ j : Fin n, α j * (A i j : ℝ)))
        = ∑ i : Fin (M + 1), eC (∑ j : Fin n, α j * (-(A i j : ℝ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [star_eC_sum']
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hstar]
  simp only [hcov]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  rw [integral_pair_pow_real n (M + 1) k A A]
  have hx : ∀ (z : Fin k → Fin (M + 1)) (j : Fin n),
      ((∑ i : Fin k, A (z i) j : ℤ) : ℝ)
        = ∑ i : Fin k, (((z i).val : ℝ) ^ ((j : ℕ) + 1)) := by
    intro z j
    let g : Fin k → ℤ := fun i => A (z i) j
    refine Eq.trans (map_sum (Int.castRingHom ℝ) g Finset.univ) ?_
    apply Finset.sum_congr rfl
    intro i _
    change (Int.castRingHom ℝ) (A (z i) j) = _
    rw [hA]
    norm_num
  unfold karJ0
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : (∀ j : Fin n, (∑ i : Fin k, A (x i) j) = (∑ i : Fin k, A (y i) j))
  · have hr : ∀ j : Fin n,
        (∑ i : Fin k, (((x i).val : ℝ) ^ ((j : ℕ) + 1)))
          = (∑ i : Fin k, (((y i).val : ℝ) ^ ((j : ℕ) + 1))) := by
      intro j
      have hh := congrArg (fun z : ℤ => (z : ℝ)) (h j)
      rw [hx x j, hx y j] at hh
      exact hh
    rw [if_pos h, if_pos hr]
  · have hr : ¬ (∀ j : Fin n,
        (∑ i : Fin k, (((x i).val : ℝ) ^ ((j : ℕ) + 1)))
          = (∑ i : Fin k, (((y i).val : ℝ) ^ ((j : ℕ) + 1)))) := by
      intro hh
      apply h
      intro j
      apply (Int.cast_inj (α := ℝ)).mp
      rw [hx x j, hx y j]
      exact hh j
    rw [if_neg h, if_neg hr]


end LeanLab.ExceptionalSet.U1539.KaracubaSplit
