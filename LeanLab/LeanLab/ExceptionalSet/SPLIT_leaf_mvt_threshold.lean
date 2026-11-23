/-
Split of the leaf `leaf_mvt_threshold` of `LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt`:
the instance of Vinogradov's mean value theorem at the least admissible exponent
`b = n l + [n(n+1)/4 + 1]`, for every `n >= 12`, `l > 0` and `P > 0`.

The cut is the standard one for a mean value bound.  The integrand of the target is the
`2b`-th power of a modulus, so the integral is a count: expanding the modulus and
integrating the exponential over the cube leaves exactly the number of `2b`-tuples
`(x_1, ..., x_b, y_1, ..., y_b)` in `[1, P]` whose first `n` power sums agree.  The
target's exponent is written as `(diagonal power) times (excess factor)`,
`P^(2b - n(n+1)/2) * P^(n(n+1)/2 * (1 - 1/n)^l)`, so the bound on the count and the
reassembly of that product are separated.  The count bound itself is cut at `l = 1`,
where the elementary determination of a tuple by its power sums already suffices, and at
`l >= 2`, where the mean value input proper is needed.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt

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

/-! ### Leaves -/

/-- LEAF. The identity that turns the target into a count: the modulus is expanded and the
exponential integrated out over the unit cube, so the integral of the `2b`-th power of the
exponential sum, at the target's exponent `b = n l + [n(n+1)/4 + 1]`, equals the number of
pairs of `b`-tuples `(x, y)` with entries in `[1, P]` whose power sums
`x_1^j + ... + x_b^j` and `y_1^j + ... + y_b^j` agree for every `j` from `1` to `n`.
One identity, no inequality. -/
theorem leaf_integral_eq_solution_count :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ)
      = ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0) := by
  intro n hn l hl P hP
  set B : ℕ := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hB
  set A : Fin P → Fin n → ℤ := fun i j => ((i.val + 1 : ℕ) : ℤ) ^ ((j : ℕ) + 1) with hA
  have hS : ∀ α : Fin n → ℝ,
      (∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1)))
      = ∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ)) := by
    intro α
    rw [sum_Icc_one_eq_sum_fin P
      (fun x => eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1)))]
    apply Finset.sum_congr rfl
    intro i _
    have harg : (∑ j : Fin n, α j * (↑(i.val + 1) : ℝ) ^ ((j : ℕ) + 1))
        = ∑ j : Fin n, α j * (A i j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hA]
      simp only
      push_cast
      ring
    rw [harg]
  have hcov : ∀ α : Fin n → ℝ,
      ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * B)
      = (((∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ))) *
          (∑ i : Fin P, eC (∑ j : Fin n, α j * (-(A i j : ℝ))))) ^ B).re := by
    intro α
    rw [hS α, norm_pow_eq]
    have hstar : (starRingEnd ℂ) (∑ i : Fin P, eC (∑ j : Fin n, α j * (A i j : ℝ)))
        = ∑ i : Fin P, eC (∑ j : Fin n, α j * (-(A i j : ℝ))) := by
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
  rw [integral_pair_pow_real n P B A A]
  have hx : ∀ (z : Fin B → Fin P) (j : Fin n),
      ((∑ i : Fin B, A (z i) j : ℤ) : ℝ)
        = ∑ i : Fin B, (((z i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1) := by
    intro z j
    refine Eq.trans (map_sum (Int.castRingHom ℝ) (fun i : Fin B => A (z i) j)
      Finset.univ) ?_
    apply Finset.sum_congr rfl
    intro i _
    rw [hA]
    simp
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc : ((∀ j : Fin n, ∑ i : Fin B, A (x i) j = ∑ i : Fin B, A (y i) j)
      ↔ (∀ j : Fin n,
          ∑ i : Fin B, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
            = ∑ i : Fin B, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))) := by
    refine forall_congr' (fun j => ?_)
    rw [← Int.cast_inj (α := ℝ), hx x j, hx y j]
  by_cases h : (∀ j : Fin n, ∑ i : Fin B, A (x i) j = ∑ i : Fin B, A (y i) j)
  · rw [if_pos h, if_pos (hc.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh))]

/-! ### The elementary count at `l = 1`: Newton identities and fixing the free entries -/

/-- Newton identities, Mathlib `MvPolynomial.mul_esymm_eq_sum`: equal power sums of orders
`1..n` give equal elementary symmetric functions of two real `n`-tuples. -/
private theorem esymm_eq_aux (n : ℕ) (u v : Fin n → ℝ)
    (h : ∀ j : Fin n, ∑ i : Fin n, u i ^ ((j : ℕ) + 1) = ∑ i : Fin n, v i ^ ((j : ℕ) + 1))
    (k : ℕ) (hk : k ≤ n) :
    MvPolynomial.aeval u (MvPolynomial.esymm (Fin n) ℝ k)
      = MvPolynomial.aeval v (MvPolynomial.esymm (Fin n) ℝ k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · have hu := congrArg (MvPolynomial.aeval u) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ k)
      have hv := congrArg (MvPolynomial.aeval v) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ k)
      simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one] at hu hv
      have hk0 : (k:ℝ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hk0
      rw [hu, hv]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      rw [ih a.1 ha.2 (by omega)]
      congr 1
      have hb : a.2 - 1 < n := by omega
      have h1 := h ⟨a.2 - 1, hb⟩
      have e : a.2 - 1 + 1 = a.2 := by omega
      dsimp only at h1
      simp only [e] at h1
      simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
      exact h1

/-- Two real `n`-tuples with equal power sums of orders `1..n` have the same roots of
`prod (X - u_i)`, so every entry of one is an entry of the other. -/
private theorem exists_eq_of_psum_eq (n : ℕ) (u v : Fin n → ℝ)
    (h : ∀ j : Fin n, ∑ i : Fin n, u i ^ ((j : ℕ) + 1) = ∑ i : Fin n, v i ^ ((j : ℕ) + 1))
    (i : Fin n) : ∃ t : Fin n, u i = v t := by
  have he : ∀ k ≤ n, (Multiset.map u Finset.univ.val).esymm k
      = (Multiset.map v Finset.univ.val).esymm k := by
    intro k hk
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℝ k u,
      ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℝ k v]
    exact esymm_eq_aux n u v h k hk
  have hp : ((Multiset.map u Finset.univ.val).map fun t => Polynomial.X - Polynomial.C t).prod
      = ((Multiset.map v Finset.univ.val).map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j hj
    rw [he j (by have := Finset.mem_range.mp hj; omega)]
  have hp' : ∏ t : Fin n, (Polynomial.X - Polynomial.C (u t))
      = ∏ t : Fin n, (Polynomial.X - Polynomial.C (v t)) := by
    rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
    simpa only [Multiset.map_map, Function.comp_def] using hp
  have h2 := congrArg (Polynomial.eval (u i)) hp'
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h2.symm
  exact ⟨t, sub_eq_zero.mp ht⟩

private theorem card_le_of_valueset {α : Type*} (n : ℕ) (s : Finset (Fin n → α))
    (h : ∀ g ∈ s, ∀ g' ∈ s, ∀ i, ∃ t, g i = g' t) : s.card ≤ n ^ n := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨g0, hg0⟩
  · simp
  · have key : ∀ g ∈ s, ∃ φ : Fin n → Fin n, ∀ i, g i = g0 (φ i) := by
      intro g hg
      choose φ hφ using h g hg g0 hg0
      exact ⟨φ, hφ⟩
    have hle : s.card ≤ (Finset.univ : Finset (Fin n → Fin n)).card := by
      apply Finset.card_le_card_of_injOn
        (fun g => if hg : g ∈ s then Classical.choose (key g hg) else fun i => i)
        (fun _ _ => Finset.mem_univ _)
      intro g hg g' hg' e
      have hg1 : g ∈ s := Finset.mem_coe.mp hg
      have hg1' : g' ∈ s := Finset.mem_coe.mp hg'
      simp only [hg1, hg1', dif_pos] at e
      funext i
      rw [Classical.choose_spec (key g hg1) i, Classical.choose_spec (key g' hg1') i, e]
    simpa using hle

private theorem card_T (n m P : ℕ)
    (hN : ∀ (u v : Fin n → ℝ),
      (∀ j : Fin n, ∑ i : Fin n, u i ^ ((j : ℕ) + 1) = ∑ i : Fin n, v i ^ ((j : ℕ) + 1)) →
        ∀ i : Fin n, ∃ t : Fin n, u i = v t)
    (c : Fin n → ℝ) (T : Finset (Fin (n + m) → Fin P))
    (hT : ∀ y ∈ T, ∀ j : Fin n,
      ∑ i : Fin (n + m), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1) = c j) :
    T.card ≤ n ^ n * P ^ m := by
  have h1 := Finset.card_le_mul_card_image
    (f := fun y : Fin (n + m) → Fin P => fun i : Fin m => y (Fin.natAdd n i)) T (n ^ n) ?_
  · refine h1.trans (Nat.mul_le_mul_left _ ?_)
    refine (Finset.card_le_univ _).trans ?_
    simp
  · intro r _
    have hinj : Set.InjOn (fun y : Fin (n + m) → Fin P => fun i : Fin n => y (Fin.castAdd m i))
        ((T.filter (fun y => (fun i : Fin m => y (Fin.natAdd n i)) = r) : Finset _) : Set _) := by
      intro y hy y' hy' e
      have hy1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      have hy1' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy')).2
      funext i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · exact congrFun e k
      · exact (congrFun hy1 k).trans (congrFun hy1' k).symm
    rw [← Finset.card_image_of_injOn hinj]
    apply card_le_of_valueset
    intro g hg g' hg' i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hg'
    obtain ⟨hyT, hyr⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyT', hyr'⟩ := Finset.mem_filter.mp hy'
    have hpow : ∀ j : Fin n,
        ∑ i : Fin n, (fun i : Fin n => (((y (Fin.castAdd m i)).val + 1 : ℕ) : ℝ)) i ^ ((j : ℕ) + 1)
          = ∑ i : Fin n, (fun i : Fin n => (((y' (Fin.castAdd m i)).val + 1 : ℕ) : ℝ)) i ^ ((j : ℕ) + 1) := by
      intro j
      have a := hT y hyT j
      have a' := hT y' hyT' j
      rw [Fin.sum_univ_add] at a a'
      have tl : ∀ k : Fin m, y (Fin.natAdd n k) = y' (Fin.natAdd n k) :=
        fun k => (congrFun hyr k).trans (congrFun hyr' k).symm
      simp only [tl] at a
      simp only
      linarith
    obtain ⟨t, ht⟩ := hN _ _ hpow i
    refine ⟨t, ?_⟩
    have h2 : (y (Fin.castAdd m i)).val + 1 = (y' (Fin.castAdd m t)).val + 1 :=
      Nat.cast_injective (R := ℝ) ht
    show y (Fin.castAdd m i) = y' (Fin.castAdd m t)
    exact Fin.ext (by omega)

private theorem count_pairs_le (n m P : ℕ)
    (hN : ∀ (u v : Fin n → ℝ),
      (∀ j : Fin n, ∑ i : Fin n, u i ^ ((j : ℕ) + 1) = ∑ i : Fin n, v i ^ ((j : ℕ) + 1)) →
        ∀ i : Fin n, ∃ t : Fin n, u i = v t)
    (B : ℕ) (hB : B = n + m) :
    (∑ x : Fin B → Fin P, ∑ y : Fin B → Fin P,
      (if (∀ j : Fin n,
          ∑ i : Fin B, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
            = ∑ i : Fin B, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
        then (1 : ℝ) else 0))
    ≤ (n : ℝ) ^ n * (P : ℝ) ^ (n + m) * (P : ℝ) ^ m := by
  subst hB
  refine (Finset.sum_le_sum (g := fun _ => (n : ℝ) ^ n * (P : ℝ) ^ m) (fun x _ => ?_)).trans
    (le_of_eq ?_)
  · rw [Finset.sum_boole]
    refine le_trans (Nat.cast_le.mpr (card_T n m P hN
      (fun j => ∑ i : Fin (n + m), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)) _
      (fun y hy j => ((Finset.mem_filter.mp hy).2 j).symm))) ?_
    push_cast
    exact le_rfl
  · rw [Finset.sum_const]
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    ring

private theorem leaf_one_arith (n F P : ℕ) (hn : 12 ≤ n) (hP : 0 < P) :
    (n : ℝ) ^ n * (P : ℝ) ^ (n + F) * (P : ℝ) ^ F
      < (20 * (n : ℝ)) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) *
          ((P : ℝ) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2 * (1 - 1 / (n : ℝ))) *
           (P : ℝ) ^ (2 * ((n : ℝ) + (F : ℝ)) - (n : ℝ) * ((n : ℝ) + 1) / 2)) := by
  have hn0 : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have h1 : (n : ℝ) ^ n < (20 * (n : ℝ)) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) := by
    have ha : (n : ℝ) ^ n < (20 * (n : ℝ)) ^ n :=
      pow_lt_pow_left₀ (by linarith) hnpos.le (by omega)
    have hb : (20 * (n : ℝ)) ^ n = (20 * (n : ℝ)) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
    have hc : (20 * (n : ℝ)) ^ (n : ℝ) ≤ (20 * (n : ℝ)) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      nlinarith
    calc (n : ℝ) ^ n < (20 * (n : ℝ)) ^ n := ha
      _ = (20 * (n : ℝ)) ^ (n : ℝ) := hb
      _ ≤ _ := hc
  have h2 : (P : ℝ) ^ (n + F) * (P : ℝ) ^ F
      ≤ (P : ℝ) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2 * (1 - 1 / (n : ℝ))) *
           (P : ℝ) ^ (2 * ((n : ℝ) + (F : ℝ)) - (n : ℝ) * ((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hPpos, ← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have he : (n : ℝ) * ((n : ℝ) + 1) / 2 * (1 - 1 / (n : ℝ)) = ((n : ℝ) + 1) * ((n : ℝ) - 1) / 2 := by
      field_simp
    rw [he]
    push_cast
    nlinarith
  have hpos : 0 < (P : ℝ) ^ (n + F) * (P : ℝ) ^ F := by positivity
  have hnn : (0 : ℝ) ≤ (20 * (n : ℝ)) ^ ((n : ℝ) * ((n : ℝ) + 1) / 2) := by positivity
  rw [mul_assoc]
  exact mul_lt_mul h1 h2 hpos hnn

/-- LEAF. The threshold exponent bound at `l = 1`, in counting form and with the diagonal
power taken out: at `b = n + [n(n+1)/4 + 1]` the number of pairs of `b`-tuples in `[1, P]`
with equal power sums up to order `n` is below `(20 n)^(n(n+1)/2)` times
`P^(n(n+1)/2 * (1 - 1/n))` times `P^(2b - n(n+1)/2)`. One inequality, the `l = 1` instance
only, the case the elementary determination of a tuple by its first `n` power sums reaches;
the number of `b`-tuples above `n` carrying a fixed initial data is what is being counted. -/
theorem leaf_solution_count_at_one :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, l = 1 → ∀ P : ℕ, 0 < P →
      ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  intro n hn l hl P hP
  subst hl
  refine lt_of_le_of_lt
    (count_pairs_le n (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) P
      (exists_eq_of_psum_eq n)
      (n * 1 + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) (by rw [Nat.mul_one])) ?_
  have key := leaf_one_arith n (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) P hn hP
  generalize (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) = F at key ⊢
  simp only [Nat.cast_one, mul_one, pow_one, Nat.cast_mul, Nat.cast_add]
  exact key

/-- LEAF. The same threshold bound for `l ≥ 2`, in the same counting form. This is the
step that needs genuine mean value input rather than the elementary determination count:
`b` exceeds `n + [n(n+1)/4 + 1]`, so each initial segment of a tuple is determined by its
power sums only up to `n` entries and the count must be fed through the mean value
inequality at the previous exponent. One inequality. -/
theorem leaf_solution_count_deep :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → 2 ≤ l → ∀ P : ℕ, 0 < P →
      ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  intro n hn l hl h2l P hP
  -- CONDITIONAL ON the CITED input `leaf_karLemma1_mvt` of KaracubaSplit: Vinogradov's
  -- mean value theorem in Karacuba's exact form.  The count is the integral by the proved
  -- identity `leaf_integral_eq_solution_count`, and the bound is the `b = b_l` case of the
  -- cited lemma, reassembled through `leaf_excess_exponent_identity`.
  rw [← leaf_integral_eq_solution_count n hn l hl P hP]
  have hkar := leaf_karLemma1_mvt n hn l hl (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊))
    (Nat.le_refl _) P hP
  have hb : ((n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ)
      = (n : ℝ) * (l : ℝ) + ((⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hb] at hkar
  have hp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [Real.rpow_add hp] at hkar
  exact lt_of_lt_of_le hkar (le_of_eq (by ring))

/-- LEAF. The bookkeeping identity that reassembles the two factors: for `P > 0` the
product of the diagonal power `P^(2b - n(n+1)/2)` and the excess factor
`P^(n(n+1)/2 * (1 - 1/n)^l)` is the single power of `P` at the sum of the two exponents,
with the constant `(20 n)^(n(n+1)/2 * l)` carried along. One identity. -/
theorem leaf_excess_exponent_identity :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))
      = (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro n hn l hl P hP
  have hp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  rw [Real.rpow_add hp]
  ring

/-! ### Assembly -/

/-- The sealed statement of the target `leaf_mvt_threshold`, from the four leaves of this
file: the integral is the count, the count is bounded at `l = 1` and at `l ≥ 2`, and the
two factors of the bound multiply back to the single power at the target's exponent. -/
theorem leaf_mvt_threshold_split :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → ∀ P : ℕ, 0 < P →
      ∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖∑ x ∈ Finset.Icc 1 P, eC (∑ j : Fin n, α j * (x : ℝ) ^ ((j : ℕ) + 1))‖ ^
          (2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℕ) <
        (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
        (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2
          + ((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) := by
  intro n hn l hl P hP
  rcases Nat.lt_or_ge l 2 with hsmall | hbig
  · have hl1 : l = 1 := by omega
    rw [leaf_integral_eq_solution_count n hn l hl P hP,
      ← leaf_excess_exponent_identity n hn l hl P hP]
    exact leaf_solution_count_at_one n hn l hl1 P hP
  · rw [leaf_integral_eq_solution_count n hn l hl P hP,
      ← leaf_excess_exponent_identity n hn l hl P hP]
    exact leaf_solution_count_deep n hn l hl hbig P hP

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
