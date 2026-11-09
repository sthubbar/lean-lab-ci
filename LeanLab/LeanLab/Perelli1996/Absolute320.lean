/-
Perelli 1996, page 481 equation 2.
The absolutely summed Ramanujan coefficients have a logarithmic majorant.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Series320
import LeanLab.Perelli1996.TotientRatio320

namespace LeanLab.Perelli1996.Absolute320
open Finset Real
noncomputable section

/-- The positive prime envelope for the absolute Ramanujan coefficients is summable. -/
theorem summable_prime_envelope :
    Summable (fun p : Nat.Primes => 1 / ((p.1 : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun p : Nat.Primes => 4 / (p.1 : ℝ) ^ 2) := by
    have h : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left 4
    exact h.subtype _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (hf := hs)
  intro p
  exact inv_sub_one_sq_le (by exact_mod_cast p.2.two_le)

/-- The absolute coefficient sum is at most an absolute constant times m over phi m. -/
theorem sum_norm_le_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (∑' q : ℕ, ‖Series320.coefficient m q‖) ≤ C * ((m : ℝ) / m.totient) := by
  classical
  let a : Nat.Primes → ℝ := fun p => 1 / ((p.1 : ℝ) - 1) ^ 2
  let T := ∑' p : Nat.Primes, a p
  let C := Real.exp T
  have hC : 0 < C := Real.exp_pos _
  have ha : ∀ p : Nat.Primes, 0 ≤ a p := fun _ => by dsimp [a]; positivity
  have hsum : Summable a := summable_prime_envelope
  have henvelope (s : Finset Nat.Primes) : (∏ p ∈ s, (1 + a p)) ≤ C := by
    calc
      _ ≤ ∏ p ∈ s, Real.exp (a p) := by
        apply Finset.prod_le_prod₀ (fun p _ => by have := ha p; linarith)
        intro p hp
        have h := Real.add_one_le_exp (a p)
        linarith
      _ = Real.exp (∑ p ∈ s, a p) := by rw [Real.exp_sum]
      _ ≤ C := Real.exp_le_exp.mpr (hsum.sum_le_tsum s (fun p _ => ha p))
  refine ⟨C, hC, ?_⟩
  intro m hm
  let f : ℕ → ℝ := fun q => ‖Series320.coefficient m q‖
  have hf1 : f 1 = 1 := by simp [f, Series320.coefficient_one]
  have hf0 : f 0 = 0 := by simp [f, Series320.coefficient_zero]
  have hfmul {q r : ℕ} (h : Nat.Coprime q r) : f (q * r) = f q * f r := by
    simp [f, Series320.coefficient_mul m q r h, norm_mul]
  have hsf : Summable (fun q => ‖f q‖) := (Series320.summable_norm_coefficient m hm).norm
  have heuler := EulerProduct.eulerProduct_hasProd (f := f) hf1 (fun {_ _} h => hfmul h) hsf hf0
  have hfactor (p : Nat.Primes) : (∑' e : ℕ, f (p.1 ^ e)) = 1 + f p.1 := by
    have hzero (e : ℕ) (he : e ∉ ({0, 1} : Finset ℕ)) : f (p.1 ^ e) = 0 := by
      have he2 : 2 ≤ e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      have hns : ¬ Squarefree (p.1 ^ e) := by
        rw [Nat.squarefree_pow_iff p.2.ne_one (by omega)]
        simp only [not_and]
        intro _
        omega
      simp [f, Series320.coefficient_nonsquarefree m _ hns]
    rw [tsum_eq_sum hzero, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), pow_zero, pow_one, hf1]
  have hprod : HasProd (fun p : Nat.Primes => 1 + f p.1) (∑' q : ℕ, f q) := by
    simpa only [hfactor] using heuler
  have hnormp (p : Nat.Primes) : f p.1 =
      if p.1 ∣ m then 1 / ((p.1 : ℝ) - 1) else 1 / ((p.1 : ℝ) - 1) ^ 2 := by
    have hh := Series320.coefficient_prime m p.1 p.2
    have heq : Series320.coefficient m p.1 =
        ((if p.1 ∣ m then 1 / ((p.1 : ℝ) - 1) else -(1 / ((p.1 : ℝ) - 1) ^ 2) : ℝ) : ℂ) := by
      unfold singF at hh
      split_ifs at hh ⊢ <;> push_cast at * <;> linear_combination hh
    dsimp [f]
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    let r : ℕ := p.1
    change |(if r ∣ m then 1 / ((r : ℝ) - 1) else -(1 / ((r : ℝ) - 1) ^ 2))| =
      if r ∣ m then 1 / ((r : ℝ) - 1) else 1 / ((r : ℝ) - 1) ^ 2
    have hp2 : (2 : ℝ) ≤ r := by exact_mod_cast p.2.two_le
    have hpos : 0 ≤ 1 / ((r : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    have hsquare : 0 ≤ 1 / ((r : ℝ) - 1) ^ 2 := by positivity
    split_ifs <;> simp only [abs_neg, abs_of_nonneg hpos, abs_of_nonneg hsquare]
  have hpoint (p : Nat.Primes) : 1 + f p.1 ≤ (1 + a p) *
      (if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
    rw [hnormp]
    have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    have hp1 : 0 < (p.1 : ℝ) - 1 := by linarith
    by_cases hd : p.1 ∣ m
    · rw [if_pos hd, if_pos hd]
      have heq : 1 + 1 / ((p.1 : ℝ) - 1) = (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by field_simp <;> ring
      rw [heq]
      have := ha p
      have hnon : 0 ≤ (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by positivity
      nlinarith
    · simp [hd, a]
  have hfinite (s : Finset Nat.Primes) : (∏ p ∈ s, (1 + f p.1)) ≤ C * ((m : ℝ) / m.totient) := by
    let u := s.filter (fun p => p.1 ∣ m)
    let v := u.image (fun p : Nat.Primes => (p : ℕ))
    have hv : v ⊆ m.primeFactors := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Nat.mem_primeFactors.mpr ⟨q.2, (Finset.mem_filter.mp hq).2, hm.ne'⟩
    have hratio : (∏ p ∈ s, if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) ≤
        (m : ℝ) / m.totient := by
      rw [← Finset.prod_filter]
      change (∏ p ∈ u, (p.1 : ℝ) / ((p.1 : ℝ) - 1)) ≤ _
      have heq : (∏ p ∈ v, (p : ℝ) / ((p : ℝ) - 1)) =
          ∏ p ∈ u, (p.1 : ℝ) / ((p.1 : ℝ) - 1) := by
        dsimp [v]
        exact Finset.prod_image Nat.Primes.coe_nat_injective.injOn
      rw [← heq]
      rw [TotientRatio320.ratio_eq_product m hm]
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hv
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors (hv hp)).two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · intro p hp hnot
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
    have hratioProd0 : 0 ≤ ∏ p ∈ s,
        if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 := by
      apply Finset.prod_nonneg
      intro p hp
      split_ifs
      · have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
        exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · norm_num
    calc
      _ ≤ ∏ p ∈ s, (1 + a p) *
          (if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
        exact Finset.prod_le_prod₀ (fun p _ => by dsimp [f]; positivity) (fun p _ => hpoint p)
      _ = (∏ p ∈ s, (1 + a p)) *
          (∏ p ∈ s, if p.1 ∣ m then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1) := by
        rw [Finset.prod_mul_distrib]
      _ ≤ C * ((m : ℝ) / m.totient) :=
        mul_le_mul (henvelope s) hratio hratioProd0 hC.le
  exact le_of_tendsto hprod (Filter.Eventually.of_forall hfinite)

/-- The absolute Ramanujan coefficient sum has an elementary logarithmic bound. -/
theorem sum_norm_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      (∑' q : ℕ, ‖Series320.coefficient m q‖) ≤ C * (1 + Real.log m) := by
  obtain ⟨C, hC, hbound⟩ := sum_norm_le_ratio
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm
  have h := mul_le_mul_of_nonneg_left (TotientRatio320.ratio_le_log m hm) hC.le
  exact (hbound m hm).trans (by nlinarith)

end
end LeanLab.Perelli1996.Absolute320
