/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 174, finite positive cosine coefficients of each power before display 4.11.
-/
import LeanLab.PlattTrudgian2014.Dyadic421

namespace LeanLab.PlattTrudgian2014

open Finset

/-- P0026 page 174, pair positive and negative integer frequencies into a cosine mode. -/
theorem phase_real_natAbs421 (k : ℤ) (x : ℝ) :
    (phase ((k : ℝ) * x)).re = Real.cos (2 * Real.pi * (k.natAbs : ℝ) * x) := by
  unfold phase
  rw [Complex.exp_ofReal_mul_I_re]
  have he : 2 * Real.pi * ((k : ℝ) * x) = 2 * Real.pi * k * x := by ring
  rw [he]
  cases k with
  | ofNat n => simp
  | negSucc n =>
    change Real.cos (2 * Real.pi * ((Int.negSucc n : ℤ) : ℝ) * x) =
      Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)
    rw [← Real.cos_neg]
    congr 1
    push_cast
    ring

/-- P0026 page 174, collecting repeated modes in a finite positive cosine sum. -/
theorem finite_cosine_collect421 {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ν : ι → ℕ) :
    ∃ b : ℕ → ℝ, (∀ k, 0 ≤ b k) ∧ Function.HasFiniteSupport b ∧ Summable b ∧
      (∑' k : ℕ, b k) = ∑ i : ι, w i ∧
      ∀ x : ℝ, (∑ i : ι, w i * Real.cos (2 * Real.pi * ν i * x)) =
        ∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * x) := by
  classical
  let b : ℕ → ℝ := fun k => ∑ i : ι, if k = ν i then w i else 0
  have hb (k : ℕ) : 0 ≤ b k := by
    dsimp only [b]
    apply sum_nonneg
    intro i hi
    split_ifs
    · exact hw i
    · exact le_rfl
  have hf : Function.HasFiniteSupport b := by
    change (Function.support b).Finite
    apply (Finset.finite_toSet (univ.image ν)).subset
    intro k hk
    by_contra hnot
    have hne (i : ι) : k ≠ ν i := by
      intro he
      apply hnot
      simpa only [he, Finset.mem_coe] using (mem_image.mpr ⟨i, mem_univ i, rfl⟩ : ν i ∈ univ.image ν)
    have hz : b k = 0 := by simp [b, hne]
    exact hk hz
  have hs (s : Finset ι) (x : ℝ) :
      HasSum (fun k : ℕ => ∑ i ∈ s,
        (if k = ν i then w i else 0) * Real.cos (2 * Real.pi * k * x))
        (∑ i ∈ s, w i * Real.cos (2 * Real.pi * ν i * x)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
    | @insert i s hi ih =>
      have hz : HasSum (fun k : ℕ =>
          (if k = ν i then w i else 0) * Real.cos (2 * Real.pi * k * x))
          (w i * Real.cos (2 * Real.pi * ν i * x)) := by
        apply (_root_.hasSum_ite_eq (ν i) (w i * Real.cos (2 * Real.pi * ν i * x))).congr_fun
        intro k
        by_cases he : k = ν i <;> simp [he]
      simpa only [sum_insert hi] using hz.add ih
  have he (x : ℝ) : HasSum (fun k : ℕ => b k * Real.cos (2 * Real.pi * k * x))
      (∑ i : ι, w i * Real.cos (2 * Real.pi * ν i * x)) := by
    simpa only [b, sum_mul] using hs univ x
  have hsum : HasSum b (∑ i : ι, w i) := by simpa using he 0
  exact ⟨b, hb, hf, hsum.summable, hsum.tsum_eq, fun x => (he x).tsum_eq.symm⟩

/-- P0026 page 174, finite nonnegative cosine coefficients for one power of real G. -/
theorem real_power_cosine_coefficients_proved421 (L n : ℕ) :
    ∃ b : ℕ → ℝ, (∀ k, 0 ≤ b k) ∧ Function.HasFiniteSupport b ∧ Summable b ∧
      (∑' k : ℕ, b k) = (L : ℝ) ^ n ∧
      ∀ x : ℝ, (G L x).re ^ n = ∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * x) := by
  let I := Σ k : Fin (n + 1), (Fin (k : ℕ) → Fin L) × (Fin (n - (k : ℕ)) → Fin L)
  let w : I → ℝ := fun i => (n.choose (i.1 : ℕ) : ℝ)
  let ν : I → ℕ := fun i =>
    ((∑ j : Fin (i.1 : ℕ), (2 : ℤ) ^ (i.2.1 j : ℕ)) -
      (∑ j : Fin (n - (i.1 : ℕ)), (2 : ℤ) ^ (i.2.2 j : ℕ))).natAbs
  obtain ⟨c, hc, hcf, hcs, hcm, hce⟩ := finite_cosine_collect421 w
    (fun i => Nat.cast_nonneg _) ν
  have hp (x : ℝ) : (2 : ℝ) ^ n * (G L x).re ^ n =
      ∑ i : I, w i * Real.cos (2 * Real.pi * ν i * x) := by
    have hh := real_power_binomial421 (G L x) n
    simp_rw [G_mixed_tuples421, Complex.re_sum, ← Int.cast_sub, phase_real_natAbs421] at hh
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at hh
    dsimp only [I, w, ν]
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type, ← mul_sum]
    let f : ℕ → ℝ := fun k => (n.choose k : ℝ) *
      ∑ u : Fin k → Fin L, ∑ v : Fin (n - k) → Fin L,
        Real.cos (2 * Real.pi *
          (((∑ j : Fin k, (2 : ℤ) ^ (u j : ℕ)) -
            (∑ j : Fin (n - k), (2 : ℤ) ^ (v j : ℕ))).natAbs : ℝ) * x)
    change (2 : ℝ) ^ n * (G L x).re ^ n = ∑ k : Fin (n + 1), f k
    rw [Fin.sum_univ_eq_sum_range f (n + 1)]
    exact hh
  let b : ℕ → ℝ := fun k => c k / (2 : ℝ) ^ n
  have hbp (k : ℕ) : 0 ≤ b k := div_nonneg (hc k) (by positivity)
  have hbf : Function.HasFiniteSupport b := by
    change (Function.support b).Finite
    apply hcf.subset
    intro k hk
    change c k ≠ 0
    intro he
    apply hk
    simp [b, he]
  have hbs : Summable b := hcs.div_const _
  have hbe (x : ℝ) : (G L x).re ^ n =
      ∑' k : ℕ, b k * Real.cos (2 * Real.pi * k * x) := by
    simp_rw [b, div_mul_eq_mul_div]
    rw [tsum_div_const, ← hce x, ← hp x]
    field_simp
  have hbm : (∑' k : ℕ, b k) = (L : ℝ) ^ n := by
    have he := hbe 0
    simpa [G_eq_sum_phase, phase] using he.symm
  exact ⟨b, hbp, hbf, hbs, hbm, hbe⟩

set_option format.width 240
#print axioms phase_real_natAbs421
#print axioms finite_cosine_collect421
#print axioms real_power_cosine_coefficients_proved421

end LeanLab.PlattTrudgian2014
