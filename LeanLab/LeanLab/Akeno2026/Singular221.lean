/-
AI wrote the Lean code. Goldbach is open.
Finite Euler product bounds for the page 7 distribution reduction.
-/
import LeanLab.Akeno2026.Statements
import LeanLab.PNTSieve.MertensProduct

namespace LeanLab.Akeno2026.Singular221
open Finset Real

/-- Page 7 singular series. Finite prime product upper bound for positive N. -/
theorem singSeries_le_inverse_prime_product221 (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    singSeries N ≤ ∏ p ∈ (Finset.Icc 1 M).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  classical
  let P := (Finset.Icc 1 M).filter Nat.Prime
  let b : ℕ → ℝ := fun p => (1 - (1 : ℝ) / p)⁻¹
  have hb : ∀ p ∈ P, 1 ≤ b p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hpos : 0 < 1 - (1 : ℝ) / p := by
      have : (1 : ℝ) / p < 1 := (div_lt_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
      linarith
    exact (one_le_inv₀ hpos).mpr (sub_le_self 1 (by positivity))
  have hterm : ∀ p : Nat.Primes,
      0 ≤ 1 + cp p N / (((p : ℕ).totient : ℝ) ^ 2) ∧
      1 + cp p N / (((p : ℕ).totient : ℝ) ^ 2) ≤ if (p : ℕ) ≤ M then b p else 1 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
    have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
    have hp1 : 0 < ((p : ℕ) : ℝ) - 1 := by linarith
    have ht : ((p : ℕ).totient : ℝ) = ((p : ℕ) : ℝ) - 1 := by
      rw [Nat.totient_prime p.property, Nat.cast_sub p.property.one_le, Nat.cast_one]
    rw [ht]
    have hnon : 0 ≤ 1 + cp p N / ((((p : ℕ) : ℝ) - 1) ^ 2) := by
      unfold cp
      split_ifs
      · positivity
      · have hh : (1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) ≤ 1 :=
          (div_le_one (by positivity)).mpr (by nlinarith)
        simp only [neg_div, one_mul]
        linarith
    refine ⟨hnon, ?_⟩
    split_ifs with hpM
    · have hcp : cp p N ≤ ((p : ℕ) : ℝ) - 1 := by
        unfold cp
        split_ifs <;> linarith
      calc
        _ ≤ 1 + ((((p : ℕ) : ℝ) - 1) / ((((p : ℕ) : ℝ) - 1) ^ 2)) := by
          exact add_le_add le_rfl (div_le_div_of_nonneg_right hcp (sq_nonneg _))
        _ = b p := by
          dsimp [b]
          field_simp
          <;> ring
    · have hpn : ¬ (p : ℕ) ∣ N := by
        intro hh
        exact hpM ((Nat.le_of_dvd hN hh).trans hNM)
      simp only [cp, hpn, ite_false]
      have hh : (-1 : ℝ) / ((((p : ℕ) : ℝ) - 1) ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
      linarith only [hh]
  have hOne : 1 ≤ ∏ p ∈ P, b p := by
    simpa only [Finset.prod_const_one] using
      (Finset.prod_le_prod₀ (s := P) (f := fun _ => (1 : ℝ)) (fun _ _ => by norm_num) hb)
  have hBound : ∀ s : Finset Nat.Primes,
      (∏ p ∈ s, (1 + cp p N / (((p : ℕ).totient : ℝ) ^ 2))) ≤ ∏ p ∈ P, b p := by
    intro s
    calc
      _ ≤ ∏ p ∈ s, if (p : ℕ) ≤ M then b p else 1 :=
        Finset.prod_le_prod₀ (fun p hp => (hterm p).1) (fun p hp => (hterm p).2)
      _ = ∏ p ∈ s.filter (fun p : Nat.Primes => (p : ℕ) ≤ M), b p := by
        rw [Finset.prod_filter]
      _ ≤ _ := by
        let t := s.filter (fun p : Nat.Primes => (p : ℕ) ≤ M)
        let u := t.image (fun p : Nat.Primes => (p : ℕ))
        have heq : (∏ p ∈ t, b p) = ∏ p ∈ u, b p := by
          rw [Finset.prod_image]
          exact fun p hp q hq he => Subtype.ext he
        have hsub : u ⊆ P := by
          intro p hp
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨q.property.one_le, (Finset.mem_filter.mp hq).2⟩, q.property⟩
        rw [heq]
        exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub
          (fun p hp => zero_le_one.trans (hb p (hsub hp))) (fun p hp hn => hb p hp)
  unfold singSeries
  by_cases hm : Multipliable (fun p : Nat.Primes => (1 + cp p N / (((p : ℕ).totient : ℝ) ^ 2)))
  · exact le_of_tendsto' hm.hasProd hBound
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact hOne

/-- Page 7 singular series. Uniform logarithmic upper bound with an explicit constant. -/
theorem singSeries_le_log221 (N : ℕ) (X : ℝ) (hX : 2 ≤ X)
    (hN : 1 ≤ N) (hNX : (N : ℝ) ≤ X) :
    singSeries N ≤ Real.exp 16 * Real.log X := by
  have hX0 : 0 ≤ X := by linarith
  have hNM : N ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0).mpr hNX
  have hM2 : 2 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0).mpr hX
  have hM2R : (2 : ℝ) ≤ (⌊X⌋₊ : ℕ) := by exact_mod_cast hM2
  have hLM : 0 < Real.log (⌊X⌋₊ : ℕ) := Real.log_pos (by linarith)
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogle : Real.log (⌊X⌋₊ : ℕ) ≤ Real.log X := Real.log_le_log (by linarith) (Nat.floor_le hX0)
  have hb := LeanLab.PNTSieve.Mertens.mertens_product_ge ⌊X⌋₊ hM2
  have hb' : Real.exp (-16) / Real.log X ≤
      ∏ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p) :=
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hLM hlogle).trans hb
  calc
    _ ≤ ∏ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ :=
      singSeries_le_inverse_prime_product221 N ⌊X⌋₊ hN hNM
    _ = (∏ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p))⁻¹ := by
      rw [Finset.prod_inv_distrib]
    _ ≤ (Real.exp (-16) / Real.log X)⁻¹ :=
      inv_anti₀ (by positivity) hb'
    _ = _ := by simp [Real.exp_neg, div_eq_mul_inv, mul_comm]

end LeanLab.Akeno2026.Singular221
