/-
P0076, Section 4, page 15, the first inequality of the display after display 4.3,
G_1 of z at least 10^-10 times the product over w < p < z of the inverse of 1 - omega p / p.
Split of leaf_G1_ge_euler_product in NormalizationSplit.lean along the standard Rankin
argument for the truncated sum of a sieve weight of dimension 3/2, reference 10 Chapter 7:
expand the Euler product at the smaller level y = z^(1/K) into a divisor sum, bound the
divisors above z by Rankin's trick, and compare the products at y and at z by Mertens.
Two cited LEAF pieces, a proved Mertens level change and a proved assembly.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NormalizationSplit

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: page 15, the Euler product over w < p at most y in the display after display 4.3 is
the full divisor sum of h over d dividing P of y, and the divisors at most z are among the
terms of G_1 of z. Class MEDIUM. Since 1 + h p equals the inverse of 1 - omega p / p, the
product minus the divisors above z is at most G_1 of z, for 1 at most y at most z. -/
theorem leaf_G1_ge_product_sub_tail :
    ∀ w : ℕ, wBig ≤ w → ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      (∏ p ∈ (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹) -
        ∑ d ∈ (envelopingPrimeProduct w y).divisors.filter (fun d : ℕ => z < (d : ℝ)), envelopingH w d ≤
          envelopingG w 1 z := by
  sorry

/-- LEAF: page 15, the Rankin bound for the divisors of P of y above z with y = z^(1/K),
in the Selberg sieve lower bound for G_1, reference 10 Chapter 7. Class MEDIUM.
With s = 1 / log y the tail is at most z^-s times the product of 1 + h p p^s, and the
Mertens bound for the sum of omega p log p / p makes the ratio of the two products bounded,
so a fixed K makes the tail at most half the product. -/
theorem leaf_rankin_tail :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      ∑ d ∈ (envelopingPrimeProduct w (z ^ (1 / K))).divisors.filter (fun d : ℕ => z < (d : ℝ)),
          envelopingH w d ≤
        (1 / 2) * ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)),
            (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  sorry

/-- For 0 at most x at most 1/2 the inverse of 1 - x is at most exp 2x. -/
theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [inv_le_comm₀ h1 (Real.exp_pos _), ← Real.exp_neg]
  have h2 := Real.add_one_le_exp (2 * x)
  have h3 : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  nlinarith

/-- Page 15, the Mertens comparison of the Euler products at z^(1/K) and at z.
PROVED: the product over z^(1/K) < p at most z, p > w, of the inverse of 1 - omega p / p is at most
exp of 4 times the sum of 1/p there, since omega p is at most 2 and p > 10, and that sum is at most
log K + 4 by the lab's clean mertens2_block in AlmostPrimes/Decomp1528b. -/
theorem euler_product_level_change :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤
        C * ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)),
            (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  intro K hK
  refine ⟨Real.exp (4 * (Real.log K + 4)), Real.exp_pos _, ?_⟩
  intro w hw z hz
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set y := z ^ (1 / K) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hz (by positivity)
  have hyz : y ≤ z := by
    calc y ≤ z ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one hK0]; exact hK)
      _ = z := Real.rpow_one z
  set f : ℕ → ℝ := fun p => (1 - (envelopingOmega w p : ℝ) / p)⁻¹ with hf
  set Fz := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z) with hFz
  set Fy := (range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ y) with hFy
  set G := Fz.filter (fun p : ℕ => y < (p : ℝ)) with hG
  have hsplit : Fz.filter (fun p : ℕ => ¬ y < (p : ℝ)) = Fy := by
    ext p
    simp only [hFz, hFy, mem_filter, mem_range, not_lt]
    constructor
    · rintro ⟨⟨-, hp, hwp, -⟩, hpy⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpy), hp, hwp, hpy⟩
    · rintro ⟨-, hp, hwp, hpy⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor (hpy.trans hyz)), hp, hwp, hpy.trans hyz⟩, hpy⟩
  have hprod : ∏ p ∈ Fz, f p = (∏ p ∈ G, f p) * ∏ p ∈ Fy, f p := by
    rw [← prod_filter_mul_prod_filter_not Fz (fun p : ℕ => y < (p : ℝ)), hsplit]
  -- facts on primes in Fz
  have hx : ∀ p ∈ Fz, 0 ≤ (envelopingOmega w p : ℝ) / p ∧ (envelopingOmega w p : ℝ) / p ≤ 1 / 2 ∧
      (envelopingOmega w p : ℝ) / p ≤ 2 * (1 / (p : ℝ)) := by
    intro p hp
    have h := (mem_filter.mp hp).2
    have h10 : (10 : ℝ) < p := lt_of_le_of_lt hw10 (by exact_mod_cast h.2.1)
    have hω : (envelopingOmega w p : ℝ) ≤ 2 := by
      unfold envelopingOmega; split_ifs <;> norm_num
    refine ⟨by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ (by linarith)]; linarith
    · rw [mul_one_div]; exact div_le_div_of_nonneg_right hω (by linarith)
  have hf0 : ∀ p ∈ Fz, 0 ≤ f p := by
    intro p hp
    have := hx p hp
    simp only [hf]; apply inv_nonneg.mpr; linarith
  have hGexp : ∏ p ∈ G, f p ≤ Real.exp (4 * ∑ p ∈ G, (1 : ℝ) / p) := by
    rw [mul_sum, Real.exp_sum]
    apply prod_le_prod₀ (fun p hp => hf0 p (filter_subset _ _ hp))
    intro p hp
    obtain ⟨h0, h12, h2⟩ := hx p (filter_subset _ _ hp)
    calc f p ≤ Real.exp (2 * ((envelopingOmega w p : ℝ) / p)) := inv_one_sub_le_exp_two_mul h0 h12
      _ ≤ Real.exp (4 * (1 / (p : ℝ))) := Real.exp_le_exp.mpr (by linarith)
  have hFy0 : 0 ≤ ∏ p ∈ Fy, f p := by
    apply prod_nonneg; intro p hp
    rw [← hsplit] at hp
    exact hf0 p (filter_subset _ _ hp)
  -- bound the sum over G by Mertens
  set y' := max y (w : ℝ) with hy'
  have hy'2 : 2 ≤ y' := le_trans (by linarith) (le_max_right y (w : ℝ))
  have hGsum : ∑ p ∈ G, (1 : ℝ) / p ≤ Real.log K + 4 := by
    by_cases hzy : z < y'
    · have hGe : G = ∅ := by
        apply eq_empty_of_forall_notMem
        intro p hp
        have h1 := (mem_filter.mp hp)
        have h2 := (mem_filter.mp h1.1).2
        have hpw : (w : ℝ) < p := by exact_mod_cast h2.2.1
        have : y' < p := max_lt h1.2 hpw
        linarith [h2.2.2]
      rw [hGe, sum_empty]
      have := Real.log_nonneg hK
      linarith
    · push Not at hzy
      have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy'2 hzy
      have hsub : G ⊆ (Ioc ⌊y'⌋₊ ⌊z⌋₊).filter Nat.Prime := by
        intro p hp
        have h1 := (mem_filter.mp hp)
        have h2 := (mem_filter.mp h1.1).2
        have hpw : (w : ℝ) < p := by exact_mod_cast h2.2.1
        have hpy' : y' < p := max_lt h1.2 hpw
        simp only [mem_filter, mem_Ioc]
        refine ⟨⟨?_, Nat.le_floor h2.2.2⟩, h2.1⟩
        exact (Nat.floor_lt (by linarith)).mpr hpy'
      have hle := sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => by positivity : ∀ p ∈ (Ioc ⌊y'⌋₊ ⌊z⌋₊).filter Nat.Prime, p ∉ G → (0 : ℝ) ≤ 1 / p)
      have hlogy' : 1 ≤ Real.log y' := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1)
          (by linarith [Real.exp_one_lt_d9, le_max_right y (w : ℝ)])
      have h4 : 4 / Real.log y' ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hz1 : 1 < z := by linarith
      have hlogz : 0 < Real.log z := Real.log_pos hz1
      have hlogy : Real.log y = Real.log z / K := by
        rw [hy, Real.log_rpow (by linarith)]; ring
      have hll : Real.log (Real.log z) - Real.log (Real.log y') ≤ Real.log K := by
        have hyy' : Real.log y ≤ Real.log y' := Real.log_le_log (by linarith) (le_max_left _ _)
        have hpos : 0 < Real.log z / K := div_pos hlogz hK0
        have : Real.log (Real.log z / K) ≤ Real.log (Real.log y') :=
          Real.log_le_log hpos (by rw [← hlogy]; exact hyy')
        rw [Real.log_div hlogz.ne' hK0.ne'] at this
        linarith
      have := (abs_le.mp hM).2
      linarith
  have hfin : ∏ p ∈ G, f p ≤ Real.exp (4 * (Real.log K + 4)) :=
    hGexp.trans (Real.exp_le_exp.mpr (by linarith))
  change ∏ p ∈ Fz, f p ≤ _ * ∏ p ∈ Fy, f p
  rw [hprod]
  exact mul_le_mul_of_nonneg_right hfin hFy0


/-- The statement of leaf_G1_ge_euler_product, CONDITIONAL ON the two LEAFs above.
G_1 of z is at least the product at y minus the tail, at least half the product at y,
at least the product at z over 2 C. -/
theorem leaf_G1_ge_euler_product_of_leaves :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤ envelopingG w 1 z := by
  obtain ⟨K, hK, HT⟩ := leaf_rankin_tail
  obtain ⟨C, hC, HC⟩ := euler_product_level_change K hK
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro w hw z hz
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hy1 : 1 ≤ z ^ (1 / K) := Real.one_le_rpow hz (by positivity)
  have hyz : z ^ (1 / K) ≤ z := by
    calc z ^ (1 / K) ≤ z ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one hK0]; exact hK)
      _ = z := Real.rpow_one z
  have hA := leaf_G1_ge_product_sub_tail w hw (z ^ (1 / K)) z hy1 hyz
  have hT := HT w hw z hz
  have hCz := HC w hw z hz
  set Ey := ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)), (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  set Ez := ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
    (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  have h1 : 1 / (2 * C) * Ez ≤ 1 / (2 * C) * (C * Ey) :=
    mul_le_mul_of_nonneg_left hCz (by positivity)
  have h2 : 1 / (2 * C) * (C * Ey) = (1 / 2) * Ey := by field_simp
  linarith

end LeanLab.Teravainen2016
