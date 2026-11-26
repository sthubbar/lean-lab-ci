/-
P0101 Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4.
Leaf split of Decomp570a.major_arc_singular_comparison, page 194, proof of Lemma 2.2,
which cites Hu and Yang, reference 2, Lemma 2.2.
The original file is unchanged: this file must import it for R1 and the singular mass,
so the exact parent statement is assembled here as
`major_arc_singular_comparison_of_leaves`.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Flag1737
import LeanLab.PNTSieve.MertensProduct

open Finset Real MeasureTheory

namespace LeanLab.Hathi2021.Decomp570aLeavesMajor

open Decomp319a Decomp570a

/-- Page 193. The shared shift h of a tuple of exponents, the sum of 2 to the power
of each exponent, as in the residuals n minus h of the set A of Lemma 2.1. -/
def shift (n₁ : ℕ) (ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1)) : ℤ :=
  ∑ j, (2 : ℤ) ^ (ν j).val

/-- Page 194, proof of Lemma 2.2. The one dimensional major arc integral of
S times T squared against e of minus alpha m, over the major arcs of page 192. -/
noncomputable def majorIntegral (n₁ n : ℕ) (m : ℤ) : ℂ :=
  ∫ α in Set.Icc (0 : ℝ) 1 ∩ majorOne n₁ n, S n₁ n α * T n₁ n α ^ 2 * e (-(α * (m : ℝ)))

/-- Page 192. G re-indexed over the exponents up to the floor of L. -/
theorem G_eq_fin_floor (n₁ : ℕ) (x : ℝ) :
    G n₁ x = ∑ v : Fin (⌊L n₁⌋₊ + 1), if 4 ≤ v.val then e ((2 : ℝ) ^ v.val * x) else 0 := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => if 4 ≤ v then e ((2 : ℝ) ^ v * x) else 0)]
  unfold G
  rw [← sum_filter]
  apply sum_congr
  · ext v; simp only [mem_Icc, mem_filter, mem_range]; omega
  · intro v _; rfl

/-- Page 194. The one dimensional major arc integrand S T squared e of minus x m. -/
noncomputable def factor (n₁ n : ℕ) (m : ℤ) (x : ℝ) : ℂ :=
  S n₁ n x * T n₁ n x ^ 2 * e (-(x * (m : ℝ)))

/-- Page 193. Pointwise expansion of the integrand over exponent tuples. -/
theorem integrand_eq_tuple_sum (n₁ n₂ : ℕ) (α : ℝ × ℝ) :
    integrand n₁ n₂ α = ∑ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
      if (∀ j, 4 ≤ (ν j).val) then
        factor n₁ n₁ ((n₁ : ℤ) - shift n₁ ν) α.1 * factor n₁ n₂ ((n₂ : ℤ) - shift n₁ ν) α.2
      else 0 := by
  classical
  unfold integrand
  rw [G_eq_fin_floor, Fintype.sum_pow, Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro ν _
  rw [Fintype.prod_ite_zero]
  by_cases hν : ∀ j, 4 ≤ (ν j).val
  · rw [if_pos hν, if_pos hν]
    rw [← e_sum]
    unfold factor
    have hph : e (∑ j, (2 : ℝ) ^ (ν j).val * (α.1 + α.2)) * e (-(α.1 * n₁ + α.2 * n₂)) =
        e (-(α.1 * (((n₁ : ℤ) - shift n₁ ν : ℤ) : ℝ))) *
          e (-(α.2 * (((n₂ : ℤ) - shift n₁ ν : ℤ) : ℝ))) := by
      rw [← e_add, ← e_add]
      congr 1
      unfold shift
      push_cast
      rw [← Finset.sum_mul]
      ring
    calc _ = S n₁ n₁ α.1 * T n₁ n₁ α.1 ^ 2 * S n₁ n₂ α.2 * T n₁ n₂ α.2 ^ 2 *
          (e (∑ j, (2 : ℝ) ^ (ν j).val * (α.1 + α.2)) * e (-(α.1 * n₁ + α.2 * n₂))) := by ring
      _ = _ := by rw [hph]; ring
  · rw [if_neg hν, if_neg hν]; ring

/-- Page 194. The one dimensional integrand is continuous. -/
theorem continuous_factor (n₁ n : ℕ) (m : ℤ) : Continuous (factor n₁ n m) := by
  have he : Continuous e := by unfold e; fun_prop
  unfold factor S T
  fun_prop

/-- Hu page 193 to 194, R1 as defined on page 193, expanded by writing G to
power k as a sum over exponent tuples and splitting the product major arc integral.
P0101, display for R1 page 193. Fubini on the product
of the two one dimensional major arc sets and multinomial expansion. -/
theorem R1_eq_sum_majorIntegral (n₁ n₂ : ℕ) :
    R1 n₁ n₂ = ∑ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
      if (∀ j, 4 ≤ (ν j).val) then
        (majorIntegral n₁ n₁ ((n₁ : ℤ) - shift n₁ ν) *
          majorIntegral n₁ n₂ ((n₂ : ℤ) - shift n₁ ν)).re
      else 0 := by
  classical
  unfold R1 arcIntegral major
  rw [Set.prod_inter_prod]
  simp_rw [integrand_eq_tuple_sum]
  have hA := (measurableSet_Icc (a := (0:ℝ)) (b := 1)).inter (measurableSet_majorOne n₁ n₁)
  have hB := (measurableSet_Icc (a := (0:ℝ)) (b := 1)).inter (measurableSet_majorOne n₁ n₂)
  rw [integral_finsetSum]
  · rw [Complex.re_sum]
    apply sum_congr rfl
    intro ν _
    by_cases hν : ∀ j, 4 ≤ (ν j).val
    · simp only [if_pos hν]
      congr 1
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod_mul (factor n₁ n₁ ((n₁ : ℤ) - shift n₁ ν))
        (factor n₁ n₂ ((n₂ : ℤ) - shift n₁ ν))
    · simp [hν]
  · intro ν _
    have hc : Continuous (fun α : ℝ × ℝ => if (∀ j, 4 ≤ (ν j).val) then
        factor n₁ n₁ ((n₁ : ℤ) - shift n₁ ν) α.1 * factor n₁ n₂ ((n₂ : ℤ) - shift n₁ ν) α.2
      else 0) := by
      split_ifs
      · exact ((continuous_factor _ _ _).comp continuous_fst).mul
          ((continuous_factor _ _ _).comp continuous_snd)
      · exact continuous_const
    have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    exact (hc.continuousOn.integrableOn_compact hK).mono_set
      (Set.prod_mono Set.inter_subset_left Set.inter_subset_left)


/-- LEAF: Hu page 194, proof of Lemma 2.2, the one dimensional major arc asymptotic
of Hu and Yang reference 2 Lemma 2.2: the integral equals the singular integral pi m
over 4 times the singular series of m, up to o of N over log log N1, uniformly for
residuals m between N minus 82 N1 over log N1 and N.
Class HARD. P0101 page 194 display, reference 2 Lemma 2.2. -/
theorem majorIntegral_asymptotic_residual (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n : ℕ, N₀ ≤ n → n ≤ n₁ → (n₁ : ℝ) ≤ C * n →
      ∀ m : ℤ, (n : ℝ) - 82 * ((n₁ : ℝ) / Real.log n₁) ≤ m → m ≤ (n : ℤ) →
        ‖majorIntegral n₁ n m - ((Real.pi / 4 * m * singularSeries m : ℝ) : ℂ)‖ ≤
          η * n / Real.log (Real.log n₁) := by
  sorry



section LocalFactors702

open scoped Classical
/-- Hu page 193. Match the standard modular character with the paper exponential. -/
theorem stdAddChar_eq_e_int (q : ℕ) [NeZero q] (z : ℤ) :
    ZMod.stdAddChar (z : ZMod q) = e ((z : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe]
  unfold e
  push_cast
  congr 1
  ring






/-- Hu page 193. Reindex the coprime residues from 1 through q by modular units. -/
theorem sum_coprime_eq_sum_units (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (f : ZMod q → ℂ) :
    (∑ m ∈ (Finset.Icc 1 q).filter (fun m => Nat.Coprime m q), f m) =
      ∑ x : (ZMod q)ˣ, f x := by
  classical
  letI : Fact (1 < q) := ⟨by omega⟩
  apply Finset.sum_bij (fun (m : ℕ) hm => ZMod.unitOfCoprime m (Finset.mem_filter.mp hm).2)
  · intro m hm; exact Finset.mem_univ _
  · intro m hm k hk heq
    have hlt (v : ℕ) (hv : v ∈ (Finset.Icc 1 q).filter (fun m => Nat.Coprime m q)) : v < q := by
      have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
      have hc := (Finset.mem_filter.mp hv).2
      have hn : v ≠ q := by intro he; subst v; simp at hc; omega
      omega
    have hv := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q).val) heq
    simpa [ZMod.val_natCast_of_lt (hlt m hm), ZMod.val_natCast_of_lt (hlt k hk)] using hv
  · intro x hx
    have hpos : 0 < (x : ZMod q).val := ZMod.val_pos.mpr (Units.ne_zero x)
    refine ⟨(x : ZMod q).val, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpos, (ZMod.val_lt _).le⟩, ZMod.val_coe_unit_coprime x⟩, ?_⟩
    apply Units.ext
    simp
  · intro m hm
    simp

/-- Hu page 193. Express C of degree d as a sum of standard characters over units. -/
theorem residueSum_eq_sum_units (q a d : ℕ) [NeZero q] (hq : 2 ≤ q) :
    residueSum q a d = ∑ x : (ZMod q)ˣ,
      ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q) ^ d) := by
  unfold residueSum
  convert sum_coprime_eq_sum_units q hq (fun x => ZMod.stdAddChar ((a : ZMod q) * x ^ d)) using 1
  apply Finset.sum_congr rfl
  intro m hm
  have hc : (a : ZMod q) * (m : ZMod q) ^ d = ((a : ℤ) * (m : ℤ) ^ d : ℤ) := by push_cast; rfl
  rw [hc, stdAddChar_eq_e_int]
  push_cast
  rfl



/-- Hu page 193. Finite orthogonality counts two unit squares and one unit.
This is a finite density identity for every positive modulus. -/
theorem unit_fourier_count (q : ℕ) [NeZero q] (r : ℤ) :
    (∑ a : ZMod q,
      (∑ x : (ZMod q)ˣ, ZMod.stdAddChar (a * (x : ZMod q))) *
      (∑ y : (ZMod q)ˣ, ZMod.stdAddChar (a * (y : ZMod q) ^ 2)) ^ 2 *
      ZMod.stdAddChar (-a * (r : ZMod q))) =
    ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ, ∑ z : (ZMod q)ˣ,
      if (x : ZMod q) ^ 2 + (y : ZMod q) ^ 2 + (z : ZMod q) = (r : ZMod q)
      then (q : ℂ) else 0 := by
  classical
  have hterm (a : ZMod q) :
      (∑ x : (ZMod q)ˣ, ZMod.stdAddChar (a * (x : ZMod q))) *
      (∑ y : (ZMod q)ˣ, ZMod.stdAddChar (a * (y : ZMod q) ^ 2)) ^ 2 *
      ZMod.stdAddChar (-a * (r : ZMod q)) =
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ, ∑ z : (ZMod q)ˣ,
        ZMod.stdAddChar (a * ((x : ZMod q) ^ 2 + (y : ZMod q) ^ 2 + (z : ZMod q) - (r : ZMod q))) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have h := AddChar.sum_mulShift
    ((x : ZMod q) ^ 2 + (y : ZMod q) ^ 2 + (z : ZMod q) - (r : ZMod q))
    (ZMod.isPrimitive_stdAddChar q)
  have hc : (∑ a : ZMod q, ZMod.stdAddChar
      (a * ((x : ZMod q) ^ 2 + (y : ZMod q) ^ 2 + (z : ZMod q) - (r : ZMod q)))) =
      if (x : ZMod q) ^ 2 + (y : ZMod q) ^ 2 + (z : ZMod q) - (r : ZMod q) = 0
      then (q : ℂ) else 0 := by
    simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using h
  simpa only [sub_eq_zero] using hc



/-- Hu page 193. At a prime modulus the units and zero partition all residues. -/
theorem sum_units_add_zero (p : ℕ) [Fact p.Prime] (f : ZMod p → ℂ) :
    (∑ u : (ZMod p)ˣ, f u) + f 0 = ∑ x : ZMod p, f x := by
  classical
  have hu : (∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, f x) =
      ∑ u : (ZMod p)ˣ, f u := by
    calc _ = ∑ x : {x : ZMod p // x ≠ 0}, f x :=
          Finset.sum_subtype _ (by simp) f
      _ = _ := (Fintype.sum_equiv unitsEquivNeZero _ _ (fun x => rfl)).symm
  rw [← hu]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ _)

/-- Hu page 193. Reindex the exact coefficient A using modular units. -/
theorem singularCoefficient_eq_units (q : ℕ) [NeZero q] (hq : 2 ≤ q) (r : ℤ) :
    singularCoefficient r q =
      (∑ a : (ZMod q)ˣ,
        (∑ x : (ZMod q)ˣ, ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))) *
        (∑ y : (ZMod q)ˣ, ZMod.stdAddChar ((a : ZMod q) * (y : ZMod q) ^ 2)) ^ 2 *
        ZMod.stdAddChar (-(a : ZMod q) * (r : ZMod q))) / (Nat.totient q : ℂ) ^ 3 := by
  unfold singularCoefficient
  simp_rw [residueSum_eq_sum_units q _ _ hq, pow_one]
  congr 1
  convert sum_coprime_eq_sum_units q hq (fun a =>
        (∑ x : (ZMod q)ˣ, ZMod.stdAddChar (a * (x : ZMod q))) *
        (∑ y : (ZMod q)ˣ, ZMod.stdAddChar (a * (y : ZMod q) ^ 2)) ^ 2 *
        ZMod.stdAddChar (-a * (r : ZMod q))) using 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  have hc : -(a : ZMod q) * (r : ZMod q) = (-(a : ℤ) * r : ℤ) := by push_cast; rfl
  rw [hc, stdAddChar_eq_e_int]
  congr 1
  push_cast
  ring



/-- Hu page 193. One plus A at a prime equals its normalized local density.
The first two unit variables are squared and the third unit variable is linear. -/
theorem prime_local_factor_eq_density (p : ℕ) [Fact p.Prime] (r : ℤ) :
    (1 : ℂ) + singularCoefficient r p =
      (∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ, ∑ z : (ZMod p)ˣ,
        if (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 + (z : ZMod p) = (r : ZMod p)
        then (p : ℂ) else 0) / (Nat.totient p : ℂ) ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  let F (a : ZMod p) : ℂ :=
      (∑ x : (ZMod p)ˣ, ZMod.stdAddChar (a * (x : ZMod p))) *
      (∑ y : (ZMod p)ˣ, ZMod.stdAddChar (a * (y : ZMod p) ^ 2)) ^ 2 *
      ZMod.stdAddChar (-a * (r : ZMod p))
  have hF : F 0 = (Nat.totient p : ℂ) ^ 3 := by
    simp [F, ZMod.card_units_eq_totient]
    ring
  have hsplit := sum_units_add_zero p F
  rw [hF] at hsplit
  rw [singularCoefficient_eq_units p hp.two_le r]
  change 1 + (∑ a : (ZMod p)ˣ, F a) / (Nat.totient p : ℂ) ^ 3 = _
  have ht : (Nat.totient p : ℂ) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne')
  rw [← unit_fourier_count p r]
  change 1 + (∑ a : (ZMod p)ˣ, F a) / (Nat.totient p : ℂ) ^ 3 =
    (∑ a : ZMod p, F a) / (Nat.totient p : ℂ) ^ 3
  rw [← hsplit]
  rw [add_div, div_self ht]
  ring



/-- Hu page 193. Every prime local factor has nonnegative real part.
This finite statement does not identify the infinite series with an Euler product. -/
theorem prime_local_factor_nonneg (p : ℕ) [Fact p.Prime] (r : ℤ) :
    0 ≤ 1 + (singularCoefficient r p).re := by
  classical
  have h := congrArg Complex.re (prime_local_factor_eq_density p r)
  simp only [Complex.add_re, Complex.one_re] at h
  rw [h]
  have hden : (Nat.totient p : ℂ) ^ 3 = (((Nat.totient p : ℝ) ^ 3 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hden, Complex.div_ofReal_re]
  apply div_nonneg _ (by positivity)
  simp only [Complex.re_sum]
  apply Finset.sum_nonneg
  intro x hx
  apply Finset.sum_nonneg
  intro y hy
  apply Finset.sum_nonneg
  intro z hz
  split_ifs <;> simp

/-- Hu page 193. One finite certificate for the unit residues at 2 and 3.
It supplies the small prime steps for every integer residual. -/
theorem small_prime_units : (∀ x : (ZMod 2)ˣ, (x : ZMod 2) = 1) ∧
    (∀ x : (ZMod 3)ˣ, (x : ZMod 3) ^ 2 = 1) := by decide +kernel

/-- Hu page 193. The local factor at 2 is 2 on odd residuals and 0 on even residuals. -/
theorem prime_local_factor_two (r : ℤ) :
    (1 : ℂ) + singularCoefficient r 2 = if (r : ZMod 2) = 1 then 2 else 0 := by
  classical
  rw [prime_local_factor_eq_density]
  norm_num [small_prime_units.1, ZMod.card_units_eq_totient, eq_comm]
  congr 2

/-- Hu page 193. The local factor at 3 vanishes on residuals congruent to 2 modulo 3. -/
theorem prime_local_factor_three_zero (r : ℤ) (hr : (r : ZMod 3) = 2) :
    (1 : ℂ) + singularCoefficient r 3 = 0 := by
  classical
  rw [prime_local_factor_eq_density]
  have hn (x y z : (ZMod 3)ˣ) :
      (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 + (z : ZMod 3) ≠ (r : ZMod 3) := by
    rw [small_prime_units.2 x, small_prime_units.2 y, hr]
    intro he
    apply Units.ne_zero z
    linear_combination he
  simp only [ite_eq_right (hn _ _ _), Finset.sum_const_zero, zero_div]

/-- Hu page 193. The product of the real prime local factors is nonnegative.
No equality with the sealed series definition is asserted here. -/
theorem prime_local_product_nonneg (r : ℤ) :
    0 ≤ ∏' p : Nat.Primes, (1 + (singularCoefficient r p.val).re) := by
  apply tprod_nonneg
  intro p
  letI : Fact p.val.Prime := ⟨p.prop⟩
  exact prime_local_factor_nonneg p.val r

/-- Hu page 193. Every prime local factor is at most p divided by phi of p.
This bound alone does not imply a log log bound for the infinite series. -/
theorem prime_local_factor_le_totient (p : ℕ) [Fact p.Prime] (r : ℤ) :
    1 + (singularCoefficient r p).re ≤ (p : ℝ) / Nat.totient p := by
  classical
  have hz (b : ZMod p) :
      (∑ z : (ZMod p)ˣ, if (z : ZMod p) = b then (p : ℝ) else 0) ≤ p := by
    calc _ = ∑ z ∈ (Finset.univ : Finset (ZMod p)ˣ).image (fun (z : (ZMod p)ˣ) => (z : ZMod p)),
          if z = b then (p : ℝ) else 0 := by
            symm
            apply Finset.sum_image
            intro x hx y hy he
            exact Units.ext he
      _ ≤ ∑ z : ZMod p, if z = b then (p : ℝ) else 0 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
          intro z hz hn
          split_ifs <;> positivity)
      _ = p := by simp
  have h := congrArg Complex.re (prime_local_factor_eq_density p r)
  simp only [Complex.add_re, Complex.one_re] at h
  rw [h]
  have hden : (Nat.totient p : ℂ) ^ 3 = (((Nat.totient p : ℝ) ^ 3 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hden, Complex.div_ofReal_re]
  have hphi : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast Nat.totient_pos.mpr (Fact.out : p.Prime).pos
  have hsum :
      ((∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ, ∑ z : (ZMod p)ˣ,
        if (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 + (z : ZMod p) = (r : ZMod p)
        then (p : ℂ) else 0) : ℂ).re ≤ (Nat.totient p : ℝ) ^ 2 * p := by
    simp only [Complex.re_sum, apply_ite Complex.re, Complex.natCast_re, Complex.zero_re]
    calc _ ≤ ∑ _x : (ZMod p)ˣ, ∑ _y : (ZMod p)ˣ, (p : ℝ) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          convert hz ((r : ZMod p) - (x : ZMod p) ^ 2 - (y : ZMod p) ^ 2) using 1
          apply Finset.sum_congr rfl
          intro z hz
          congr 1
          apply propext
          constructor <;> intro he <;> linear_combination he
      _ = _ := by simp [ZMod.card_units_eq_totient]; ring
  calc _ ≤ ((Nat.totient p : ℝ) ^ 2 * p) / (Nat.totient p : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by field_simp


/-- Hu page 193. The denominator one term of the singular series is 1. -/
theorem singularCoefficient_one (r : ℤ) : singularCoefficient r 1 = 1 := by
  have he (z : ℤ) : e (z : ℝ) = 1 := by
    have h := stdAddChar_eq_e_int 1 z
    have hz : (z : ZMod 1) = 0 := Subsingleton.elim _ _
    simpa only [hz, AddChar.map_zero_eq_one, Nat.cast_one, div_one] using h.symm
  have he1 : e 1 = 1 := by simpa using he 1
  have hen : e (-(r : ℝ)) = 1 := by simpa using he (-r)
  simp [singularCoefficient, residueSum, he1, hen]


/-- Hu page 193. The printed linear residue sum C1 equals minus one at a prime
when the frequency is coprime to that prime. -/
theorem residueSum_prime_linear (p a : ℕ) [Fact p.Prime] (ha : Nat.Coprime a p) :
    residueSum p a 1 = -1 := by
  classical
  have hp : p.Prime := Fact.out
  have ha0 : (a : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime a p).2 ha).ne_zero
  have hs := sum_units_add_zero p (fun x => ZMod.stdAddChar ((a : ZMod p) * x))
  have hf : (∑ x : ZMod p, ZMod.stdAddChar ((a : ZMod p) * x)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha0, Nat.cast_zero] using
      AddChar.sum_mulShift (a : ZMod p) (ZMod.isPrimitive_stdAddChar p)
  rw [hf] at hs
  simp only [mul_zero, AddChar.map_zero_eq_one] at hs
  rw [residueSum_eq_sum_units p a 1 hp.two_le]
  simp only [pow_one]
  linear_combination hs


/-- Hu page 193. Reindex a unit sum as a sum over all residues with the unit indicator. -/
theorem sum_units_eq_sum_isUnit (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ u : (ZMod q)ˣ, f u) = ∑ x : ZMod q, if IsUnit x then f x else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q))
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
  · intro u hu v hv he
    exact Units.ext he
  · intro x hx
    have hu := (Finset.mem_filter.mp hx).2
    exact ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
  · intro u hu
    rfl

/-- Hu page 193. Finite cancellation under translation by a nilpotent residue.
If the translation phase differs from 1, the unit character sum vanishes. -/
theorem unit_character_sum_eq_zero_of_nilpotent (q : ℕ) [NeZero q]
    (a b : ZMod q) (hb : IsNilpotent b) (hphase : ZMod.stdAddChar (a * b) ≠ 1) :
    (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) = 0 := by
  classical
  have hu (x : ZMod q) : IsUnit (x + b) ↔ IsUnit x := by
    constructor
    · intro hx
      have h := hb.neg.isUnit_add_left_of_commute hx (Commute.all _ _)
      simpa using h
    · intro hx
      exact hb.isUnit_add_left_of_commute hx (Commute.all _ _)
  rw [sum_units_eq_sum_isUnit q (fun x => ZMod.stdAddChar (a * x))]
  let f (x : ZMod q) : ℂ := if IsUnit x then ZMod.stdAddChar (a * x) else 0
  have hs := Equiv.sum_comp (Equiv.addRight b) f
  change (∑ x : ZMod q, f (x + b)) = ∑ x : ZMod q, f x at hs
  have hx (x : ZMod q) : f (x + b) = f x * ZMod.stdAddChar (a * b) := by
    dsimp only [f]
    simp only [hu, mul_add, AddChar.map_add_eq_mul]
    split_ifs <;> simp
  simp_rw [hx] at hs
  rw [← Finset.sum_mul] at hs
  have hzero : (∑ x : ZMod q, f x) * (ZMod.stdAddChar (a * b) - 1) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hphase)

/-- Hu page 193. The linear residue sum is zero at prime powers with exponent
at least two and frequencies coprime to the modulus. -/
theorem residueSum_prime_power_linear (p k a : ℕ) [Fact p.Prime]
    (ha : Nat.Coprime a (p ^ (k + 2))) :
    residueSum (p ^ (k + 2)) a 1 = 0 := by
  classical
  have hp : p.Prime := Fact.out
  let q := p ^ (k + 2)
  letI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  let b : ZMod q := (p ^ (k + 1) : ℕ)
  have hb : IsNilpotent b := by
    refine ⟨2, ?_⟩
    have hd : p ^ (k + 2) ∣ (p ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    change ((p ^ (k + 1) : ℕ) : ZMod q) ^ 2 = 0
    rw [← Nat.cast_pow]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hd
  have hb0 : b ≠ 0 := by
    have hlt : p ^ (k + 1) < q := by
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    intro he
    have he' := congrArg ZMod.val he
    change (((p ^ (k + 1) : ℕ) : ZMod q)).val = (0 : ZMod q).val at he'
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at he'
    exact (pow_pos hp.pos _).ne' he'
  have hau : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hphase : ZMod.stdAddChar ((a : ZMod q) * b) ≠ 1 := by
    intro he
    have hz : (a : ZMod q) * b = 0 := ZMod.injective_stdAddChar (by simpa using he)
    apply hb0
    exact hau.mul_left_cancel (by simpa using hz)
  rw [residueSum_eq_sum_units _ _ _ (by exact Nat.one_lt_pow (by omega) hp.one_lt)]
  simp only [pow_one]
  exact unit_character_sum_eq_zero_of_nilpotent q (a : ZMod q) b hb hphase



/-- Hu page 193. Every coefficient A at a prime power with exponent at least two is zero. -/
theorem singularCoefficient_prime_power (p k : ℕ) [Fact p.Prime] (r : ℤ) :
    singularCoefficient r (p ^ (k + 2)) = 0 := by
  classical
  unfold singularCoefficient
  have hs : (∑ a ∈ (Finset.Icc 1 (p ^ (k + 2))).filter
      (fun a => Nat.Coprime a (p ^ (k + 2))),
      residueSum (p ^ (k + 2)) a 1 * residueSum (p ^ (k + 2)) a 2 ^ 2 *
        LeanLab.Hathi2021.Decomp319a.e (-(a : ℝ) * r / (p ^ (k + 2)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [residueSum_prime_power_linear p k a (Finset.mem_filter.mp ha).2, zero_mul, zero_mul]
  simp only [Nat.cast_pow]
  rw [hs, zero_div]

/-- Hu page 193. Split an integer frequency character across two positive moduli
using an integer Bezout identity. -/
theorem stdAddChar_mul_moduli (m n : ℕ) [NeZero m] [NeZero n] (u v z : ℤ)
    (hbez : u * (m : ℤ) + v * (n : ℤ) = 1) :
    ZMod.stdAddChar (z : ZMod (m * n)) =
      ZMod.stdAddChar ((v * z : ℤ) : ZMod m) * ZMod.stdAddChar ((u * z : ℤ) : ZMod n) := by
  rw [stdAddChar_eq_e_int, stdAddChar_eq_e_int, stdAddChar_eq_e_int, ← e_add]
  congr 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hbez' : (u : ℝ) * m + (v : ℝ) * n = 1 := by exact_mod_cast hbez
  push_cast
  field_simp
  linear_combination -(z : ℝ) * hbez'


/-- Hu page 193. The residue sum C with its frequency indexed in ZMod. -/
noncomputable def unitExpSum (q : ℕ) [NeZero q] (a : ZMod q) (d : ℕ) : ℂ :=
  ∑ x : (ZMod q)ˣ, ZMod.stdAddChar (a * (x : ZMod q) ^ d)


/-- Hu page 193. The standard character factors through the Chinese remainder projections
with the Bezout frequency weights. -/
theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    (u v : ℤ) (hbez : u * (m : ℤ) + v * (n : ℤ) = 1) (z : ZMod (m * n)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((v : ZMod m) * (ZMod.chineseRemainder hmn z).1) *
      ZMod.stdAddChar ((u : ZMod n) * (ZMod.chineseRemainder hmn z).2) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective z
  simpa only [map_intCast, Prod.fst_intCast, Prod.snd_intCast, Int.cast_mul] using
    stdAddChar_mul_moduli m n u v z hbez


/-- Hu page 193. The unit residue sum factors across coprime moduli
with the Bezout frequency weights. -/
theorem unitExpSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    (u v : ℤ) (hbez : u * (m : ℤ) + v * (n : ℤ) = 1) (a : ZMod (m * n)) (d : ℕ) :
    unitExpSum (m * n) a d =
      unitExpSum m ((v : ZMod m) * (ZMod.chineseRemainder hmn a).1) d *
      unitExpSum n ((u : ZMod n) * (ZMod.chineseRemainder hmn a).2) d := by
  classical
  let e := (Units.mapEquiv (ZMod.chineseRemainder hmn).toMulEquiv).trans MulEquiv.prodUnits
  unfold unitExpSum
  calc (∑ x : (ZMod (m * n))ˣ, ZMod.stdAddChar (a * (x : ZMod (m * n)) ^ d)) =
      ∑ xy : (ZMod m)ˣ × (ZMod n)ˣ,
        ZMod.stdAddChar (a * ((e.symm xy : (ZMod (m * n))ˣ) : ZMod (m * n)) ^ d) :=
        (Equiv.sum_comp e.toEquiv.symm _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      have he : ZMod.chineseRemainder hmn
          ((e.symm (x, y) : (ZMod (m * n))ˣ) : ZMod (m * n)) =
          ((x : ZMod m), (y : ZMod n)) := by
        exact congrArg (fun xy : (ZMod m)ˣ × (ZMod n)ˣ =>
          ((xy.1 : ZMod m), (xy.2 : ZMod n))) (e.apply_symm_apply (x, y))
      rw [stdAddChar_crt m n hmn u v hbez]
      simp only [map_mul, map_pow, he, Prod.fst_mul, Prod.snd_mul]
      change ZMod.stdAddChar ((v : ZMod m) * ((ZMod.chineseRemainder hmn a).1 * (x : ZMod m) ^ d)) *
        ZMod.stdAddChar ((u : ZMod n) * ((ZMod.chineseRemainder hmn a).2 * (y : ZMod n) ^ d)) = _
      congr 1 <;> congr 1 <;> ring


/-- Hu page 193. The exact coefficient A is multiplicative for two moduli at least two.
This form carries the integer Bezout coefficients explicitly. -/
theorem singularCoefficient_mul_of_bezout (m n : ℕ) [NeZero m] [NeZero n]
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : Nat.Coprime m n)
    (u v : ℤ) (hbez : u * (m : ℤ) + v * (n : ℤ) = 1) (r : ℤ) :
    singularCoefficient r (m * n) = singularCoefficient r m * singularCoefficient r n := by
  classical
  let F (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
    unitExpSum q a 1 * unitExpSum q a 2 ^ 2 * ZMod.stdAddChar (-a * (r : ZMod q))
  have hFm : singularCoefficient r m = (∑ a : (ZMod m)ˣ, F m a) / (Nat.totient m : ℂ) ^ 3 := by
    simpa only [F, unitExpSum, pow_one] using singularCoefficient_eq_units m hm r
  have hFn : singularCoefficient r n = (∑ a : (ZMod n)ˣ, F n a) / (Nat.totient n : ℂ) ^ 3 := by
    simpa only [F, unitExpSum, pow_one] using singularCoefficient_eq_units n hn r
  have hFmn : singularCoefficient r (m * n) =
      (∑ a : (ZMod (m * n))ˣ, F (m * n) a) / (Nat.totient (m * n) : ℂ) ^ 3 := by
    simpa only [F, unitExpSum, pow_one] using
      singularCoefficient_eq_units (m * n) (by nlinarith) r
  have hv : (v : ZMod m) * (n : ZMod m) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_self, mul_zero, zero_add] using h
  have hu : (u : ZMod n) * (m : ZMod n) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod n)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_self, mul_zero, add_zero] using h
  let vm : (ZMod m)ˣ := ⟨v, n, hv, by rw [mul_comm]; exact hv⟩
  let un : (ZMod n)ˣ := ⟨u, m, hu, by rw [mul_comm]; exact hu⟩
  have hvm : (∑ x : (ZMod m)ˣ, F m ((v : ZMod m) * (x : ZMod m))) =
      ∑ x : (ZMod m)ˣ, F m x := by
    exact Equiv.sum_comp (Equiv.mulLeft vm) (fun x : (ZMod m)ˣ => F m x)
  have hun : (∑ x : (ZMod n)ˣ, F n ((u : ZMod n) * (x : ZMod n))) =
      ∑ x : (ZMod n)ˣ, F n x := by
    exact Equiv.sum_comp (Equiv.mulLeft un) (fun x : (ZMod n)ˣ => F n x)
  have hF (a : ZMod (m * n)) : F (m * n) a =
      F m ((v : ZMod m) * (ZMod.chineseRemainder hmn a).1) *
      F n ((u : ZMod n) * (ZMod.chineseRemainder hmn a).2) := by
    unfold F
    rw [unitExpSum_crt m n hmn u v hbez a 1,
      unitExpSum_crt m n hmn u v hbez a 2, stdAddChar_crt m n hmn u v hbez]
    simp only [map_mul, map_neg, map_intCast, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_neg, Prod.snd_neg, Prod.fst_intCast, Prod.snd_intCast]
    have hmphase : (v : ZMod m) * (-((ZMod.chineseRemainder hmn a).1) * (r : ZMod m)) =
        -((v : ZMod m) * (ZMod.chineseRemainder hmn a).1) * (r : ZMod m) := by ring
    have hnphase : (u : ZMod n) * (-((ZMod.chineseRemainder hmn a).2) * (r : ZMod n)) =
        -((u : ZMod n) * (ZMod.chineseRemainder hmn a).2) * (r : ZMod n) := by ring
    rw [hmphase, hnphase]
    ring
  let e := (Units.mapEquiv (ZMod.chineseRemainder hmn).toMulEquiv).trans MulEquiv.prodUnits
  have hsum : (∑ a : (ZMod (m * n))ˣ, F (m * n) a) =
      (∑ a : (ZMod m)ˣ, F m a) * (∑ a : (ZMod n)ˣ, F n a) := by
    calc _ = ∑ xy : (ZMod m)ˣ × (ZMod n)ˣ, F (m * n) (e.symm xy) :=
          (Equiv.sum_comp e.toEquiv.symm _).symm
      _ = (∑ x : (ZMod m)ˣ, F m ((v : ZMod m) * (x : ZMod m))) *
          (∑ y : (ZMod n)ˣ, F n ((u : ZMod n) * (y : ZMod n))) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        have he : ZMod.chineseRemainder hmn
            ((e.symm (x, y) : (ZMod (m * n))ˣ) : ZMod (m * n)) =
            ((x : ZMod m), (y : ZMod n)) := by
          exact congrArg (fun xy : (ZMod m)ˣ × (ZMod n)ˣ =>
            ((xy.1 : ZMod m), (xy.2 : ZMod n))) (e.apply_symm_apply (x, y))
        rw [hF, he]
      _ = _ := by rw [hvm, hun]
  rw [hFmn, hFm, hFn, hsum, Nat.totient_mul hmn, Nat.cast_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _


/-- Hu page 193. The sealed coefficient definition extends to zero modulus with value zero.
The paper series itself starts at denominator one. -/
theorem singularCoefficient_zero (r : ℤ) : singularCoefficient r 0 = 0 := by
  simp [singularCoefficient, residueSum]


/-- Hu page 193. The exact coefficient A is multiplicative on coprime moduli,
including its zero and one extensions. -/
theorem singularCoefficient_multiplicative (r : ℤ) (m n : ℕ) (hmn : Nat.Coprime m n) :
    singularCoefficient r (m * n) = singularCoefficient r m * singularCoefficient r n := by
  by_cases hm0 : m = 0
  · subst m; simp [singularCoefficient_zero]
  by_cases hn0 : n = 0
  · subst n; simp [singularCoefficient_zero]
  by_cases hm1 : m = 1
  · subst m; simp [singularCoefficient_one]
  by_cases hn1 : n = 1
  · subst n; simp [singularCoefficient_one]
  letI : NeZero m := ⟨hm0⟩
  letI : NeZero n := ⟨hn0⟩
  have hbez := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one] at hbez
  apply singularCoefficient_mul_of_bezout m n (by omega) (by omega) hmn
    (Nat.gcdA m n) (Nat.gcdB m n) _ r
  linear_combination -hbez


/-- Hu page 193. A prime local factor equals the complex embedding of its real part. -/
theorem prime_local_factor_real (p : ℕ) [Fact p.Prime] (r : ℤ) :
    (1 : ℂ) + singularCoefficient r p = ((1 + (singularCoefficient r p).re : ℝ) : ℂ) := by
  have him : ((1 : ℂ) + singularCoefficient r p).im = 0 := by
    rw [prime_local_factor_eq_density]
    have hden : (Nat.totient p : ℂ) ^ 3 = (((Nat.totient p : ℝ) ^ 3 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hden, Complex.div_ofReal_im]
    simp only [Complex.im_sum, apply_ite Complex.im, Complex.natCast_im,
      Complex.zero_im, ite_self, Finset.sum_const_zero, zero_div]
  apply Complex.ext
  · simp
  · simpa using him


/-- Hu page 193. The prime power series equals one plus A at the prime.
All higher prime power terms vanish. -/
theorem prime_power_series (p : ℕ) [Fact p.Prime] (r : ℤ) :
    (∑' k : ℕ, singularCoefficient r (p ^ k)) = (1 : ℂ) + singularCoefficient r p := by
  calc _ = ∑ k ∈ ({0, 1} : Finset ℕ), singularCoefficient r (p ^ k) := by
          apply tsum_eq_sum
          intro k hk
          have hk2 : 2 ≤ k := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            omega
          obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk2
          simpa only [Nat.add_comm] using singularCoefficient_prime_power p l r
    _ = _ := by simp [singularCoefficient_one]


/-- Hu page 193. At modulus one, every frequency and degree residue sum is 1. -/
theorem residueSum_modulus_one (a d : ℕ) : residueSum 1 a d = 1 := by
  have he : e (a : ℝ) = 1 := by
    have h := stdAddChar_eq_e_int 1 (a : ℤ)
    have hz : ((a : ℤ) : ZMod 1) = 0 := Subsingleton.elim _ _
    simpa only [hz, AddChar.map_zero_eq_one, Nat.cast_one, div_one, Int.cast_natCast] using h.symm
  simp [residueSum, he]

/-- Hu page 193. A coprime frequency does not change the linear residue sum. -/
theorem residueSum_linear_frequency (q a : ℕ) (ha : Nat.Coprime a q) :
    residueSum q a 1 = residueSum q 1 1 := by
  by_cases hq0 : q = 0
  · subst q; simp [residueSum]
  by_cases hq1 : q = 1
  · subst q; simp [residueSum_modulus_one]
  letI : NeZero q := ⟨hq0⟩
  rw [residueSum_eq_sum_units q a 1 (by omega), residueSum_eq_sum_units q 1 1 (by omega)]
  simp only [pow_one, Nat.cast_one, one_mul]
  let au := ZMod.unitOfCoprime a ha
  exact Equiv.sum_comp (Equiv.mulLeft au) (fun x : (ZMod q)ˣ => ZMod.stdAddChar (x : ZMod q))

/-- Hu page 193. The linear residue sum at frequency one is multiplicative on coprime moduli. -/
theorem residueSum_linear_multiplicative (m n : ℕ) (hmn : Nat.Coprime m n) :
    residueSum (m * n) 1 1 = residueSum m 1 1 * residueSum n 1 1 := by
  classical
  by_cases hm0 : m = 0
  · subst m; simp [residueSum]
  by_cases hn0 : n = 0
  · subst n; simp [residueSum]
  by_cases hm1 : m = 1
  · subst m; simp [residueSum_modulus_one]
  by_cases hn1 : n = 1
  · subst n; simp [residueSum_modulus_one]
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  letI : NeZero m := ⟨hm0⟩
  letI : NeZero n := ⟨hn0⟩
  let u := Nat.gcdA m n
  let v := Nat.gcdB m n
  have hbez : u * (m : ℤ) + v * (n : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [hmn.gcd_eq_one] at h
    dsimp [u, v]
    linear_combination -h
  have hvn : (v : ZMod m) * (n : ZMod m) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_self, mul_zero, zero_add] using h
  have hum : (u : ZMod n) * (m : ZMod n) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod n)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_self, mul_zero, add_zero] using h
  have hv : IsUnit (v : ZMod m) := IsUnit.of_mul_eq_one (n : ZMod m) hvn
  have hu : IsUnit (u : ZMod n) := IsUnit.of_mul_eq_one (m : ZMod n) hum
  have hf (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
      unitExpSum q (a : ZMod q) 1 = unitExpSum q 1 1 := by
    unfold unitExpSum
    simp only [pow_one, one_mul]
    exact Equiv.sum_comp (Equiv.mulLeft a) (fun x : (ZMod q)ˣ => ZMod.stdAddChar (x : ZMod q))
  rw [residueSum_eq_sum_units (m * n) 1 1 (by nlinarith),
    residueSum_eq_sum_units m 1 1 (by omega), residueSum_eq_sum_units n 1 1 (by omega)]
  simp only [Nat.cast_one]
  change unitExpSum (m * n) 1 1 = unitExpSum m 1 1 * unitExpSum n 1 1
  rw [unitExpSum_crt m n hmn u v hbez 1 1]
  simp only [map_one, Prod.fst_one, Prod.snd_one, mul_one]
  rw [show unitExpSum m (v : ZMod m) 1 = unitExpSum m 1 1 from by simpa using hf m hv.unit,
    show unitExpSum n (u : ZMod n) 1 = unitExpSum n 1 1 from by simpa using hf n hu.unit]

/-- Hu page 193, printed C1 equals mu identity. The linear residue sum equals
the Moebius function when the frequency is coprime to the modulus. -/
theorem residueSum_linear_eq_moebius (q a : ℕ) (ha : Nat.Coprime a q) :
    residueSum q a 1 = (ArithmeticFunction.moebius q : ℂ) := by
  rw [residueSum_linear_frequency q a ha]
  clear ha a
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [residueSum]
  | one => simp [residueSum_modulus_one]
  | prime_pow p k hp hk =>
    letI : Fact p.Prime := ⟨hp⟩
    by_cases hk1 : k = 1
    · subst k
      simp [ArithmeticFunction.moebius_apply_prime hp,
        residueSum_prime_linear p 1 (by simp)]
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk2
      have hC : residueSum (p ^ (2 + l)) 1 1 = 0 := by
        simpa only [Nat.add_comm] using residueSum_prime_power_linear p l 1 (by simp)
      rw [hC, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega), Int.cast_zero]
  | coprime m n hm hn hmn ihm ihn =>
    rw [residueSum_linear_multiplicative m n hmn, ihm, ihn,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul]

/-- Hu pages 191 and 193. A vanishing prime local factor makes the exact
singular series definition zero. No analytic convergence input is assumed. -/
theorem singularSeries_eq_zero_of_local_factor (r : ℤ) (p : ℕ) (hp : p.Prime)
    (hfactor : (1 : ℂ) + singularCoefficient r p = 0) : singularSeries r = 0 := by
  classical
  by_cases hs : Summable (fun q : ℕ => singularCoefficient r (q + 1))
  · have hfull : Summable (fun q : ℕ => singularCoefficient r q) :=
      (summable_nat_add_iff 1).mp hs
    have hshift := hfull.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, singularCoefficient_zero, zero_add] at hshift
    have hpowers (p : Nat.Primes) : (∑' k : ℕ, singularCoefficient r (p.val ^ k)) =
        (1 : ℂ) + singularCoefficient r p.val := by
      letI : Fact p.val.Prime := ⟨p.prop⟩
      exact prime_power_series p.val r
    have hprod := EulerProduct.eulerProduct_hasProd (singularCoefficient_one r)
      (fun {m n} h => singularCoefficient_multiplicative r m n h) hfull.norm
      (singularCoefficient_zero r)
    simp_rw [hpowers] at hprod
    have hzero : HasProd (fun q : Nat.Primes => (1 : ℂ) + singularCoefficient r q.val) 0 :=
      hasProd_zero_of_exists_eq_zero ⟨⟨p, hp⟩, hfactor⟩
    unfold singularSeries
    rw [hshift, hprod.unique hzero, Complex.zero_re]
  · simp [singularSeries, tsum_eq_zero_of_not_summable hs]

/-- Hu pages 191 and 193. The singular series vanishes at every even residual. -/
theorem singularSeries_eq_zero_of_even (r : ℤ) (hr : Even r) : singularSeries r = 0 := by
  apply singularSeries_eq_zero_of_local_factor r 2 Nat.prime_two
  rw [prime_local_factor_two]
  have hz : (r : ZMod 2) = 0 := hr.intCast_zmod_two
  simp [hz]

/-- Hu pages 191 and 193. The singular series vanishes at residuals congruent to 2 modulo 3. -/
theorem singularSeries_eq_zero_of_mod_three (r : ℤ) (hr : (r : ZMod 3) = 2) :
    singularSeries r = 0 :=
  singularSeries_eq_zero_of_local_factor r 3 Nat.prime_three
    (prime_local_factor_three_zero r hr)


/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem sum_comp_sq_quadraticChar {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) (f : F → ℂ) :
    (∑ x : F, f (x ^ 2)) = ∑ y : F, ((quadraticChar F y + 1 : ℤ) : ℂ) * f y := by
  classical
  calc _ = ∑ y : F, ∑ x : F, if x ^ 2 = y then f y else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          simp
    _ = ∑ y : F, (((Finset.univ : Finset F).filter (fun x => x ^ 2 = y)).card : ℂ) * f y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro y hy
          congr 1
          have h := quadraticChar_card_sqrts hF y
          have hset : {x : F | x ^ 2 = y}.toFinset =
              (Finset.univ : Finset F).filter (fun x => x ^ 2 = y) := by ext x; simp
          rw [hset] at h
          exact_mod_cast h



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem unitExpSum_quadratic_gauss (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : (ZMod p)ˣ) :
    unitExpSum p (a : ZMod p) 2 =
      gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        (ZMod.stdAddChar.mulShift (a : ZMod p)) - 1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hs := sum_units_add_zero p (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2))
  have ha0 : (a : ZMod p) ≠ 0 := Units.ne_zero a
  have hz : (∑ y : ZMod p, ZMod.stdAddChar ((a : ZMod p) * y)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha0, Nat.cast_zero] using
      AddChar.sum_mulShift (a : ZMod p) (ZMod.isPrimitive_stdAddChar p)
  have hq := sum_comp_sq_quadraticChar hF (fun y => ZMod.stdAddChar ((a : ZMod p) * y))
  have he : (∑ x : ZMod p, ZMod.stdAddChar ((a : ZMod p) * x ^ 2)) =
      gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        (ZMod.stdAddChar.mulShift (a : ZMod p)) := by
    rw [hq]
    simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, Finset.sum_add_distrib, hz, add_zero]
    simp only [gaussSum, MulChar.ringHomComp_apply, AddChar.mulShift_apply, Int.coe_castRingHom]
    congr!
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    AddChar.map_zero_eq_one] at hs
  rw [he] at hs
  unfold unitExpSum
  linear_combination hs



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem quadratic_gauss_sq_eval (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      ZMod.stdAddChar ^ 2 =
      (((quadraticChar (ZMod p) (-1) : ℤ) : ℂ)) * (p : ℂ) := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  let χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hχ1 : χ ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ)
      (by intro x y h; change (x : ℂ) = (y : ℂ) at h; exact_mod_cast h)).mpr
    exact quadraticChar_ne_one hF
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  simpa only [χ, MulChar.ringHomComp_apply, Int.coe_castRingHom, ZMod.card] using
    gaussSum_sq hχ1 hχ2 (ZMod.isPrimitive_stdAddChar p)

/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem quadratic_gauss_sq_norm (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ‖gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      ZMod.stdAddChar ^ 2‖ = (p : ℝ) := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  let χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hχ1 : χ ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ)
      (by intro x y h; change (x : ℂ) = (y : ℂ) at h; exact_mod_cast h)).mpr
    exact quadraticChar_ne_one hF
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  have hnorm (x : ZMod p) (hx : x ≠ 0) : ‖χ x‖ = 1 := by
    rcases quadraticChar_dichotomy hx with h | h <;> simp [χ, h]
  have hsq := gaussSum_sq hχ1 hχ2 (ZMod.isPrimitive_stdAddChar p)
  change ‖gaussSum χ ZMod.stdAddChar ^ 2‖ = (p : ℝ)
  rw [hsq, norm_mul, hnorm (-1) (neg_ne_zero.mpr one_ne_zero), one_mul]
  simp [ZMod.card]



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem unitExpSum_quadratic_char (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : (ZMod p)ˣ) :
    unitExpSum p (a : ZMod p) 2 =
      ((quadraticChar (ZMod p) (a : ZMod p) : ℤ) : ℂ) *
        gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
          ZMod.stdAddChar - 1 := by
  rw [unitExpSum_quadratic_gauss p hp a, gaussSum_mulShift_eq]
  have hχ := (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  rw [hχ.inv]
  rfl

/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem unitExpSum_linear_nonzero (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    unitExpSum p a 1 = -1 := by
  have hs := sum_units_add_zero p (fun x => ZMod.stdAddChar (a * x))
  have hz : (∑ y : ZMod p, ZMod.stdAddChar (a * y)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha, Nat.cast_zero] using
      AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar p)
  simp only [mul_zero, AddChar.map_zero_eq_one, hz] at hs
  unfold unitExpSum
  simp only [pow_one]
  linear_combination hs



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem prime_coefficient_gauss_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (r : ℤ) (hr : (r : ZMod p) ≠ 0) :
    singularCoefficient r p =
      ((1 + 2 * (((quadraticChar (ZMod p) (-(r : ZMod p)) : ℤ) : ℂ))) *
        gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
          ZMod.stdAddChar ^ 2 + 1) / (Nat.totient p : ℂ) ^ 3 := by
  classical
  let χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  let G := gaussSum χ ZMod.stdAddChar
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  have hχsq (a : (ZMod p)ˣ) : (χ (a : ZMod p)) ^ 2 = 1 := by
    rcases quadraticChar_dichotomy (Units.ne_zero a) with h | h <;> simp [χ, h]
  have hlin (a : (ZMod p)ˣ) :
      (∑ x : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) * (x : ZMod p))) = -1 :=
    by simpa [unitExpSum] using unitExpSum_linear_nonzero p a (Units.ne_zero a)
  have hs : (∑ a : (ZMod p)ˣ, ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p))) = -1 := by
    simpa only [unitExpSum, pow_one, neg_mul, mul_neg, mul_comm] using
      unitExpSum_linear_nonzero p (-(r : ZMod p)) (neg_ne_zero.mpr hr)
  have hw : (∑ a : (ZMod p)ˣ, χ (a : ZMod p) *
      ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p))) = χ (-(r : ZMod p)) * G := by
    let b : (ZMod p)ˣ := Units.mk0 (-(r : ZMod p)) (neg_ne_zero.mpr hr)
    have hf := sum_units_add_zero p (fun x => χ x * ZMod.stdAddChar ((b : ZMod p) * x))
    have hg := gaussSum_mulShift_eq χ ZMod.stdAddChar b
    rw [hχ2.inv] at hg
    simp only [MulChar.map_zero, zero_mul, add_zero] at hf
    calc _ = gaussSum χ (ZMod.stdAddChar.mulShift (b : ZMod p)) := by
          change _ = ∑ x : ZMod p, χ x * ZMod.stdAddChar ((b : ZMod p) * x)
          rw [← hf]
          apply Finset.sum_congr rfl
          intro a ha
          congr 2
          dsimp [b]
          ring
      _ = _ := hg
  rw [singularCoefficient_eq_units p (Fact.out : p.Prime).two_le]
  simp_rw [hlin]
  change (∑ a : (ZMod p)ˣ, -1 * (unitExpSum p (a : ZMod p) 2) ^ 2 *
      ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p))) / _ = _
  simp_rw [unitExpSum_quadratic_char p hp]
  have ht (a : (ZMod p)ˣ) :
      -1 * (χ (a : ZMod p) * G - 1) ^ 2 *
        ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p)) =
      -(G ^ 2 + 1) * ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p)) +
        (2 * G) * (χ (a : ZMod p) * ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p))) := by
    linear_combination -G ^ 2 * ZMod.stdAddChar (-(a : ZMod p) * (r : ZMod p)) * hχsq a
  change (∑ a : (ZMod p)ˣ, -1 * (χ (a : ZMod p) * G - 1) ^ 2 * _) / _ = _
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hw]
  dsimp [G, χ]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom]
  ring



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem prime_coefficient_norm_bound (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (r : ℤ) (hr : (r : ZMod p) ≠ 0) :
    ‖singularCoefficient r p‖ ≤ (3 * (p : ℝ) + 1) / (Nat.totient p : ℝ) ^ 3 := by
  let χ : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  let G := gaussSum χ ZMod.stdAddChar
  have hc : ‖1 + 2 * χ (-(r : ZMod p))‖ ≤ 3 := by
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr hr) with h | h <;> norm_num [χ, h]
  have hG : ‖G ^ 2‖ = (p : ℝ) := quadratic_gauss_sq_norm p hp
  have hnum : ‖(1 + 2 * χ (-(r : ZMod p))) * G ^ 2 + 1‖ ≤ 3 * (p : ℝ) + 1 := by
    calc _ ≤ ‖(1 + 2 * χ (-(r : ZMod p))) * G ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖1 + 2 * χ (-(r : ZMod p))‖ * (p : ℝ) + 1 := by rw [norm_mul, hG, norm_one]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg p)]
  rw [prime_coefficient_gauss_formula p hp r hr, norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnum (by positivity)



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem prime_coefficient_norm_le_inv_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (r : ℤ) (hr : (r : ZMod p) ≠ 0) :
    ‖singularCoefficient r p‖ ≤ 32 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine (prime_coefficient_norm_bound p hp r hr).trans ?_
  rw [Nat.totient_prime (Fact.out : p.Prime)]
  rw [Nat.cast_sub ((Fact.out : p.Prime).one_lt.le : 1 ≤ p), Nat.cast_one]
  apply (div_le_div_iff₀ (pow_pos hm 3) (pow_pos hp0 2)).mpr
  have h3 := mul_nonneg (sq_nonneg ((p : ℝ) - 2)) (by linarith : 0 ≤ (p : ℝ) - 2)
  nlinarith [sq_nonneg ((p : ℝ) - 2)]



/-- Hu page 193. Quadratic character evaluation of the exact local coefficient.
This algebraic helper uses the Mathlib Gauss sum identities. -/
theorem prime_coefficient_quadratic_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (r : ℤ) (hr : (r : ZMod p) ≠ 0) :
    singularCoefficient r p =
      ((1 + 2 * (((quadraticChar (ZMod p) (-(r : ZMod p)) : ℤ) : ℂ))) *
        (((quadraticChar (ZMod p) (-1) : ℤ) : ℂ)) * (p : ℂ) + 1) /
        (Nat.totient p : ℂ) ^ 3 := by
  rw [prime_coefficient_gauss_formula p hp r hr, quadratic_gauss_sq_eval p hp]
  ring


/-- Hu page 193. Outside the prime divisors of r the local factor has a summable exponential bound. -/
theorem prime_local_factor_le_exp_of_nonzero (p : ℕ) [Fact p.Prime]
    (r : ℤ) (hr : (r : ZMod p) ≠ 0) :
    1 + (singularCoefficient r p).re ≤ Real.exp (32 / (p : ℝ) ^ 2) := by
  by_cases hp : p = 2
  · subst p
    have h := prime_local_factor_le_totient 2 r
    have he := Real.add_one_le_exp (8 : ℝ)
    norm_num [Nat.totient_prime (by decide : Nat.Prime 2)] at h ⊢
    linarith
  · have h := prime_coefficient_norm_le_inv_sq p hp r hr
    have hre := Complex.re_le_norm (singularCoefficient r p)
    have he := Real.add_one_le_exp (32 / (p : ℝ) ^ 2)
    linarith



/-- Hu page 193. Bound the exact Euler product by the exceptional prime divisor factors. -/
theorem finite_prime_local_product_le (r : ℕ) (hr : r ≠ 0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, (1 + (singularCoefficient (r : ℤ) p).re)) ≤
      (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
        Real.exp (∑' n : ℕ, 32 / (n : ℝ) ^ 2) := by
  let A := s.filter (fun p => p ∈ r.primeFactors)
  let B := s.filter (fun p => p ∉ r.primeFactors)
  have hratio (p : ℕ) (hp : p.Prime) : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hsmall : (∏ p ∈ A, (1 + (singularCoefficient (r : ℤ) p).re)) ≤
      ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    calc _ ≤ ∏ p ∈ A, (p : ℝ) / ((p : ℝ) - 1) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            letI : Fact p.Prime := ⟨hs p (Finset.mem_filter.mp hp).1⟩
            exact prime_local_factor_nonneg p r
          · intro p hp
            have hp' := hs p (Finset.mem_filter.mp hp).1
            letI : Fact p.Prime := ⟨hp'⟩
            simpa only [Nat.totient_prime hp', Nat.cast_sub hp'.one_lt.le, Nat.cast_one] using
              prime_local_factor_le_totient p r
      _ ≤ _ := by
          apply Finset.prod_le_prod_of_subset_of_one_le₀
          · intro p hp; exact (Finset.mem_filter.mp hp).2
          · intro p hp
            exact le_trans zero_le_one (hratio p (hs p (Finset.mem_filter.mp hp).1))
          · intro p hp hpA
            exact hratio p (Nat.prime_of_mem_primeFactors hp)
  have hsum : Summable (fun n : ℕ => 32 / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 32
  have hlarge : (∏ p ∈ B, (1 + (singularCoefficient (r : ℤ) p).re)) ≤
      Real.exp (∑' n : ℕ, 32 / (n : ℝ) ^ 2) := by
    calc _ ≤ ∏ p ∈ B, Real.exp (32 / (p : ℝ) ^ 2) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            letI : Fact p.Prime := ⟨hs p (Finset.mem_filter.mp hp).1⟩
            exact prime_local_factor_nonneg p r
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hp, hpr⟩
            have hp' := hs p hp
            letI : Fact p.Prime := ⟨hp'⟩
            apply prime_local_factor_le_exp_of_nonzero p r
            intro hzero
            have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp (by simpa using hzero)
            exact hpr (Nat.mem_primeFactors.mpr ⟨hp', hdvd, hr⟩)
      _ = Real.exp (∑ p ∈ B, 32 / (p : ℝ) ^ 2) := (Real.exp_sum B _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hsum.sum_le_tsum B (fun n hn => by positivity))
  have hsplit := Finset.prod_filter_mul_prod_filter_not s (fun p => p ∈ r.primeFactors)
    (fun p => 1 + (singularCoefficient (r : ℤ) p).re)
  change (∏ p ∈ A, (1 + (singularCoefficient (r : ℤ) p).re)) *
      (∏ p ∈ B, (1 + (singularCoefficient (r : ℤ) p).re)) = _ at hsplit
  rw [← hsplit]
  exact mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by
    letI : Fact p.Prime := ⟨hs p (Finset.mem_filter.mp hp).1⟩
    exact prime_local_factor_nonneg p r)) (Finset.prod_nonneg (fun p hp =>
      le_trans zero_le_one (hratio p (Nat.prime_of_mem_primeFactors hp))))



/-- Hu page 193. Bound the exact Euler product by the exceptional prime divisor factors. -/
theorem singularSeries_le_primeFactors (r : ℕ) (hr : r ≠ 0) :
    singularSeries (r : ℤ) ≤
      (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
        Real.exp (∑' n : ℕ, 32 / (n : ℝ) ^ 2) := by
  classical
  let R := (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
        Real.exp (∑' n : ℕ, 32 / (n : ℝ) ^ 2)
  by_cases hs : Summable (fun q : ℕ => singularCoefficient (r : ℤ) (q + 1))
  · have hfull : Summable (fun q : ℕ => singularCoefficient (r : ℤ) q) :=
      (summable_nat_add_iff 1).mp hs
    have hshift := hfull.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, singularCoefficient_zero, zero_add] at hshift
    have hpowers (p : Nat.Primes) : (∑' k : ℕ, singularCoefficient (r : ℤ) (p.val ^ k)) =
        (1 : ℂ) + singularCoefficient (r : ℤ) p.val := by
      letI : Fact p.val.Prime := ⟨p.prop⟩
      exact prime_power_series p.val r
    have hprod := EulerProduct.eulerProduct_hasProd (singularCoefficient_one (r : ℤ))
      (fun {m n} h => singularCoefficient_multiplicative (r : ℤ) m n h) hfull.norm
      (singularCoefficient_zero (r : ℤ))
    simp_rw [hpowers] at hprod
    have hlim := Complex.continuous_re.continuousAt.tendsto.comp hprod
    have hbound (s : Finset Nat.Primes) :
        (∏ p ∈ s, ((1 : ℂ) + singularCoefficient (r : ℤ) p.val)).re ≤ R := by
      have heq : (∏ p ∈ s, ((1 : ℂ) + singularCoefficient (r : ℤ) p.val)) =
          (((∏ p ∈ s, (1 + (singularCoefficient (r : ℤ) p.val).re : ℝ)) : ℝ) : ℂ) := by
        calc _ = ∏ p ∈ s, ((1 + (singularCoefficient (r : ℤ) p.val).re : ℝ) : ℂ) := by
                apply Finset.prod_congr rfl
                intro p hp
                letI : Fact p.val.Prime := ⟨p.prop⟩
                exact prime_local_factor_real p.val r
          _ = _ := by push_cast; rfl
      have hcast := congrArg Complex.re heq
      simp only [Complex.ofReal_re] at hcast
      rw [hcast]
      have hnat := finite_prime_local_product_le r hr (s.image Subtype.val) (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact q.prop)
      calc _ = ∏ p ∈ s.image Subtype.val, (1 + (singularCoefficient (r : ℤ) p).re) := by
              symm
              apply Finset.prod_image
              intro a ha b hb hab
              exact Subtype.ext hab
        _ ≤ R := hnat
    unfold singularSeries
    rw [hshift]
    exact le_of_tendsto' hlim hbound
  · have hzero : singularSeries (r : ℤ) = 0 := by
      simp [singularSeries, tsum_eq_zero_of_not_summable hs]
    rw [hzero]
    apply mul_nonneg _ (Real.exp_pos _).le
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (by positivity) (by linarith)




/-- Hu page 193. Prime divisor cutoff estimate for the exact singular series.
The Mertens input is the proved shared PNTSieve theorem. -/
theorem card_primeFactors_log_bound (n : ℕ) (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have hp : 2 ^ n.primeFactors.card ≤ n := by
    calc _ = ∏ p ∈ n.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  have hpr : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n.primeFactors.card) hpr
  simpa only [Real.log_pow] using hlog



/-- Hu page 193. Prime divisor cutoff estimate for the exact singular series.
The Mertens input is the proved shared PNTSieve theorem. -/
theorem prime_ratio_le_exp (p : ℕ) (hp : p.Prime) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (2 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hi : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
    apply (div_le_div_iff₀ hm hp0).mpr
    linarith
  calc (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by field_simp; ring
    _ ≤ 1 + 2 / (p : ℝ) := by linarith
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (2 / (p : ℝ))


/-- Hu page 193. Prime divisor cutoff estimate for the exact singular series.
The Mertens input is the proved shared PNTSieve theorem. -/
theorem prime_ratio_product_le_log (N : ℕ) (hN : 2 ≤ N) :
    (∏ p ∈ (Icc 1 N).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp 16 * Real.log N := by
  let S := (Icc 1 N).filter Nat.Prime
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpos : 0 < ∏ p ∈ S, (1 - (1 : ℝ) / p) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hi : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hlo := LeanLab.PNTSieve.Mertens.mertens_product_ge N hN
  have hid : (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) =
      (∏ p ∈ S, (1 - (1 : ℝ) / p))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  change (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) ≤ _
  rw [hid]
  calc _ ≤ (Real.exp (-16) / Real.log N)⁻¹ := by
          simpa only [one_div, S] using one_div_le_one_div_of_le (div_pos (Real.exp_pos _) hlog) hlo
    _ = _ := by simp [div_eq_mul_inv, Real.exp_neg]; ring



/-- Hu page 193. Prime divisor cutoff estimate for the exact singular series.
The Mertens input is the proved shared PNTSieve theorem. -/
theorem primeFactors_product_cutoff (n T : ℕ) (hn : n ≠ 0) (hT : 2 ≤ T)
    (hlog : Real.log n ≤ 2 * (T : ℝ)) :
    (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (16 + 4 / Real.log 2) * Real.log T := by
  let A := n.primeFactors.filter (fun p => p ≤ T)
  let B := n.primeFactors.filter (fun p => ¬p ≤ T)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have h20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors) := Nat.prime_of_mem_primeFactors hp
  have hratio (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hsmall : (∏ p ∈ A, (p : ℝ) / ((p : ℝ) - 1)) ≤ Real.exp 16 * Real.log T := by
    refine le_trans ?_ (prime_ratio_product_le_log T hT)
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hpt⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hprime p hp).one_lt.le, hpt⟩, hprime p hp⟩
    · intro p hp
      exact le_trans zero_le_one (hratio p (Finset.mem_filter.mp hp).1)
    · intro p hp hpA
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
  have hcount : (B.card : ℝ) * Real.log 2 ≤ 2 * (T : ℝ) := by
    have hc : (B.card : ℝ) ≤ n.primeFactors.card := by exact_mod_cast Finset.card_filter_le n.primeFactors (fun p => ¬p ≤ T)
    have hc' := mul_le_mul_of_nonneg_right hc h20.le
    exact hc'.trans ((card_primeFactors_log_bound n hn).trans hlog)
  have hexp : (B.card : ℝ) * (2 / (T : ℝ)) ≤ 4 / Real.log 2 := by
    apply (le_div_iff₀ h20).mpr
    have ht := (mul_le_mul_of_nonneg_right hcount (show 0 ≤ 2 / (T : ℝ) by positivity))
    have hid : (2 * (T : ℝ)) * (2 / (T : ℝ)) = 4 := by field_simp; ring
    rw [hid] at ht
    nlinarith
  have hlarge : (∏ p ∈ B, (p : ℝ) / ((p : ℝ) - 1)) ≤ Real.exp (4 / Real.log 2) := by
    calc _ ≤ ∏ p ∈ B, Real.exp (2 / (T : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            exact le_trans zero_le_one (hratio p (Finset.mem_filter.mp hp).1)
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hp, hpt⟩
            refine (prime_ratio_le_exp p (hprime p hp)).trans (Real.exp_le_exp.mpr ?_)
            have hpt' : (T : ℝ) ≤ p := by exact_mod_cast (show T ≤ p by omega)
            exact div_le_div_of_nonneg_left (by norm_num) hT0 hpt'
      _ = Real.exp ((B.card : ℝ) * (2 / (T : ℝ))) := by rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ T)
    (fun p => (p : ℝ) / ((p : ℝ) - 1))
  change (∏ p ∈ A, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ B, (p : ℝ) / ((p : ℝ) - 1)) = _ at hsplit
  rw [← hsplit]
  calc _ ≤ (Real.exp 16 * Real.log T) * Real.exp (4 / Real.log 2) :=
        mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => le_trans zero_le_one
          (hratio p (Finset.mem_filter.mp hp).1))) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring



/-- Hu page 193. Prime divisor cutoff estimate for the exact singular series.
The Mertens input is the proved shared PNTSieve theorem. -/
theorem primeFactors_product_le_loglog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 3 ≤ n →
      (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) ≤
        K * Real.log (Real.log n) := by
  let C := Real.exp (16 + 4 / Real.log 2)
  let D := Real.exp 2 / Real.log (Real.log 3)
  have hL3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hLL3 : 0 < Real.log (Real.log 3) := Real.log_pos hL3
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hLn : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) hn3
  have hLLn : Real.log (Real.log 3) ≤ Real.log (Real.log n) :=
    Real.log_le_log (by linarith) hLn
  by_cases hlarge : 2 ≤ Real.log n
  · let T := ⌊Real.log n⌋₊
    have hT : 2 ≤ T := (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ Real.log n)).mpr hlarge
    have hTf : (T : ℝ) ≤ Real.log n := Nat.floor_le (by linarith)
    have hTc : Real.log n < (T : ℝ) + 1 := Nat.lt_floor_add_one _
    have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have hlt : Real.log n ≤ 2 * (T : ℝ) := by linarith
    have hlogT : Real.log T ≤ Real.log (Real.log n) := Real.log_le_log (by linarith) hTf
    calc _ ≤ C * Real.log T := primeFactors_product_cutoff n T hn0 hT hlt
      _ ≤ C * Real.log (Real.log n) := mul_le_mul_of_nonneg_left hlogT hC
      _ ≤ _ := by nlinarith [mul_nonneg hD (show 0 ≤ Real.log (Real.log n) by linarith)]
  · have hlt : Real.log n < 2 := lt_of_not_ge hlarge
    have hnexp : (n : ℝ) < Real.exp 2 := by
      have h := Real.exp_lt_exp.mpr hlt
      rwa [Real.exp_log hnpos] at h
    have hprod : (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) ≤ n := by
      calc _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro p hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
              exact div_nonneg (by positivity) (by linarith)
            · intro p hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
              apply (div_le_iff₀ (by linarith)).mpr
              nlinarith
        _ ≤ n := by
            rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
    have hD_eq : D * Real.log (Real.log 3) = Real.exp 2 := by dsimp [D]; field_simp
    calc _ ≤ (n : ℝ) := hprod
      _ ≤ Real.exp 2 := hnexp.le
      _ = D * Real.log (Real.log 3) := hD_eq.symm
      _ ≤ D * Real.log (Real.log n) := mul_le_mul_of_nonneg_left hLLn hD
      _ ≤ _ := by nlinarith [mul_nonneg hC (show 0 ≤ Real.log (Real.log n) by linarith)]


end LocalFactors702

/-- LEAF: Hu page 193, the singular series S of n for one prime and two prime
squares is nonnegative, by its Euler product of local densities.
Class HARD. P0101 page 193 definition of S of n, used in Lemma 2.1 and 2.2. -/
theorem singularSeries_nonneg (r : ℤ) : 0 ≤ singularSeries r := by
  classical
  by_cases hs : Summable (fun q : ℕ => singularCoefficient r (q + 1))
  · have hfull : Summable (fun q : ℕ => singularCoefficient r q) :=
      (summable_nat_add_iff 1).mp hs
    have hshift := hfull.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, singularCoefficient_zero, zero_add] at hshift
    have hpowers (p : Nat.Primes) : (∑' k : ℕ, singularCoefficient r (p.val ^ k)) =
        (1 : ℂ) + singularCoefficient r p.val := by
      letI : Fact p.val.Prime := ⟨p.prop⟩
      exact prime_power_series p.val r
    have hprod := EulerProduct.eulerProduct_hasProd (singularCoefficient_one r)
      (fun {m n} h => singularCoefficient_multiplicative r m n h) hfull.norm
      (singularCoefficient_zero r)
    simp_rw [hpowers] at hprod
    have hlim := Complex.continuous_re.continuousAt.tendsto.comp hprod
    have hpos (s : Finset Nat.Primes) :
        0 ≤ (∏ p ∈ s, ((1 : ℂ) + singularCoefficient r p.val)).re := by
      have heq : (∏ p ∈ s, ((1 : ℂ) + singularCoefficient r p.val)) =
          (((∏ p ∈ s, (1 + (singularCoefficient r p.val).re : ℝ)) : ℝ) : ℂ) := by
        calc _ = ∏ p ∈ s, ((1 + (singularCoefficient r p.val).re : ℝ) : ℂ) := by
                apply Finset.prod_congr rfl
                intro p hp
                letI : Fact p.val.Prime := ⟨p.prop⟩
                exact prime_local_factor_real p.val r
          _ = _ := by push_cast; rfl
      have hcast := congrArg Complex.re heq
      simp only [Complex.ofReal_re] at hcast
      rw [hcast]
      apply Finset.prod_nonneg
      intro p hp
      letI : Fact p.val.Prime := ⟨p.prop⟩
      exact prime_local_factor_nonneg p.val r
    unfold singularSeries
    rw [hshift]
    exact ge_of_tendsto' hlim hpos
  · simp [singularSeries, tsum_eq_zero_of_not_summable hs]

/-- LEAF: Hu page 193, the standard upper bound of the singular series S of n by a
constant times log log n, from its Euler product, only primes dividing n contribute
factors of size one plus O of one over p.
Class HARD. P0101 page 193 definition of S of n. -/
theorem singularSeries_le_loglog :
    ∃ K : ℝ, ∀ r : ℤ, 3 ≤ r → singularSeries r ≤ K * Real.log (Real.log r) := by
  obtain ⟨K, hK, hb⟩ := primeFactors_product_le_loglog
  let E := Real.exp (∑' n : ℕ, 32 / (n : ℝ) ^ 2)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨K * E, ?_⟩
  intro r hr
  let n := r.toNat
  have hn3 : 3 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnr : (n : ℤ) = r := Int.toNat_of_nonneg (by omega)
  have hnrR : (n : ℝ) = (r : ℝ) := by exact_mod_cast hnr
  calc singularSeries r = singularSeries (n : ℤ) := by rw [hnr]
    _ ≤ (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) * E :=
      singularSeries_le_primeFactors n hn0
    _ ≤ (K * Real.log (Real.log n)) * E := mul_le_mul_of_nonneg_right (hb n hn3) hE
    _ = _ := by rw [hnrR]; ring


/-- Page 194, elementary growth: a constant times log log x squared is eventually
below log x. Used to move the singular integral from m to N. -/
theorem loglog_sq_le_log (A : ℝ) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ x : ℝ, (N₀ : ℝ) ≤ x → A * Real.log (Real.log x) ^ 2 ≤ Real.log x := by
  have h1 : (fun y : ℝ => Real.log y ^ 2) =o[Filter.atTop] id :=
    Real.isLittleO_pow_log_id_atTop
  have h2 := h1.bound (show (0 : ℝ) < 1 / A by positivity)
  have h3 : ∀ᶠ x in Filter.atTop, ‖Real.log (Real.log x) ^ 2‖ ≤ 1 / A * ‖id (Real.log x)‖ :=
    Real.tendsto_log_atTop.eventually h2
  have h4 : ∀ᶠ x in Filter.atTop, (0 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 0)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h3.and h4)
  refine ⟨⌈N⌉₊, fun x hx => ?_⟩
  obtain ⟨hb, hpos⟩ := hN x ((Nat.le_ceil N).trans hx)
  rw [Real.norm_of_nonneg (sq_nonneg _), id, Real.norm_of_nonneg hpos] at hb
  have := mul_le_mul_of_nonneg_left hb hA.le
  rw [← mul_assoc, mul_one_div_cancel hA.ne', one_mul] at this
  exact this

/-- Page 194, proof of Lemma 2.2, the displayed form with main term pi N over 4 times
the singular series of the residual. CONDITIONAL ON the residual asymptotic and the
two singular series leaves. -/
theorem majorIntegral_asymptotic (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n : ℕ, N₀ ≤ n → n ≤ n₁ → (n₁ : ℝ) ≤ C * n →
      ∀ m : ℤ, (n : ℝ) - 82 * ((n₁ : ℝ) / Real.log n₁) ≤ m → m ≤ (n : ℤ) →
        ‖majorIntegral n₁ n m - ((Real.pi / 4 * n * singularSeries m : ℝ) : ℂ)‖ ≤
          η * n / Real.log (Real.log n₁) := by
  obtain ⟨K₀, hK₀⟩ := singularSeries_le_loglog
  set K : ℝ := max K₀ 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hCpos : (0 : ℝ) < C := by linarith
  set A : ℝ := Real.pi * 82 * K * C / (2 * η) + 1 with hAdef
  have hA0 : 0 < A := by
    have : 0 ≤ Real.pi * 82 * K * C / (2 * η) := by positivity
    linarith
  obtain ⟨N₂, hN₂⟩ := loglog_sq_le_log A hA0
  obtain ⟨N₁, hN₁⟩ := majorIntegral_asymptotic_residual C (η / 2) hC (half_pos hη)
  refine ⟨max (max N₁ N₂) (max (max ⌈Real.exp (Real.exp 1)⌉₊ ⌈Real.exp (164 * C)⌉₊) 16), ?_⟩
  intro n₁ n hN hle hratio m hlo hhi
  have hNN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ n₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hN.trans hle)
  have hee : Real.exp (Real.exp 1) ≤ n₁ := by
    have h1 : ⌈Real.exp (Real.exp 1)⌉₊ ≤ n₁ := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))) (hN.trans hle)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hec : Real.exp (164 * C) ≤ n₁ := by
    have h1 : ⌈Real.exp (164 * C)⌉₊ ≤ n₁ := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))) (hN.trans hle)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have h16 : 16 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hnr : (16 : ℝ) ≤ n := by exact_mod_cast h16
  have hnn₁ : (n : ℝ) ≤ n₁ := by exact_mod_cast hle
  have hn₁pos : (0 : ℝ) < n₁ := by linarith
  have hlogn₁ : Real.exp 1 ≤ Real.log n₁ := by
    rw [Real.le_log_iff_exp_le hn₁pos]; exact hee
  have hlogC : 164 * C ≤ Real.log n₁ := by
    rw [Real.le_log_iff_exp_le hn₁pos]; exact hec
  have hlogpos : 0 < Real.log n₁ := lt_of_lt_of_le (Real.exp_pos 1) hlogn₁
  set D : ℝ := Real.log (Real.log n₁) with hDdef
  have hD : 1 ≤ D := by
    rw [hDdef, Real.le_log_iff_exp_le hlogpos]; exact hlogn₁
  have hD0 : 0 < D := by linarith
  set X : ℝ := 82 * ((n₁ : ℝ) / Real.log n₁) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXlog : X * Real.log n₁ = 82 * n₁ := by
    rw [hXdef]; field_simp
  have hXsmall : X ≤ (n : ℝ) / 2 := by
    have h1 : X * Real.log n₁ ≤ (n : ℝ) / 2 * Real.log n₁ := by
      rw [hXlog]
      have : 82 * (n₁ : ℝ) ≤ 82 * (C * n) := by linarith
      nlinarith
    exact le_of_mul_le_mul_right h1 hlogpos
  have hm3 : (3 : ℝ) ≤ m := by linarith
  have hm3' : (3 : ℤ) ≤ m := by exact_mod_cast hm3
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hhi
  have hmn₁ : (m : ℝ) ≤ n₁ := hmn.trans hnn₁
  have hS0 := singularSeries_nonneg m
  have hSle : singularSeries m ≤ K * D := by
    have hlogm : 1 < Real.log m := by
      have : Real.exp 1 < m := lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith)
      rw [Real.lt_log_iff_exp_lt (by linarith)]; exact this
    have hll : Real.log (Real.log m) ≤ D :=
      Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hmn₁)
    have hll0 : 0 ≤ Real.log (Real.log m) := Real.log_nonneg hlogm.le
    calc singularSeries m ≤ K₀ * Real.log (Real.log m) := hK₀ m hm3'
      _ ≤ K * Real.log (Real.log m) := mul_le_mul_of_nonneg_right (le_max_left _ _) hll0
      _ ≤ K * D := mul_le_mul_of_nonneg_left hll hK
  have hres := hN₁ n₁ n hNN₁ hle hratio m hlo hhi
  -- the shift of the main term from m to n
  have hshift : Real.pi / 4 * ((n : ℝ) - m) * singularSeries m ≤ η / 2 * n / D := by
    have hnm : (n : ℝ) - m ≤ X := by linarith
    have hnm0 : 0 ≤ (n : ℝ) - m := by linarith
    have hAD := hN₂ n₁ (by exact_mod_cast hNN₂)
    have hstep1 : Real.pi / 4 * ((n : ℝ) - m) * singularSeries m ≤
        Real.pi / 4 * X * (K * D) := by
      have := mul_le_mul hnm hSle hS0 hX0
      have hp : 0 ≤ Real.pi / 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hp]
    have hkey : Real.pi / 4 * 82 * K * C * D ^ 2 ≤ η / 2 * Real.log n₁ := by
      have hA' : Real.pi / 4 * 82 * K * C ≤ η / 2 * A := by
        rw [hAdef]
        have : η / 2 * (Real.pi * 82 * K * C / (2 * η)) = Real.pi / 4 * 82 * K * C := by
          field_simp; ring
        nlinarith
      have hD2 : 0 ≤ D ^ 2 := sq_nonneg _
      calc Real.pi / 4 * 82 * K * C * D ^ 2 ≤ η / 2 * A * D ^ 2 :=
            mul_le_mul_of_nonneg_right hA' hD2
        _ = η / 2 * (A * D ^ 2) := by ring
        _ ≤ η / 2 * Real.log n₁ := mul_le_mul_of_nonneg_left hAD (by positivity)
    have hstep2 : Real.pi / 4 * X * (K * D) ≤ η / 2 * n / D := by
      rw [le_div_iff₀ hD0]
      have hlhs : Real.pi / 4 * X * (K * D) * D * Real.log n₁ =
          Real.pi / 4 * 82 * K * D ^ 2 * n₁ := by
        have : Real.pi / 4 * X * (K * D) * D * Real.log n₁ =
            Real.pi / 4 * K * D ^ 2 * (X * Real.log n₁) := by ring
        rw [this, hXlog]; ring
      have hn₁C : Real.pi / 4 * 82 * K * D ^ 2 * n₁ ≤
          Real.pi / 4 * 82 * K * D ^ 2 * (C * n) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      have hfin : Real.pi / 4 * 82 * K * D ^ 2 * (C * n) ≤ η / 2 * n * Real.log n₁ := by
        have := mul_le_mul_of_nonneg_right hkey (show (0 : ℝ) ≤ n by positivity)
        nlinarith
      have h3 : Real.pi / 4 * X * (K * D) * D * Real.log n₁ ≤
          η / 2 * n * Real.log n₁ := by linarith
      exact le_of_mul_le_mul_right (by linarith) hlogpos
    linarith
  have hsplit : majorIntegral n₁ n m - ((Real.pi / 4 * n * singularSeries m : ℝ) : ℂ) =
      (majorIntegral n₁ n m - ((Real.pi / 4 * m * singularSeries m : ℝ) : ℂ)) -
        ((Real.pi / 4 * ((n : ℝ) - m) * singularSeries m : ℝ) : ℂ) := by
    push_cast; ring
  rw [hsplit]
  have hnorm2 : ‖((Real.pi / 4 * ((n : ℝ) - m) * singularSeries m : ℝ) : ℂ)‖ ≤
      η / 2 * n / D := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      have : 0 ≤ (n : ℝ) - m := by linarith
      positivity)]
    exact hshift
  calc _ ≤ ‖majorIntegral n₁ n m - ((Real.pi / 4 * m * singularSeries m : ℝ) : ℂ)‖ +
        ‖((Real.pi / 4 * ((n : ℝ) - m) * singularSeries m : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ η / 2 * n / D + η / 2 * n / D := add_le_add hres hnorm2
    _ = η * n / D := by ring

/-- Page 194. Norm algebra for the product of two approximations. -/
theorem prod_approx_le (I₁ I₂ : ℂ) (a b K D ε n₁ n₂ : ℝ) (hK : 0 ≤ K) (hD : 1 ≤ D)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ K * D) (hb : b ≤ K * D)
    (h₁ : ‖I₁ - ((Real.pi / 4 * n₁ * a : ℝ) : ℂ)‖ ≤ ε * n₁ / D)
    (h₂ : ‖I₂ - ((Real.pi / 4 * n₂ * b : ℝ) : ℂ)‖ ≤ ε * n₂ / D) :
    Real.pi ^ 2 / 16 * (n₁ * n₂) * (a * b) - ε * (1 + Real.pi * K / 2) * (n₁ * n₂) ≤
      (I₁ * I₂).re := by
  set M₁ : ℝ := Real.pi / 4 * n₁ * a
  set M₂ : ℝ := Real.pi / 4 * n₂ * b
  have hD0 : 0 < D := by linarith
  have hM₁ : 0 ≤ M₁ := by positivity
  have hM₂ : 0 ≤ M₂ := by positivity
  have hM₁le : M₁ ≤ Real.pi / 4 * n₁ * (K * D) := by
    have : 0 ≤ Real.pi / 4 * n₁ := by positivity
    exact mul_le_mul_of_nonneg_left ha this
  have hM₂le : M₂ ≤ Real.pi / 4 * n₂ * (K * D) := by
    have : 0 ≤ Real.pi / 4 * n₂ := by positivity
    exact mul_le_mul_of_nonneg_left hb this
  set u : ℂ := I₁ - (M₁ : ℂ)
  set v : ℂ := I₂ - (M₂ : ℂ)
  have hdecomp : I₁ * I₂ - ((M₁ * M₂ : ℝ) : ℂ) = u * v + u * (M₂ : ℂ) + (M₁ : ℂ) * v := by
    simp only [u, v]; push_cast; ring
  have hu : ‖u‖ ≤ ε * n₁ / D := h₁
  have hv : ‖v‖ ≤ ε * n₂ / D := h₂
  have hnorm : ‖I₁ * I₂ - ((M₁ * M₂ : ℝ) : ℂ)‖ ≤ ‖u‖ * ‖v‖ + ‖u‖ * M₂ + M₁ * ‖v‖ := by
    rw [hdecomp]
    calc ‖u * v + u * (M₂ : ℂ) + (M₁ : ℂ) * v‖
        ≤ ‖u * v‖ + ‖u * (M₂ : ℂ)‖ + ‖(M₁ : ℂ) * v‖ := norm_add₃_le
      _ = ‖u‖ * ‖v‖ + ‖u‖ * M₂ + M₁ * ‖v‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hM₁, Real.norm_of_nonneg hM₂]
  have hre : (((M₁ * M₂ : ℝ) : ℂ)).re - ‖I₁ * I₂ - ((M₁ * M₂ : ℝ) : ℂ)‖ ≤ (I₁ * I₂).re := by
    have h := Complex.abs_re_le_norm (I₁ * I₂ - ((M₁ * M₂ : ℝ) : ℂ))
    rw [Complex.sub_re] at h
    linarith [neg_abs_le ((I₁ * I₂).re - (((M₁ * M₂ : ℝ) : ℂ)).re)]
  rw [Complex.ofReal_re] at hre
  -- bounds on the three error terms
  have hun : 0 ≤ ‖u‖ := norm_nonneg _
  have hvn : 0 ≤ ‖v‖ := norm_nonneg _
  have e1 : ‖u‖ * ‖v‖ ≤ ε * (n₁ * n₂) := by
    have : ‖u‖ * ‖v‖ ≤ (ε * n₁ / D) * (ε * n₂ / D) := mul_le_mul hu hv hvn (by positivity)
    have h2 : (ε * n₁ / D) * (ε * n₂ / D) = ε * ε * (n₁ * n₂) / (D * D) := by
      field_simp
    have h3 : ε * ε * (n₁ * n₂) / (D * D) ≤ ε * (n₁ * n₂) := by
      rw [div_le_iff₀ (by positivity)]
      have hεε : ε * ε ≤ ε := by nlinarith
      have hDD : 1 ≤ D * D := by nlinarith
      have hp : 0 ≤ ε * (n₁ * n₂) := by positivity
      nlinarith [mul_le_mul hεε hDD zero_le_one hε, mul_nonneg hn₁ hn₂]
    linarith
  have e2 : ‖u‖ * M₂ ≤ ε * (Real.pi * K / 4) * (n₁ * n₂) := by
    have : ‖u‖ * M₂ ≤ (ε * n₁ / D) * (Real.pi / 4 * n₂ * (K * D)) :=
      mul_le_mul hu hM₂le hM₂ (by positivity)
    have h2 : (ε * n₁ / D) * (Real.pi / 4 * n₂ * (K * D)) =
        ε * (Real.pi * K / 4) * (n₁ * n₂) := by
      field_simp
    linarith
  have e3 : M₁ * ‖v‖ ≤ ε * (Real.pi * K / 4) * (n₁ * n₂) := by
    have : M₁ * ‖v‖ ≤ (Real.pi / 4 * n₁ * (K * D)) * (ε * n₂ / D) :=
      mul_le_mul hM₁le hv hvn (by positivity)
    have h2 : (Real.pi / 4 * n₁ * (K * D)) * (ε * n₂ / D) =
        ε * (Real.pi * K / 4) * (n₁ * n₂) := by
      field_simp
    linarith
  have hmain : M₁ * M₂ = Real.pi ^ 2 / 16 * (n₁ * n₂) * (a * b) := by
    simp only [M₁, M₂]; ring
  nlinarith

/-- Page 192. Each admissible shared shift is at most 82 times 2 to the floor of L. -/
theorem shift_le (n₁ : ℕ) (ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1)) :
    (shift n₁ ν : ℝ) ≤ 82 * (2 : ℝ) ^ ⌊L n₁⌋₊ := by
  unfold shift
  push_cast
  calc ∑ j, (2 : ℝ) ^ (ν j).val ≤ ∑ _j : Fin 82, (2 : ℝ) ^ ⌊L n₁⌋₊ := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp (ν j).isLt)
    _ = 82 * (2 : ℝ) ^ ⌊L n₁⌋₊ := by simp

/-- Page 192. Shared shifts are nonnegative. -/
theorem shift_nonneg (n₁ : ℕ) (ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1)) :
    0 ≤ shift n₁ ν := by
  unfold shift
  positivity

/-- Page 194. Exact parent statement, Decomp570a.major_arc_singular_comparison,
CONDITIONAL ON the four leaves above. -/
theorem major_arc_singular_comparison_of_leaves (C η : ℝ) (hC : 1 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) * singularMass n₁ n₂ -
        η * scale n₁ n₂ ≤ R1 n₁ n₂ := by
  classical
  obtain ⟨K₀, hK₀⟩ := singularSeries_le_loglog
  set K : ℝ := max K₀ 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set c : ℝ := 1 + Real.pi * K / 2 with hcdef
  have hc : 1 ≤ c := by
    have : 0 ≤ Real.pi * K / 2 := by positivity
    linarith
  set ε : ℝ := min 1 (η / (c * 2 ^ 82)) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε * c * 2 ^ 82 ≤ η := by
    have h := min_le_right 1 (η / (c * 2 ^ 82))
    have hpos : 0 < c * 2 ^ 82 := by positivity
    calc ε * c * 2 ^ 82 = ε * (c * 2 ^ 82) := by ring
      _ ≤ η / (c * 2 ^ 82) * (c * 2 ^ 82) := mul_le_mul_of_nonneg_right h hpos.le
      _ = η := div_mul_cancel₀ η hpos.ne'
  obtain ⟨N₁, hB⟩ := majorIntegral_asymptotic C ε hC hεpos
  refine ⟨max (max N₁ 16) (max ⌈Real.exp (Real.exp 1)⌉₊ ⌈Real.exp (164 * C)⌉₊), ?_⟩
  intro n₁ n₂ _ho₁ _ho₂ hn hlt hratio
  have hN₁ : N₁ ≤ n₂ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have h16 : 16 ≤ n₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hee : Real.exp (Real.exp 1) ≤ n₁ := by
    have h1 : ⌈Real.exp (Real.exp 1)⌉₊ ≤ n₁ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hn.trans hlt.le)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hec : Real.exp (164 * C) ≤ n₁ := by
    have h1 : ⌈Real.exp (164 * C)⌉₊ ≤ n₁ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hn.trans hlt.le)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hn₂r : (16 : ℝ) ≤ n₂ := by exact_mod_cast h16
  have hn₁₂ : (n₂ : ℝ) ≤ n₁ := by exact_mod_cast hlt.le
  have hn₁pos : (0 : ℝ) < n₁ := by linarith
  have hlogn₁ : Real.exp 1 ≤ Real.log n₁ := by
    rw [Real.le_log_iff_exp_le hn₁pos]; exact hee
  have hlogC : 164 * C ≤ Real.log n₁ := by
    rw [Real.le_log_iff_exp_le hn₁pos]; exact hec
  have hlogpos : 0 < Real.log n₁ := lt_of_lt_of_le (Real.exp_pos 1) hlogn₁
  set D : ℝ := Real.log (Real.log n₁) with hDdef
  have hD : 1 ≤ D := by
    rw [hDdef, Real.le_log_iff_exp_le hlogpos]; exact hlogn₁
  -- the shift bound
  have hshift_le : ∀ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
      (shift n₁ ν : ℝ) ≤ 82 * ((n₁ : ℝ) / Real.log n₁) := by
    intro ν
    have h1 := shift_le n₁ ν
    have h2 := Flag1737.two_pow_floor_L_le n₁ (by omega)
    linarith
  have hHsmall : 82 * ((n₁ : ℝ) / Real.log n₁) ≤ (n₂ : ℝ) / 2 := by
    have hCpos : (0 : ℝ) < C := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hlogpos]
    have : 82 * (n₁ : ℝ) ≤ 82 * (C * n₂) := by linarith
    nlinarith
  -- per tuple lower bound
  have hterm : ∀ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
      Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) *
          (let h : ℤ := ∑ j, (2 : ℤ) ^ (ν j).val
           let r₁ : ℤ := (n₁ : ℤ) - h
           let r₂ : ℤ := (n₂ : ℤ) - h
           if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁ ∧ 2 ≤ r₂ ∧ r₁ % 3 ≠ 2 ∧ r₂ % 3 ≠ 2
           then singularSeries r₁ * singularSeries r₂ else 0) -
        ε * c * ((n₁ : ℝ) * n₂) ≤
      (if (∀ j, 4 ≤ (ν j).val) then
        (majorIntegral n₁ n₁ ((n₁ : ℤ) - shift n₁ ν) *
          majorIntegral n₁ n₂ ((n₂ : ℤ) - shift n₁ ν)).re
      else 0) := by
    intro ν
    have hεc : 0 ≤ ε * c * ((n₁ : ℝ) * n₂) := by positivity
    by_cases hadm : ∀ j, 4 ≤ (ν j).val
    · rw [if_pos hadm]
      set r₁ : ℤ := (n₁ : ℤ) - shift n₁ ν with hr₁
      set r₂ : ℤ := (n₂ : ℤ) - shift n₁ ν with hr₂
      have hs0 : (0 : ℝ) ≤ shift n₁ ν := by exact_mod_cast shift_nonneg n₁ ν
      have hs := hshift_le ν
      have hr₁le : r₁ ≤ (n₁ : ℤ) := by have := shift_nonneg n₁ ν; omega
      have hr₂le : r₂ ≤ (n₂ : ℤ) := by have := shift_nonneg n₁ ν; omega
      have hr₁lo : (n₁ : ℝ) - 82 * ((n₁ : ℝ) / Real.log n₁) ≤ (r₁ : ℝ) := by
        rw [hr₁]; push_cast; linarith
      have hr₂lo : (n₂ : ℝ) - 82 * ((n₁ : ℝ) / Real.log n₁) ≤ (r₂ : ℝ) := by
        rw [hr₂]; push_cast; linarith
      have hr₂3 : (3 : ℝ) ≤ r₂ := by linarith
      have hr₁3 : (3 : ℝ) ≤ r₁ := by linarith
      have hr₂3' : (3 : ℤ) ≤ r₂ := by exact_mod_cast hr₂3
      have hr₁3' : (3 : ℤ) ≤ r₁ := by exact_mod_cast hr₁3
      -- singular series bounds
      have hloglog : ∀ r : ℤ, 3 ≤ r → r ≤ (n₁ : ℤ) →
          singularSeries r ≤ K * D := by
        intro r h3 hle
        have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast h3
        have hrle : (r : ℝ) ≤ n₁ := by exact_mod_cast hle
        have hlogr : 1 < Real.log r := by
          have : Real.exp 1 < r := lt_of_lt_of_le Real.exp_one_lt_d9 (by linarith)
          rw [Real.lt_log_iff_exp_lt (by linarith)]; exact this
        have hll : Real.log (Real.log r) ≤ D :=
          Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hrle)
        have hll0 : 0 ≤ Real.log (Real.log r) := Real.log_nonneg hlogr.le
        calc singularSeries r ≤ K₀ * Real.log (Real.log r) := hK₀ r h3
          _ ≤ K * Real.log (Real.log r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hll0
          _ ≤ K * D := mul_le_mul_of_nonneg_left hll hK
      have ha := hloglog r₁ hr₁3' hr₁le
      have hb := hloglog r₂ hr₂3' (by omega)
      have hI₁ := hB n₁ n₁ (hN₁.trans hlt.le) le_rfl (le_mul_of_one_le_left hn₁pos.le hC.le) r₁ hr₁lo hr₁le
      have hI₂ := hB n₁ n₂ hN₁ hlt.le hratio r₂ hr₂lo hr₂le
      have key := prod_approx_le _ _ (singularSeries r₁) (singularSeries r₂) K D ε n₁ n₂
        hK hD hεpos.le hε1 (by positivity) (by positivity)
        (singularSeries_nonneg r₁) (singularSeries_nonneg r₂) ha hb hI₁ hI₂
      have hsel : (let h : ℤ := ∑ j, (2 : ℤ) ^ (ν j).val
           let r₁' : ℤ := (n₁ : ℤ) - h
           let r₂' : ℤ := (n₂ : ℤ) - h
           if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁' ∧ 2 ≤ r₂' ∧ r₁' % 3 ≠ 2 ∧ r₂' % 3 ≠ 2
           then singularSeries r₁' * singularSeries r₂' else 0) ≤
          singularSeries r₁ * singularSeries r₂ := by
        show (if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁ ∧ 2 ≤ r₂ ∧ r₁ % 3 ≠ 2 ∧ r₂ % 3 ≠ 2
           then singularSeries r₁ * singularSeries r₂ else 0) ≤ _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (singularSeries_nonneg r₁) (singularSeries_nonneg r₂)
      have hcoef : 0 ≤ Real.pi ^ 2 / 16 * ((n₁ : ℝ) * n₂) := by positivity
      have := mul_le_mul_of_nonneg_left hsel hcoef
      have hcdef' : ε * c * ((n₁ : ℝ) * n₂) = ε * (1 + Real.pi * K / 2) * ((n₁ : ℝ) * n₂) := by
        rw [hcdef]
      linarith
    · rw [if_neg hadm]
      have hsel : (let h : ℤ := ∑ j, (2 : ℤ) ^ (ν j).val
           let r₁ : ℤ := (n₁ : ℤ) - h
           let r₂ : ℤ := (n₂ : ℤ) - h
           if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁ ∧ 2 ≤ r₂ ∧ r₁ % 3 ≠ 2 ∧ r₂ % 3 ≠ 2
           then singularSeries r₁ * singularSeries r₂ else 0) = 0 := by
        simp only
        rw [if_neg (fun h => hadm h.1)]
      rw [hsel, mul_zero]
      linarith
  -- sum over tuples
  rw [R1_eq_sum_majorIntegral]
  have hsum := Finset.sum_le_sum (fun ν (_ : ν ∈ (Finset.univ :
    Finset (Fin 82 → Fin (⌊L n₁⌋₊ + 1)))) => hterm ν)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hmass : singularMass n₁ n₂ = ∑ ν : Fin 82 → Fin (⌊L n₁⌋₊ + 1),
      (let h : ℤ := ∑ j, (2 : ℤ) ^ (ν j).val
       let r₁ : ℤ := (n₁ : ℤ) - h
       let r₂ : ℤ := (n₂ : ℤ) - h
       if (∀ j, 4 ≤ (ν j).val) ∧ 2 ≤ r₁ ∧ 2 ≤ r₂ ∧ r₁ % 3 ≠ 2 ∧ r₂ % 3 ≠ 2
       then singularSeries r₁ * singularSeries r₂ else 0) := by
    unfold singularMass
    congr 1
  rw [hmass]
  -- the number of tuples is at most 2 to power 82 times L to power 82
  have hL1 : 1 ≤ L n₁ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    unfold L Decomp115.logScale
    rw [le_div_iff₀ hlog2, one_mul]
    have hratio' : (2 : ℝ) ≤ (n₁ : ℝ) / Real.log n₁ := by
      rw [le_div_iff₀ hlogpos]
      have hx : Real.log ((n₁ : ℝ) / 2) ≤ (n₁ : ℝ) / 2 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at hx
      linarith
    exact Real.log_le_log (by norm_num) hratio'
  have hcard : ((Fintype.card (Fin 82 → Fin (⌊L n₁⌋₊ + 1)) : ℕ) : ℝ) ≤
      2 ^ 82 * L n₁ ^ 82 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    have hfl : (⌊L n₁⌋₊ : ℝ) ≤ L n₁ := Nat.floor_le (by linarith)
    calc ((⌊L n₁⌋₊ : ℝ) + 1) ^ 82 ≤ (2 * L n₁) ^ 82 := by
          apply pow_le_pow_left₀ (by positivity); linarith
      _ = 2 ^ 82 * L n₁ ^ 82 := by ring
  have herr : ((Fintype.card (Fin 82 → Fin (⌊L n₁⌋₊ + 1)) : ℕ) : ℝ) *
      (ε * c * ((n₁ : ℝ) * n₂)) ≤ η * scale n₁ n₂ := by
    unfold scale
    have hnn : 0 ≤ ε * c * ((n₁ : ℝ) * n₂) := by positivity
    calc ((Fintype.card (Fin 82 → Fin (⌊L n₁⌋₊ + 1)) : ℕ) : ℝ) * (ε * c * ((n₁ : ℝ) * n₂))
        ≤ (2 ^ 82 * L n₁ ^ 82) * (ε * c * ((n₁ : ℝ) * n₂)) :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ = (ε * c * 2 ^ 82) * ((n₁ : ℝ) * n₂ * L n₁ ^ 82) := by ring
      _ ≤ η * ((n₁ : ℝ) * n₂ * L n₁ ^ 82) := by
          apply mul_le_mul_of_nonneg_right hεη
          have : 0 ≤ L n₁ := by linarith
          positivity
  linarith



end LeanLab.Hathi2021.Decomp570aLeavesMajor
