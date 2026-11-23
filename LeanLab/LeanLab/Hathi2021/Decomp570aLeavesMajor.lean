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

/-- LEAF: Hu page 193, the singular series S of n for one prime and two prime
squares is nonnegative, by its Euler product of local densities.
Class HARD. P0101 page 193 definition of S of n, used in Lemma 2.1 and 2.2. -/
theorem singularSeries_nonneg (r : ℤ) : 0 ≤ singularSeries r := by
  sorry

/-- LEAF: Hu page 193, the standard upper bound of the singular series S of n by a
constant times log log n, from its Euler product, only primes dividing n contribute
factors of size one plus O of one over p.
Class HARD. P0101 page 193 definition of S of n. -/
theorem singularSeries_le_loglog :
    ∃ K : ℝ, ∀ r : ℤ, 3 ≤ r → singularSeries r ≤ K * Real.log (Real.log r) := by
  sorry

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
