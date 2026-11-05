/-
AI wrote this Lean code. Codex task310.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 pages 72 and 83 to 86.
The Type II proof separates the coefficient moment from the row energy.
The coefficient moment is proved. The row energy input remains OPEN.
The assembly is CONDITIONAL ON row_energy only.
-/
import LeanLab.Tolev2009.Decomp310a

open Finset Real ComplexConjugate

namespace LeanLab.Tolev2009.Decomp310b

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp310a

/-- The squared inner row sum before the correlation expansion on page 83. -/
noncomputable def energy (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖row lam l₃ K N α x H H₁ b m‖ ^ 2

/-- The exact finite Cauchy step on page 83 preceding display 55. -/
theorem bilinear_sq_le_energy (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) * energy lam l₃ K N α x M M₁ H H₁ b := by
  rw [bilinear_eq_rows]
  have ht : ‖∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ * ‖row lam l₃ K N α x H H₁ b m‖ := by
    simpa only [norm_mul] using
      (norm_sum_le (Ioc ⌊M⌋₊ ⌊M₁⌋₊) (fun m => a m * row lam l₃ K N α x H H₁ b m))
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (sum_mul_sq_le_sq_mul_sq _ _ _)

/-- The finite correlation expansion on Tolev 1999 page 83 before display 55.
The phase depends on the difference of the two second variables.
This identity uses no coefficient estimate or minor arc input. -/
theorem energy_eq_correlations (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (b : ℕ → ℂ) :
    (energy lam l₃ K N α x M M₁ H H₁ b : ℂ) =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ∑ l₁ ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, ∑ l₂ ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
        if (x < (m * l₁ : ℕ) ∧ (m * l₁ : ℕ) ≤ 2 * x ∧ m * l₁ ≤ N) ∧
            (x < (m * l₂ : ℕ) ∧ (m * l₂ : ℕ) ≤ 2 * x ∧ m * l₂ ≤ N) then
          b l₁ * conj (b l₂) *
            ((L2Bound.weight lam l₃ K (m * l₁) * L2Bound.weight lam l₃ K (m * l₂) : ℝ) : ℂ) *
            ee (α * m * ((l₁ : ℝ) - l₂))
        else 0 := by
  simp only [energy, Complex.ofReal_sum]
  apply sum_congr rfl
  intro m hm
  rw [sq_norm_eq_mul_conj]
  simp only [row, map_sum]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro l₁ hl₁
  apply sum_congr rfl
  intro l₂ hl₂
  by_cases h₁ : x < (m * l₁ : ℕ) ∧ (m * l₁ : ℕ) ≤ 2 * x ∧ m * l₁ ≤ N
  · by_cases h₂ : x < (m * l₂ : ℕ) ∧ (m * l₂ : ℕ) ≤ 2 * x ∧ m * l₂ ≤ N
    · simp only [h₁, h₂, and_self, ite_true, map_mul, Complex.conj_ofReal, conj_ee,
        Complex.ofReal_mul]
      have he : ee (α * (m * l₁ : ℕ)) * ee (-(α * (m * l₂ : ℕ))) =
          ee (α * m * ((l₁ : ℝ) - l₂)) := by
        rw [← ee_add]
        congr 1
        push_cast
        ring
      calc
        _ = b l₁ * conj (b l₂) *
            ((L2Bound.weight lam l₃ K (m * l₁) : ℂ) * L2Bound.weight lam l₃ K (m * l₂)) *
            (ee (α * (m * l₁ : ℕ)) * ee (-(α * (m * l₂ : ℕ)))) := by ring
        _ = _ := by rw [he]
    · simp only [h₁, h₂, true_and, and_false, ite_true, ite_false, map_zero, mul_zero]
  · simp only [h₁, false_and, ite_false, zero_mul]

/-- The exclusion part of Tolev 1999 page 85 display 62.
A reduced approximation inside a major arc radius has denominator above Q on the minor arcs.
This does not assert existence of a rational approximation. -/
theorem denominator_gt_Q (Q τ α : ℝ) (q a : ℕ)
    (hminor : α ∉ majorArcs Q τ) (hq : 1 ≤ q) (ha : a < q)
    (hcop : Nat.Coprime a q) (herr : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * τ)) :
    Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have hmem : q ∈ Icc 1 ⌊Q⌋₊ := mem_Icc.mpr ⟨hq, (Nat.le_floor hqQ)⟩
  apply hminor
  simp only [majorArcs, Set.mem_iUnion]
  refine ⟨q, hmem, a, ?_, ?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr ha, hcop⟩
  · rcases abs_le.mp herr with ⟨hl, hr⟩
    constructor <;> linarith

/-- The shell adaptation of Tolev 1999 page 85 displays 61 and 62.
This is the algebraic saving once the denominator bounds have been supplied.
It does not assert existence of a rational approximation. -/
theorem denominator_ratios (A : ℝ) (N : ℕ) (x q : ℝ)
    (hN : 0 < N) (hL : 0 < Real.log N)
    (hqQ : Qof A N ≤ q) (hqt : q ≤ τof A N)
    (hx : (N : ℝ) * Real.log N ^ (-4 * A) ≤ x) :
    1 / q ≤ Real.log N ^ (-(20 * A)) ∧ q / x ≤ Real.log N ^ (-(16 * A)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ : 0 < Qof A N := Real.rpow_pos_of_pos hL _
  have hx0 : 0 < x := (mul_pos hNr (Real.rpow_pos_of_pos hL _)).trans_le hx
  constructor
  · have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hQ hqQ
    simpa only [Qof, one_div, Real.rpow_neg hL.le] using hb
  · apply (div_le_iff₀ hx0).mpr
    have ht : τof A N = ((N : ℝ) * Real.log N ^ (-4 * A)) * Real.log N ^ (-(16 * A)) := by
      calc
        _ = (N : ℝ) * Real.log N ^ (-(20 * A)) := by
          rw [τof, Qof, Real.rpow_neg hL.le, div_eq_mul_inv]
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_add hL]
          congr 1
          ring
    calc
      q ≤ τof A N := hqt
      _ = _ := ht
      _ ≤ x * Real.log N ^ (-(16 * A)) :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hL.le _)
      _ = _ := by ring

open LeanLab.HeathBrown1985

/-- The elementary reciprocal mean of the ordered divisor function.
Tolev 1999 page 72 Lemma 8, the convolution count used for part i. -/
theorem zeta_power_reciprocal (k N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n ≤ Hn N ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_div, zero_div, sum_ite_eq', pow_zero]
    split_ifs <;> norm_num
  | succ k ih =>
    have hpoint : ∀ n ∈ Icc 1 N,
        (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n =
          ∑ d ∈ Icc 1 N, if d ∣ n then (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / n else 0 := by
      intro n hn
      rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.cast_sum, sum_div,
        divisors_eq_filter N n hn, sum_filter]
    have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) / n) =
        ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) *
          ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (n : ℝ)⁻¹ := by
      rw [sum_congr rfl hpoint, sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    rw [he]
    calc
      _ ≤ ∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) * (Hn N / d) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (sum_inv_multiples_le N d (mem_Icc.mp hd).1)
          (Nat.cast_nonneg _)
      _ = (∑ d ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) d : ℕ) : ℝ) / d) * Hn N := by
        rw [sum_mul]
        apply sum_congr rfl
        intro d hd
        ring
      _ ≤ Hn N ^ k * Hn N := mul_le_mul_of_nonneg_right ih (Hn_nonneg N)
      _ = _ := (pow_succ _ _).symm

/-- The ordinary mean of a convolution power of zeta follows from reciprocal counting.
Tolev 1999 page 72 Lemma 8, the ordered divisor average behind part i. -/
theorem zeta_power_sum (k N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ) ≤
      (N : ℝ) * Hn N ^ k := by
  have hi : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have he : (∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ (k + 1)) n : ℕ) : ℝ)) =
      ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N / n : ℕ) : ℝ) := by
    have hh := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (ArithmeticFunction.zeta ^ k) N
    simp only [ArithmeticFunction.natCoe_nat, ← pow_succ, ← hi, Nat.cast_id] at hh
    exact_mod_cast hh
  rw [he]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) * ((N : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ k) n : ℕ) : ℝ) / n := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (zeta_power_reciprocal k N) (Nat.cast_nonneg N)

/-- A joint multiset has arbitrary prescribed marginals of the same cardinality.
This counting inequality is the local factor comparison for Tolev 1999 page 72 Lemma 8 part i. -/
theorem multichoose_mul_le (k l e : ℕ) :
    Nat.multichoose k e * Nat.multichoose l e ≤ Nat.multichoose (k * l) e := by
  classical
  have hs : ∀ e, Function.Surjective (fun s : Sym (Fin k × Fin l) e =>
      (s.map Prod.fst, s.map Prod.snd)) := by
    intro e
    induction e with
    | zero =>
      intro st
      exact ⟨Sym.nil, Subsingleton.elim _ _⟩
    | succ e ih =>
      rintro ⟨s, t⟩
      obtain ⟨a, s, rfl⟩ := Sym.exists_eq_cons_of_succ s
      obtain ⟨b, t, rfl⟩ := Sym.exists_eq_cons_of_succ t
      obtain ⟨u, hu⟩ := ih (s, t)
      have hu1 : Sym.map Prod.fst u = s := congrArg Prod.fst hu
      have hu2 : Sym.map Prod.snd u = t := congrArg Prod.snd hu
      refine ⟨Sym.cons (a, b) u, ?_⟩
      apply Prod.ext
      · simp only [Sym.map_cons]
        rw [hu1]
      · simp only [Sym.map_cons]
        rw [hu2]
  have hc := Fintype.card_le_of_surjective _ (hs e)
  simpa only [Fintype.card_prod, Sym.card_sym_eq_multichoose, Fintype.card_fin] using hc

/-- The local ordered divisor count is a multiset count.
This identifies the convolution power used in Tolev 1999 page 72 Lemma 8. -/
theorem zeta_power_prime_pow (k p e : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.zeta ^ (k + 1)) (p ^ e) = Nat.multichoose (k + 1) e := by
  induction k generalizing e with
  | zero =>
    simp [ArithmeticFunction.zeta_apply_ne (pow_ne_zero _ hp.ne_zero), Nat.multichoose_one]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    rw [show k + 1 + 1 + e - 1 = e + (k + 1) by omega]
    exact Nat.choose_symm_add.symm

/-- Tau5 squared is bounded pointwise by the 25th convolution power of zeta.
This is the elementary majorant for the squared moment in Tolev 1999 page 72 Lemma 8 part i. -/
theorem tau5_sq_le_zeta25 (n : ℕ) : tau5 n ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) n := by
  have hm5 : (ArithmeticFunction.zeta ^ 5).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have hm25 : (ArithmeticFunction.zeta ^ 25).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp [tau5]
  · intro p e hp
    change (ArithmeticFunction.zeta ^ (4 + 1)) (p ^ e) ^ 2 ≤
      (ArithmeticFunction.zeta ^ (24 + 1)) (p ^ e)
    rw [zeta_power_prime_pow 4 p e hp, zeta_power_prime_pow 24 p e hp]
    simpa only [pow_two] using multichoose_mul_le 5 5 e
  · intro a b ha hb hab hIa hIb
    change ((ArithmeticFunction.zeta ^ 5) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 25) (a * b)
    rw [hm5.map_mul_of_coprime hab, hm25.map_mul_of_coprime hab, mul_pow]
    exact Nat.mul_le_mul hIa hIb

/-- LEAF. Tolev 1999 page 72 Lemma 8 part i with k equal to five,
and page 83 before display 55. This is a coefficient moment without a phase,
a modulus, a residue, a minor arc or a second coefficient.
The absolute constant two times five to the 24th is supplied. -/
theorem coefficient_mass :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ M M₁ : ℝ, 0 < M → M ≤ M₁ → M₁ ≤ 2 * M → M ≤ 2 * N →
      ∀ a : ℕ → ℂ, (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
        (∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ‖a m‖ ^ 2) ≤
          D * M * Real.log N ^ (26 : ℕ) := by
  refine ⟨2 * 5 ^ (24 : ℕ), by positivity, ?_⟩
  intro N hN M M₁ hM hMM₁ hM₁ hMN a ha
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 ≤ Real.log N := by linarith
  let R : ℕ := ⌊2 * M⌋₊
  have hR : (R : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
  have hRN : (R : ℝ) ≤ 4 * N := by nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogR : Real.log R ≤ Real.log (4 : ℝ) + Real.log N := by
    rcases Nat.eq_zero_or_pos R with hz | hp
    · simp only [hz, Nat.cast_zero, Real.log_zero]
      have h4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      positivity
    · rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (N : ℝ) ≠ 0)]
      exact Real.log_le_log (by exact_mod_cast hp) hRN
  have hH : Hn R ≤ 5 * Real.log N := (Hn_le R).trans (by linarith)
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Icc 1 R := by
    intro m hm
    rcases mem_Ioc.mp hm with ⟨hm0, hm1⟩
    exact mem_Icc.mpr ⟨by omega, hm1.trans (Nat.floor_le_floor hM₁)⟩
  have ht : ∀ m, ‖a m‖ ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) := by
    intro m
    have hτ : (tau5 m : ℝ) ^ 2 ≤ (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) := by
      exact_mod_cast tau5_sq_le_zeta25 m
    calc
      _ ≤ ((tau5 m : ℝ) * Real.log N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (ha m) 2
      _ = (tau5 m : ℝ) ^ 2 * Real.log N ^ (2 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hτ (sq_nonneg _)
  calc
    _ ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
      sum_le_sum (fun m hm => ht m)
    _ ≤ ∑ m ∈ Icc 1 R,
        (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ) * Real.log N ^ (2 : ℕ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => by positivity)
    _ = (∑ m ∈ Icc 1 R, (((ArithmeticFunction.zeta ^ 25) m : ℕ) : ℝ)) *
        Real.log N ^ (2 : ℕ) := by rw [sum_mul]
    _ ≤ ((R : ℝ) * Hn R ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (zeta_power_sum 24 R) (sq_nonneg _)
    _ ≤ ((2 * M) * (5 * Real.log N) ^ (24 : ℕ)) * Real.log N ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hR (pow_le_pow_left₀ (Hn_nonneg R) hH 24) (by positivity) (by positivity)
    _ = _ := by ring


/-- Tolev 1999 page 84 display 57, the elementary lcm fiber majorant. -/
theorem lcm_fiber_divisor_bound (h K : ℕ) :
    ∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
      (p.1.divisors.card : ℝ) * p.2.divisors.card ≤ (h.divisors.card : ℝ) ^ 4 := by
  by_cases hh : h = 0
  · subst h
    have he : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = 0) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases mem_filter.mp hp with ⟨hp, he⟩
      rcases mem_product.mp hp with ⟨hp1, hp2⟩
      have h1 := (mem_Icc.mp hp1).1
      have h2 := (mem_Icc.mp hp2).1
      exact (Nat.lcm_ne_zero (by omega) (by omega)) he
    rw [he]
    norm_num
  · have hs : (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h) ⊆
        h.divisors ×ˢ h.divisors := by
      intro p hp
      have he := (mem_filter.mp hp).2
      apply mem_product.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_left p.1 p.2, hh⟩
      · exact Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_right p.1 p.2, hh⟩
    calc
      _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (p.1.divisors.card : ℝ) * p.2.divisors.card :=
        sum_le_sum_of_subset_of_nonneg hs (fun p hp hn => by positivity)
      _ ≤ ∑ p ∈ h.divisors ×ˢ h.divisors, (h.divisors.card : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p hp
        have hp1 := (mem_product.mp hp).1
        have hp2 := (mem_product.mp hp).2
        have hd1 : (p.1.divisors.card : ℝ) ≤ h.divisors.card := by
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp1))
        have hd2 : (p.2.divisors.card : ℝ) ≤ h.divisors.card := by
          exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hh (Nat.dvd_of_mem_divisors hp2))
        simpa only [pow_two] using mul_le_mul hd1 hd2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul]
        ring

/-- Tolev 1999 page 84 display 58, in a stronger harmonic form.
This proves the lcm sum that occurs in the Type II diagonal term. -/
theorem lcm_divisor_sum (K : ℕ) :
    ∑ p ∈ Icc 1 K ×ˢ Icc 1 K,
      ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2 ≤
        LeanLab.HeathBrown1985.Hn (K * K) ^ (16 : ℕ) := by
  have hm : ∀ p ∈ Icc 1 K ×ˢ Icc 1 K, Nat.lcm p.1 p.2 ∈ Icc 1 (K * K) := by
    intro p hp
    rcases mem_product.mp hp with ⟨hp1, hp2⟩
    rcases mem_Icc.mp hp1 with ⟨h1, h1K⟩
    rcases mem_Icc.mp hp2 with ⟨h2, h2K⟩
    apply mem_Icc.mpr
    constructor
    · exact Nat.lcm_pos (by omega) (by omega)
    · exact (Nat.lcm_le_mul h1 h2).trans (Nat.mul_le_mul h1K h2K)
  have hf := sum_fiberwise_of_maps_to hm
    (fun p : ℕ × ℕ => ((p.1.divisors.card : ℝ) * p.2.divisors.card) / Nat.lcm p.1 p.2)
  rw [← hf]
  calc
    _ = ∑ h ∈ Icc 1 (K * K),
        (∑ p ∈ (Icc 1 K ×ˢ Icc 1 K).filter (fun p => Nat.lcm p.1 p.2 = h),
          (p.1.divisors.card : ℝ) * p.2.divisors.card) / h := by
      apply sum_congr rfl
      intro h hh
      rw [sum_div]
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ h ∈ Icc 1 (K * K), (h.divisors.card : ℝ) ^ (4 : ℕ) / h := by
      apply sum_le_sum
      intro h hh
      exact div_le_div_of_nonneg_right (lcm_fiber_divisor_bound h K) (Nat.cast_nonneg h)
    _ ≤ _ := by simpa only [show (2 : ℕ) ^ 4 = 16 by norm_num] using divisor_power_reciprocal 4 (K * K)

/-- LEAF. Tolev 1999 pages 83 to 86 displays 55 to 63 after the first Cauchy step.
Estimate the row energy only. The arbitrary first coefficient has been removed.
The log exponent 634 leaves slack after the coefficient moment exponent 26.
The fixed residue and 2009 shell adaptation remain OPEN. -/
theorem row_energy :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ b : ℕ → ℂ,
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A) := by
  sorry

/-- The exact sealed Type II statement follows from the coefficient moment and row energy.
CONDITIONAL ON row_energy only. The coefficient moment is proved. -/
theorem typeII_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨D, hD, hm⟩ := coefficient_mass
  obtain ⟨C, N₀, hC, he⟩ := row_energy A hA l₃ hl₃
  refine ⟨D + C + 1, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi a b ha hb
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN3nat : 3 ≤ N := by exact_mod_cast hN3
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith : 1 ≤ x) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).trans hlo
  have hMbound : M ≤ 2 * N := by nlinarith
  have hmass := hm N hN3nat M M₁ hM hMM₁ hM₁ hMbound a ha
  have henergy := he N hodd hN₀ lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi b hb
  have hE0 : 0 ≤ energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := by
    unfold energy
    positivity
  have hp : Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A) =
      (Real.log N ^ (330 - 4 * A)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL, ← Real.rpow_mul_natCast hL.le]
    congr 1
    ring
  have hs := (bilinear_sq_le_energy lam l₃ _ N α x M M₁ H H₁ a b).trans
    (mul_le_mul_of_nonneg_right hmass hE0)
  have hs' : ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ^ 2 ≤
      (D * C) * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 := by
    calc
      _ ≤ (D * M * Real.log N ^ (26 : ℕ)) *
          energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b := hs
      _ = (D * Real.log N ^ (26 : ℕ)) *
          (M * energy lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ b) := by ring
      _ ≤ (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by rw [show (D * Real.log N ^ (26 : ℕ)) *
          (C * (N : ℝ) ^ 2 * Real.log N ^ (634 - 8 * A)) =
          D * C * (N : ℝ) ^ 2 *
            (Real.log N ^ (26 : ℕ) * Real.log N ^ (634 - 8 * A)) by ring, hp]
  have hc : D * C ≤ (D + C + 1) ^ 2 := by nlinarith [sq_nonneg (D - C)]
  have hs'' := hs'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg (N : ℝ)))
    (sq_nonneg (Real.log N ^ (330 - 4 * A))))
  have ht : (D + C + 1) ^ 2 * (N : ℝ) ^ 2 * (Real.log N ^ (330 - 4 * A)) ^ 2 =
      ((D + C + 1) * N * Real.log N ^ (330 - 4 * A)) ^ 2 := by ring
  rw [ht] at hs''
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs''

end LeanLab.Tolev2009.Decomp310b
