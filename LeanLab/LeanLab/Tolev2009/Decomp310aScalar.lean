/-
AI wrote this Lean code. FREE-nv-minimax task144.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98 page 86 displays 65 and 66.
Scalar support for the two exact row leaves of Decomp310a. The progression,
phase cap, divisor moment, Dirichlet approximation and phase average steps
are proved here with clean axioms. No row statement is changed.
-/
import LeanLab.Tolev2009.Decomp286b
import LeanLab.PNTPort.Vinogradov.Count
import LeanLab.PNTPort.LargeSieve.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Coprime.Lemmas

open Finset Real

namespace LeanLab.Tolev2009.Decomp310aScalar

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.HeathBrown1985
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve

/-- The single modulus progression in Tolev 1999 page 86 display 64.
All three product cutoffs and the fixed residue are retained. -/
noncomputable def progression (l₃ k N m : ℕ) (α x H H₁ : ℝ) : ℂ :=
  ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
        (m * l) % k = l₃ % k then ee (α * (m * l : ℕ)) else 0


/-- The geometric majorant in display 65, with its resonance case explicit.
The additional one retains the endpoint in the progression count. -/
noncomputable def phaseCap (α x : ℝ) (n : ℕ) : ℝ :=
  if ee (α * n) = 1 then 2 * x / n + 1
  else min (2 * x / n + 1) (2 / ‖ee (α * n) - 1‖)


/-- The majorant is nonnegative for a nonnegative shell endpoint. -/
theorem phaseCap_nonneg (α x : ℝ) (n : ℕ) (hx : 0 ≤ x) : 0 ≤ phaseCap α x n := by
  unfold phaseCap
  split_ifs <;> positivity


/-- The nearest integer denominator comparison used in Tolev 1999 page 86 display 65.
This supplies the exact constant for the geometric majorant. -/
theorem distance_comparison (t : ℝ) :
    4 * |t - (round t : ℝ)| ≤ ‖ee t - 1‖ := by
  let u : ℝ := t - round t
  have hperiod : ee t = ee u := by
    have h := ee_add u (round t : ℝ)
    rw [ee_int, mul_one] at h
    simpa only [u, sub_add_cancel] using h
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hpi : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hpi
  have hnorm : ‖ee u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
    have he : ee u = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
      unfold ee
      push_cast
      ring_nf
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
    rw [Real.norm_eq_abs, abs_mul]
    norm_num
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hcancel : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    field_simp
  rw [hcancel] at hs
  rw [hperiod, hnorm]
  change 4 * |u| ≤ _
  linarith


/-- The exclusion part of Tolev 1999 page 85 display 62.
A reduced approximation inside a major arc radius has denominator above Q on the minor arcs.
This does not assert existence of a rational approximation. -/
theorem denominator_gt_Q_row (Q τ α : ℝ) (q a : ℕ)
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


/-- The elementary reciprocal mean of the ordered divisor function.
Tolev 1999 page 72 Lemma 8, the convolution count used for part i. -/
theorem zeta_power_reciprocal_row (k N : ℕ) :
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


/-- A joint multiset has arbitrary prescribed marginals of the same cardinality.
This counting inequality is the local factor comparison for Tolev 1999 page 72 Lemma 8 part i. -/
theorem multichoose_mul_le_row (k l e : ℕ) :
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
theorem zeta_power_prime_pow_row (k p e : ℕ) (hp : p.Prime) :
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


/-- The affine parametrization of the finite progression before display 65. -/
theorem progression_affine (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) :
    ∃ β : ℝ, ∃ J : ℕ,
      progression l₃ k N m α x H H₁ =
        ∑ j ∈ range J, ee (β + (j : ℝ) * (α * (m * k : ℕ))) ∧
      (J : ℝ) ≤ 2 * x / (m * k : ℕ) + 1 := by
  classical
  let s := (Ioc ⌊H⌋₊ ⌊H₁⌋₊).filter (fun l =>
    (x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N) ∧
      (m * l) % k = l₃ % k)
  have he : progression l₃ k N m α x H H₁ = ∑ l ∈ s, ee (α * (m * l : ℕ)) := by
    simp only [progression, s, sum_filter]
  have hmk : 0 < (m * k : ℕ) := by positivity
  by_cases hne : s.Nonempty
  · let a := s.min' hne
    let b := s.max' hne
    have ha : a ∈ s := s.min'_mem hne
    have hb : b ∈ s := s.max'_mem hne
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hab : a ≤ b := s.min'_le b hb
    have hkm : Nat.Coprime k m := by
      have hh : Nat.Coprime k (m * a) := by
        change Nat.gcd k (m * a) = 1
        rw [Nat.gcd_rec, ha'.2.2, ← Nat.gcd_rec]
        exact hcop
      exact hh.of_dvd_right (dvd_mul_right m a)
    have hmod : ∀ l ∈ s, a ≡ l [MOD k] := by
      intro l hl
      have hl' := mem_filter.mp hl
      exact Nat.ModEq.cancel_left_of_coprime hkm (ha'.2.2.trans hl'.2.2.symm)
    have hdiv : k ∣ b - a := (hmod b hb).dvd'
    have hbe : b = a + ((b - a) / k) * k := by
      rw [Nat.div_mul_cancel hdiv]
      omega
    let J := (b - a) / k + 1
    have hbetween : ∀ j < J, a ≤ a + j * k ∧ a + j * k ≤ b := by
      intro j hj
      dsimp [J] at hj
      constructor
      · omega
      · have hh := Nat.mul_le_mul_right k (show j ≤ (b - a) / k by omega)
        omega
    have hmem : ∀ j < J, a + j * k ∈ s := by
      intro j hj
      obtain ⟨hlo, hhi⟩ := hbetween j hj
      apply mem_filter.mpr
      constructor
      · exact mem_Ioc.mpr ⟨(mem_Ioc.mp ha'.1).1.trans_le hlo,
          hhi.trans (mem_Ioc.mp hb'.1).2⟩
      · have hprodlo : m * a ≤ m * (a + j * k) := Nat.mul_le_mul_left m hlo
        have hprodhi : m * (a + j * k) ≤ m * b := Nat.mul_le_mul_left m hhi
        constructor
        · refine ⟨ha'.2.1.1.trans_le (by exact_mod_cast hprodlo),
            (by exact_mod_cast hprodhi : ((m * (a + j * k) : ℕ) : ℝ) ≤ (m * b : ℕ)).trans hb'.2.1.2.1,
            hprodhi.trans hb'.2.1.2.2⟩
        · simpa [Nat.mul_add_mod, Nat.mul_mod, Nat.add_mod, Nat.mul_assoc] using ha'.2.2
    have hs : s = (range J).image (fun j => a + j * k) := by
      ext l
      constructor
      · intro hl
        have hal : a ≤ l := s.min'_le l hl
        have hlb : l ≤ b := s.le_max' l hl
        have hdl : k ∣ l - a := (hmod l hl).dvd'
        refine mem_image.mpr ⟨(l - a) / k, mem_range.mpr ?_, ?_⟩
        · dsimp [J]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : l - a ≤ b - a))
        · rw [Nat.div_mul_cancel hdl]
          omega
      · intro hl
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hl
        exact hmem j (mem_range.mp hj)
    refine ⟨α * (m * a : ℕ), J, ?_, ?_⟩
    · rw [he, hs, sum_image]
      · apply sum_congr rfl
        intro j hj
        congr 1
        push_cast
        ring
      · intro j hj j' hj' heq
        have hh : j * k = j' * k := Nat.add_left_cancel heq
        exact (Nat.mul_right_cancel (by omega : 0 < k) hh)
    · have hmkpos : (0 : ℝ) < (m * k : ℕ) := by exact_mod_cast hmk
      have hbprod : (m : ℝ) * b ≤ 2 * x := by
        simpa only [Nat.cast_mul] using hb'.2.1.2.1
      have hbeR : (b : ℝ) = a + ((b - a) / k : ℕ) * (k : ℝ) := by exact_mod_cast hbe
      have hJR : (J : ℝ) = ((b - a) / k : ℕ) + 1 := by simp [J]
      have hnum : ((J : ℝ) - 1) * (m * k : ℕ) ≤ 2 * x := by
        rw [hJR]
        push_cast
        have hh := congrArg (fun t : ℝ => (m : ℝ) * t) hbeR
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)
          (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)]
      have hquot : (J : ℝ) - 1 ≤ 2 * x / (m * k : ℕ) :=
        (le_div_iff₀ hmkpos).mpr hnum
      linarith
  · refine ⟨0, 0, ?_, ?_⟩
    · rw [he, not_nonempty_iff_eq_empty.mp hne]
      simp
    · have : (0 : ℝ) ≤ 2 * x / (m * k : ℕ) := by positivity
      simpa using (show (0 : ℝ) ≤ 2 * x / (m * k : ℕ) + 1 by linarith)


/-- The finite convolution regrouping in Tolev 1999 page 86 display 65.
It bounds the restricted coefficient rectangle by the sixth convolution of zeta. -/
theorem convolution_reduction (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (L U K : ℕ) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, F (m*k) ≤
      ∑ n ∈ Icc 1 (U*K), (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n := by
  classical
  by_cases hU : U = 0
  · subst U; simp
  by_cases hK : K = 0
  · subst K; simp
  let T := U*K
  have hUT : U ≤ T := Nat.le_mul_of_pos_right U (Nat.pos_of_ne_zero hK)
  have hKT : K ≤ T := Nat.le_mul_of_pos_left K (Nat.pos_of_ne_zero hU)
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 T) :
      (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n =
        ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1*p.2=n),
          (tau5 p.1 : ℝ) * F n := by
    rw [show (6 : ℕ) = 5+1 by norm_num, pow_succ, ArithmeticFunction.mul_apply,
      Nat.cast_sum, sum_mul]
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2]
    apply sum_congr rfl
    intro p hp
    have hp0 : p.2 ≠ 0 := by have := (mem_Ioc.mp (mem_product.mp (mem_filter.mp hp).1).2).1; omega
    simp [tau5, ArithmeticFunction.zeta_apply, hp0]
  have he : (∑ n ∈ Icc 1 T, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) * F n) =
      ∑ p ∈ (Ioc 0 T ×ˢ Ioc 0 T).filter (fun p : ℕ × ℕ => p.1*p.2 ≤ T),
        (tau5 p.1 : ℝ) * F (p.1*p.2) := by
    rw [sum_congr rfl hpoint]
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    have hpos : 0 < p.1*p.2 := Nat.mul_pos (mem_Ioc.mp (mem_product.mp hp).1).1 (mem_Ioc.mp (mem_product.mp hp).2).1
    simp only [sum_ite_eq, mem_Icc]
    by_cases hh : p.1*p.2 ≤ T
    · simp [hh, show 1 ≤ p.1*p.2 by omega]
    · simp [hh]
  simp_rw [mul_sum]
  rw [he, ← sum_product']
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hm, hk⟩ := mem_product.mp hp
    have hm' := mem_Ioc.mp hm
    have hk' := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨by omega, hm'.2.trans hUT⟩,
      mem_Ioc.mpr ⟨by omega, hk'.2.trans hKT⟩⟩, Nat.mul_le_mul hm'.2 hk'.2⟩
  · intro p hp hnot
    exact mul_nonneg (Nat.cast_nonneg _) (hF _)


/-- The joint multiset majorant for the squared sixth divisor coefficient.
This supplies the moment component of Tolev 1999 page 86 display 65. -/
theorem zeta6_sq_le_zeta36_nat (n : ℕ) :
    (ArithmeticFunction.zeta ^ 6) n ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) n := by
  have hm6 : (ArithmeticFunction.zeta ^ 6).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  have hm36 : (ArithmeticFunction.zeta ^ 36).IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.pow
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p e hp
    change (ArithmeticFunction.zeta ^ (5 + 1)) (p ^ e) ^ 2 ≤
      (ArithmeticFunction.zeta ^ (35 + 1)) (p ^ e)
    rw [zeta_power_prime_pow_row 5 p e hp, zeta_power_prime_pow_row 35 p e hp]
    simpa only [pow_two] using multichoose_mul_le_row 6 6 e
  · intro a b ha hb hab hIa hIb
    change ((ArithmeticFunction.zeta ^ 6) (a * b)) ^ 2 ≤ (ArithmeticFunction.zeta ^ 36) (a * b)
    rw [hm6.map_mul_of_coprime hab, hm36.map_mul_of_coprime hab, mul_pow]
    exact Nat.mul_le_mul hIa hIb


/-- The same pointwise comparison after casting to real coefficients. -/
theorem zeta6_sq_le_zeta36 (n : ℕ) :
    (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 ≤
      (((ArithmeticFunction.zeta ^ 36) n : ℕ) : ℝ) := by
  exact_mod_cast zeta6_sq_le_zeta36_nat n


 /-- The reciprocal squared sixth divisor moment in the scalar Cauchy step. -/
theorem zeta6_sq_reciprocal (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ) ^ 2 / n ≤
      Hn N ^ 36 := by
  apply le_trans (sum_le_sum (fun n hn =>
    div_le_div_of_nonneg_right (zeta6_sq_le_zeta36 n) (Nat.cast_nonneg n)))
  exact zeta_power_reciprocal_row 36 N


/-- The geometric cap retains its endpoint count, Tolev page 86 display 65. -/
theorem phaseCap_le_count (α x : ℝ) (n : ℕ) : phaseCap α x n ≤ 2*x/n+1 := by
  unfold phaseCap
  split_ifs
  · rfl
  · exact min_le_left _ _


/-- The weighted finite Cauchy step in display 65, retaining the count one. -/
theorem weighted_phase_cauchy (a : ℕ → ℝ) (T : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, (a n) ^ 2 / n) *
        ((2*x + T) * ∑ n ∈ Icc 1 T, phaseCap α x n) := by
  let f : ℕ → ℝ := fun n => (a n)^2 / n
  let g : ℕ → ℝ := fun n => (n : ℝ) * phaseCap α x n ^ 2
  have hc : (∑ n ∈ Icc 1 T, a n * phaseCap α x n) ^ 2 ≤
      (∑ n ∈ Icc 1 T, f n) * (∑ n ∈ Icc 1 T, g n) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      dsimp [f]
      positivity
    · intro n hn
      dsimp [g]
      positivity
    · intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
      dsimp [f, g]
      apply le_of_eq
      field_simp
  have hg : (∑ n ∈ Icc 1 T, g n) ≤ (2*x+T) * ∑ n ∈ Icc 1 T, phaseCap α x n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    have hnT : (n : ℝ) ≤ T := by exact_mod_cast (mem_Icc.mp hn).2
    have hp := phaseCap_nonneg α x n hx
    have hcap : phaseCap α x n - 1 ≤ 2*x/n := by linarith [phaseCap_le_count α x n]
    have hcap' := (le_div_iff₀ hn0).mp hcap
    have hh : (n : ℝ) * phaseCap α x n ≤ 2*x+T := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh hp
    dsimp [g]
    nlinarith
  exact hc.trans (mul_le_mul_of_nonneg_left hg (sum_nonneg (fun n hn => by dsimp [f]; positivity)))


/-- The finite rectangle bound after Cauchy and the proved coefficient moment.
This is the coefficient part of Tolev page 86 display 65. -/
theorem rectangle_phase_sq_le (L U K : ℕ) (α x : ℝ) (hx : 0 ≤ x) :
    (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k)) ^ 2 ≤
      Hn (U*K) ^ 36 * ((2*x + (U*K : ℕ)) *
        ∑ n ∈ Icc 1 (U*K), phaseCap α x n) := by
  have hconv := convolution_reduction (phaseCap α x) (fun n => phaseCap_nonneg α x n hx) L U K
  have hpos : 0 ≤ ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k) := by
    apply sum_nonneg
    intro m hm
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun k hk => phaseCap_nonneg α x (m*k) hx)
  apply (pow_le_pow_left₀ hpos hconv 2).trans
  apply (weighted_phase_cauchy (fun n => (((ArithmeticFunction.zeta ^ 6) n : ℕ) : ℝ)) (U*K) α x hx).trans
  apply mul_le_mul_of_nonneg_right (zeta6_sq_reciprocal (U*K))
  exact mul_nonneg (by positivity) (sum_nonneg (fun n hn => phaseCap_nonneg α x n hx))


/-- The exact complex cap is at most the standard nearest integer cap plus one. -/
theorem phaseCap_le_G_add_one (α x : ℝ) (n : ℕ) :
    phaseCap α x n ≤ LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n) + 1 := by
  by_cases hd : dist0 (α*n) = 0
  · rw [LeanLab.PNTPort.Vinogradov.G, if_pos hd]
    exact phaseCap_le_count α x n
  · have hdpos : 0 < dist0 (α*n) := lt_of_le_of_ne (dist0_nonneg _) (Ne.symm hd)
    have hdist : 4 * dist0 (α*n) ≤ ‖ee (α*n)-1‖ := distance_comparison _
    have hden : 0 < ‖ee (α*n)-1‖ := by linarith
    have he : ee (α*n) ≠ 1 := by
      intro hh
      simp [hh] at hden
    have hdiv : 2 / ‖ee (α*n)-1‖ ≤ 1 / (2*dist0 (α*n)) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    rw [phaseCap, if_neg he, LeanLab.PNTPort.Vinogradov.G, if_neg hd, ← min_add_add_right]
    apply le_min
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hdiv.trans (by linarith))


/-- The rational approximation reciprocal sum in Tolev page 72 Lemma 7 part ii. -/
theorem phaseCap_sum_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α x : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ)^2) (hx : 0 ≤ x) (T : ℕ) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤
      12 * (2*x/q + T + q) * (1 + Real.log q + Real.log T) + T := by
  calc
    _ ≤ ∑ n ∈ Icc 1 T, (LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n) + 1) :=
      sum_le_sum (fun n hn => phaseCap_le_G_add_one α x n)
    _ = (∑ n ∈ Icc 1 T, LeanLab.PNTPort.Vinogradov.G (2*x/n) (α*n)) + T := by
      rw [sum_add_distrib]
      simp
    _ ≤ _ := add_le_add (sum_G_div_le hq hcop hα T (by positivity : 0 ≤ 2*x)) le_rfl


/-- Minor arcs exclude small reduced denominators, including the shifted interval endpoints. -/
theorem integer_denominator_gt_Q (Q τ α : ℝ) (q : ℕ) (a : ℤ)
    (hQ : 0 ≤ Q) (hτ : Q+1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1/τ) (1-1/τ)) (hminor : α ∉ majorArcs Q τ)
    (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (herr : |α - (a : ℝ)/q| ≤ 1/((q : ℝ)*τ)) : Q < q := by
  by_contra hn
  have hqQ : (q : ℝ) ≤ Q := le_of_not_gt hn
  have ht : 0 < τ := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : |(q : ℝ)*α-a| ≤ 1/τ := by
    have hh := mul_le_mul_of_nonneg_left herr hqr.le
    rw [show (q : ℝ) * |α - (a : ℝ)/q| = |(q : ℝ)*α-a| by
      rw [← abs_of_pos hqr, ← abs_mul, abs_of_pos hqr]
      congr 1
      field_simp] at hh
    convert hh using 1
    field_simp
  have hlo := (abs_le.mp he).1
  have hhi := (abs_le.mp he).2
  have hlα := mul_lt_mul_of_pos_left hα.1 hqr
  have huα := mul_lt_mul_of_pos_left hα.2 hqr
  have hqτ : (q : ℝ)+1 ≤ τ := by linarith
  have hl : (-1 : ℝ) < a := by
    have hh : (q : ℝ)/τ + 1/τ ≤ 1 := by
      rw [← add_div, div_le_one ht]
      exact hqτ
    have hm : (q : ℝ)*(-1/τ) = -(q:ℝ)/τ := by ring
    rw [hm, neg_div] at hlα
    linarith
  have hu : (a : ℝ) < q := by
    have hh : 1/τ ≤ (q : ℝ)/τ := div_le_div_of_nonneg_right (by exact_mod_cast hq) ht.le
    have hm : (q : ℝ)*(1-1/τ) = q-(q:ℝ)/τ := by ring
    rw [hm] at huα
    linarith
  have ha0 : 0 ≤ a := by exact_mod_cast (show (-1 : ℤ) < a by exact_mod_cast hl)
  have haq : a < (q : ℤ) := by exact_mod_cast hu
  have hac : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
  have hc : Nat.Coprime a.toNat q := by
    apply IsCoprime.natCoprime
    simpa only [hac] using hcop
  have haqr : a.toNat < q := by omega
  have her : |α - (a.toNat : ℝ)/q| ≤ 1/((q : ℝ)*τ) := by
    simpa only [show (a.toNat : ℝ) = (a : ℝ) by exact_mod_cast hac] using herr
  exact (not_lt_of_ge hqQ) (denominator_gt_Q_row Q τ α q a.toNat hminor hq haqr hc her)


/-- Dirichlet approximation with both required error bounds and an integer numerator. -/
theorem minor_arc_reduced_approximation (Q τ α : ℝ)
    (hQ : 0 ≤ Q) (hτ : Q+1 ≤ τ) (ht : 1 ≤ τ)
    (hα : α ∈ Set.Ioo (-1/τ) (1-1/τ)) (hminor : α ∉ majorArcs Q τ) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Q < (q : ℝ) ∧ (q : ℝ) ≤ τ ∧
      IsCoprime a (q : ℤ) ∧
      |α - (a : ℝ)/q| ≤ 1/((q : ℝ)*τ) ∧
      |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2 := by
  have hfloor : 0 < ⌊τ⌋₊ := by
    have hh : 1 ≤ ⌊τ⌋₊ := (Nat.le_floor (by simpa using ht))
    omega
  obtain ⟨r, herr, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le α hfloor
  have hq : 1 ≤ r.den := Rat.pos r
  have hqt : (r.den : ℝ) ≤ τ :=
    (show (r.den : ℝ) ≤ ⌊τ⌋₊ by exact_mod_cast hr).trans (Nat.floor_le (by linarith))
  have htf : τ ≤ (⌊τ⌋₊ : ℝ)+1 := (Nat.lt_floor_add_one τ).le
  have hqr : (0 : ℝ) < r.den := by exact_mod_cast Rat.pos r
  have he : |α - (r.num : ℝ)/r.den| ≤ 1/((r.den : ℝ)*τ) := by
    rw [← Rat.cast_def]
    apply herr.trans
    apply one_div_le_one_div_of_le (mul_pos hqr (by linarith))
    nlinarith
  have he2 : |α - (r.num : ℝ)/r.den| ≤ 1/(r.den : ℝ)^2 := by
    apply he.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hqr)
    nlinarith
  exact ⟨r.num, r.den, hq,
    integer_denominator_gt_Q Q τ α r.den r.num hQ hτ hα hminor hq r.isCoprime_num_den he,
    hqt, r.isCoprime_num_den, he, he2⟩


/-- The major arc parameters obey the separation condition for all sufficiently large N. -/
theorem eventual_minor_arc_parameters (A : ℝ) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ Real.log N ∧ Qof A N + 1 ≤ τof A N := by
  have he := (isLittleO_log_rpow_rpow_atTop (40*A) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨max X₀ (Real.exp 2), ?_⟩
  intro N hN
  have hNe : Real.exp 2 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := (Real.exp_pos 2).trans_le hNe
  have hL : 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hL0 : 0 < Real.log N := by linarith
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have hbound := hX (N : ℝ) ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), abs_of_pos hN0] at hbound
  have hQsq : Qof A N ^ 2 = Real.log N ^ (40*A) := by
    rw [Qof, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    congr 1
    ring
  refine ⟨hL, ?_⟩
  unfold τof
  apply (le_div_iff₀ hQ0).mpr
  rw [← hQsq] at hbound
  nlinarith


/-- The product cutoff retains the full logarithmic saving in the Type I shell. -/
theorem shell_product_bound (A : ℝ) (N : ℕ) (x M H : ℝ)
    (hA : 10000 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) (hH : 0 < H)
    (hMH : M*H ≤ 2*x) (hHlo : x^((249:ℝ)/500) ≤ H) :
    let T := ⌊2*M⌋₊ * cutoff3 (10000*A) N
    (T : ℝ) ≤ 4*N*Real.log N^(-10000*A) ∧
    (T : ℝ) ≤ N ∧
    (T : ℝ) ≤ 4*N*Real.log N^(-20*A) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hp : 0 < x^((249:ℝ)/500) := Real.rpow_pos_of_pos hx _
  have hmp : M*x^((249:ℝ)/500) ≤ 2*x :=
    (mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH
  have hm : M ≤ 2*x^((251:ℝ)/500) := by
    have hh : M ≤ 2*x / x^((249:ℝ)/500) := (le_div_iff₀ hp).mpr hmp
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1:ℝ)-(249:ℝ)/500 = (251:ℝ)/500 by norm_num, Real.rpow_one] using Real.rpow_sub hx 1 ((249:ℝ)/500)
  have hmN : M ≤ 2*(N:ℝ)^((251:ℝ)/500) :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by norm_num))
  have hf : (⌊2*M⌋₊ : ℝ) ≤ 2*M := Nat.floor_le (by positivity)
  have hk : (cutoff3 (10000*A) N : ℝ) ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A) :=
    by
      unfold cutoff3
      have hh := Nat.floor_le (show 0 ≤ (N:ℝ)^((1:ℝ)/3)*Real.log N^(-(10000*A)) by positivity)
      simpa only [neg_mul] using hh
  have hfirst : ((⌊2*M⌋₊ * cutoff3 (10000*A) N : ℕ) : ℝ) ≤
      4*(N:ℝ)*Real.log N^(-10000*A) := by
    push_cast
    calc
      _ ≤ (2*M)*((N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A)) :=
        mul_le_mul hf hk (Nat.cast_nonneg _) (by positivity)
      _ ≤ (2*(2*(N:ℝ)^((251:ℝ)/500)))*((N:ℝ)^((1:ℝ)/3)*Real.log N^(-10000*A)) := by
        gcongr
      _ = 4*(N:ℝ)^((1253:ℝ)/1500)*Real.log N^(-10000*A) := by
        rw [show (1253:ℝ)/1500 = (251:ℝ)/500 + 1/3 by norm_num, Real.rpow_add hN0]
        ring
      _ ≤ _ := by
        have hh : (N:ℝ)^((1253:ℝ)/1500) ≤ N := by
          convert Real.rpow_le_rpow_of_exponent_le hN (show (1253:ℝ)/1500 ≤ 1 by norm_num) using 1 <;> simp
        gcongr
  have hs : Real.log N^(-10000*A) ≤ (1:ℝ)/4 := by
    calc
      _ ≤ Real.log N^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ (2:ℝ)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = 1/4 := by norm_num
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      _ ≤ 4*(N:ℝ)*Real.log N^(-10000*A) := hfirst
      _ ≤ 4*(N:ℝ)*(1/4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)


/-- The rational approximation mass estimate with the exact third cutoff savings. -/
theorem phase_mass_from_approx (A : ℝ) (N T q : ℕ) (a : ℤ) (α x : ℝ)
    (hA : 0 ≤ A) (hN : 0 < (N : ℝ)) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hTN : T ≤ N)
    (hTS : (T : ℝ) ≤ 4 * N * Real.log N ^ (-20*A))
    (hq : 1 ≤ q) (hqQ : Qof A N < q) (hqτ : (q : ℝ) ≤ τof A N)
    (hcop : IsCoprime a (q : ℤ)) (herr : |α - (a : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ∑ n ∈ Icc 1 T, phaseCap α x n ≤ 256 * N * Real.log N ^ (1-20*A) := by
  let s : ℝ := N * Real.log N ^ (-20*A)
  have hL0 : 0 < Real.log N := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hQ : 1 ≤ Qof A N := by
    unfold Qof
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hQ0 : 0 < Qof A N := by linarith
  have ht : τof A N = s := by
    dsimp [τof, Qof, s]
    rw [show -20*A = -(20*A) by ring, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hqS : (q : ℝ) ≤ s := by rwa [ht] at hqτ
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqN : (q : ℝ) ≤ N := hqτ.trans (div_le_self hN.le hQ)
  have hlogq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN
  have hlogT : Real.log T ≤ Real.log N := by
    by_cases hT : T = 0
    · simp [hT]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT) (by exact_mod_cast hTN)
  have hlog : 1 + Real.log q + Real.log T ≤ 3 * Real.log N := by linarith
  have hlog0 : 0 ≤ 1 + Real.log q + Real.log T := by positivity
  have hNq : (N : ℝ)/q ≤ s := by
    calc
      _ ≤ (N : ℝ) / Qof A N := div_le_div_of_nonneg_left hN.le hQ0 hqQ.le
      _ = s := ht
  have hxq : 2*x/q ≤ 2*s := by
    calc
      _ = 2 * (x/q) := by ring
      _ ≤ 2 * ((N : ℝ)/q) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hxN hq0.le) (by norm_num)
      _ ≤ 2*s := mul_le_mul_of_nonneg_left hNq (by norm_num)
  have hT : (T : ℝ) ≤ 4*s := by simpa only [s, mul_assoc] using hTS
  have hcoef : 2*x/q + T + q ≤ 7*s := by linarith
  have hm := phaseCap_sum_le hq hcop herr hx T
  apply hm.trans
  have hprod := mul_le_mul hcoef hlog hlog0 (by positivity : 0 ≤ 7*s)
  have hbound : 12 * (2*x/q + T + q) * (1+Real.log q+Real.log T) + T ≤
      256 * s * Real.log N := by
    nlinarith [mul_nonneg hs (show 0 ≤ Real.log N - 1 by linarith)]
  apply hbound.trans_eq
  dsimp [s]
  rw [show (1-20*A) = (-20*A) + (1:ℝ) by ring, Real.rpow_add hL0, Real.rpow_one]
  ring


/-- The scalar Cauchy estimate fits the target exponent with an absolute constant. -/
theorem rectangle_phase_of_mass (A : ℝ) (N : ℕ) (α x : ℝ) (L U K : ℕ)
    (hA : 10000 ≤ A) (hN : 0 < N) (hL : 2 ≤ Real.log N)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hT : U*K ≤ N)
    (hmass : ∑ n ∈ Icc 1 (U*K), phaseCap α x n ≤
      256*(N:ℝ)*Real.log N^(1-20*A)) :
    ∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k) ≤
      (2:ℝ)^30 * N * Real.log N^(328-4*A) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLp : 0 < Real.log N := by linarith
  have hTc : (U*K : ℕ) ≤ (N:ℝ) := by exact_mod_cast hT
  have hlog : Real.log (U*K : ℕ) ≤ Real.log N := by
    by_cases ht0 : U*K = 0
    · simp only [ht0, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht0) hTc
  have hH : Hn (U*K) ≤ 2*Real.log N := (Hn_le _).trans (by linarith)
  have hHp : Hn (U*K)^36 ≤ (2*Real.log N)^36 :=
    pow_le_pow_left₀ (Hn_nonneg _) hH 36
  have hcount : 2*x+(U*K : ℕ) ≤ 3*(N:ℝ) := by linarith
  have hmass0 : 0 ≤ ∑ n ∈ Icc 1 (U*K), phaseCap α x n :=
    sum_nonneg (fun n hn => phaseCap_nonneg α x n hx)
  have hs := rectangle_phase_sq_le L U K α x hx
  have hs' : (∑ m ∈ Ioc L U, (tau5 m : ℝ) * ∑ k ∈ Icc 1 K, phaseCap α x (m*k))^2 ≤
      (2*Real.log N)^36 * (3*(N:ℝ)*(256*(N:ℝ)*Real.log N^(1-20*A))) := by
    apply hs.trans
    apply mul_le_mul hHp _ (by positivity) (by positivity)
    exact mul_le_mul hcount hmass hmass0 (by positivity)
  have heq : (2*Real.log N)^36 * (3*(N:ℝ)*(256*(N:ℝ)*Real.log N^(1-20*A))) =
      (768*(2:ℝ)^36)*(N:ℝ)^2*Real.log N^(37-20*A) := by
    rw [show (37-20*A) = (36:ℝ)+(1-20*A) by ring, Real.rpow_add hLp,
      show Real.log N^(36:ℝ) = Real.log N^(36:ℕ) from Real.rpow_natCast _ 36]
    ring
  rw [heq] at hs'
  have hexp : Real.log N^(37-20*A) ≤ Real.log N^(656-8*A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hcoeff : 768*(2:ℝ)^36 ≤ (2:ℝ)^60 := by norm_num
  have hb : (768*(2:ℝ)^36)*(N:ℝ)^2*Real.log N^(37-20*A) ≤
      (2:ℝ)^60*(N:ℝ)^2*Real.log N^(656-8*A) := by
    gcongr
  have hsq : ((2:ℝ)^30*N*Real.log N^(328-4*A))^2 =
      (2:ℝ)^60*(N:ℝ)^2*Real.log N^(656-8*A) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Real.log N^(328-4*A)) 2,
      ← Real.rpow_mul hLp.le]
    congr 1
    · norm_num
    · congr 1; ring
  have hB : 0 ≤ (2:ℝ)^30*N*Real.log N^(328-4*A) := by positivity
  have hh := hs'.trans hb
  rw [← hsq] at hh
  nlinarith


/-- LEAF. Tolev 1999 page 86 display 65 after the progression bound.
This scalar phase average has no lambda, residue, row or upper interval endpoints.
The two spare logarithmic powers supply the Abel variant in display 66.
The plus one term is retained rather than discarded. -/
theorem phase_average :
    ∀ A : ℝ, 10 ^ 4 ≤ A →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N),
          α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M H : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → 0 < H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) *
            ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), phaseCap α x (m * k) ≤
              C * N * Real.log N ^ (328 - 4 * A) := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := eventual_minor_arc_parameters A (by linarith)
  refine ⟨(2 : ℝ)^30, N₀, by positivity, ?_⟩
  intro N hodd hNN α hα hminor x M H hxlo hxN hx hM hH hprodlo hprodhi hsize
  obtain ⟨hL, hτ⟩ := hN₀ N hNN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hQ : 0 ≤ Qof A N := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  obtain ⟨a, q, hq, hqQ, hqτ, hcop, herr, herr2⟩ :=
    minor_arc_reduced_approximation (Qof A N) (τof A N) α hQ hτ
      (by linarith) hα hminor
  have hprod := shell_product_bound A N x M H (by norm_num at hA ⊢; exact hA)
    hN1 hL (by linarith) hxN hM hH hprodhi hsize
  have hTN : ⌊2*M⌋₊ * cutoff3 (10000*A) N ≤ N := by exact_mod_cast hprod.2.1
  have hmass := phase_mass_from_approx A N (⌊2*M⌋₊ * cutoff3 (10000*A) N) q a α x
    (by linarith) hNpos hL (by linarith) hxN hTN hprod.2.2 hq hqQ hqτ hcop herr2
  have hres := rectangle_phase_of_mass A N α x ⌊M⌋₊ ⌊2*M⌋₊ (cutoff3 (10000*A) N)
    (by norm_num at hA ⊢; exact hA) (by exact_mod_cast hNpos) hL
    (by linarith) hxN hTN hmass
  norm_num only [show (10 : ℝ)^4 = 10000 by norm_num] at *
  exact hres

end LeanLab.Tolev2009.Decomp310aScalar
