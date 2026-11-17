/-
Upstream large sieve and Vaughan pieces for the page 17 maximal prime input.
Davenport, second edition, chapters 24, 27 and 28.
Source https://doi.org/10.1007/978-1-4757-5927-3_28
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.LargeSieve.Bilinear
import LeanLab.PNTPort.BV.Vaughan
import LeanLab.PNTPort.BV.Characters
import LeanLab.PNTPort.BV.Hyperbolic
import LeanLab.PNTPort.BV.TypeII
import LeanLab.PNTPort.BV.LargeConductorProof

namespace LeanLab.KumchevLiu2007.Task557a

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Davenport chapter 28 page 162 display 2, the maximal character sum.
The inserted zero handles the empty endpoint range. -/
noncomputable def primitiveMax {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧
    v = ‖LeanLab.PNTPort.BV.psiChi x χ‖})

/-- Davenport chapter 28 page 162, the character supremum has a finite
von Mangoldt majorant. Thus its real supremum has no unbounded set artifact. -/
theorem primitiveMax_bddAbove {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    BddAbove (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧
      v = ‖LeanLab.PNTPort.BV.psiChi x χ‖}) := by
  refine ⟨∑ n ∈ Finset.Icc 1 ⌊T⌋₊, ArithmeticFunction.vonMangoldt n, ?_⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  · obtain ⟨x, hx, hxT, rfl⟩ := hv
    unfold LeanLab.PNTPort.BV.psiChi
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
          (DirichletCharacter.norm_le_one _ _)
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxT))
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

#print axioms primitiveMax_bddAbove

/-- Davenport chapter 28 page 162, the maximal character norm is nonnegative. -/
theorem primitiveMax_nonneg {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    0 ≤ primitiveMax T χ :=
  le_csSup (primitiveMax_bddAbove T χ) (Set.mem_insert 0 _)

#print axioms primitiveMax_nonneg

/-- Davenport chapter 28 page 162, every endpoint norm lies below its maximum. -/
theorem primitiveMax_majorizes {q : ℕ} (T x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 ≤ x) (hxT : x ≤ T) :
    ‖LeanLab.PNTPort.BV.psiChi x χ‖ ≤ primitiveMax T χ := by
  apply le_csSup (primitiveMax_bddAbove T χ)
  exact Set.mem_insert_of_mem 0 ⟨x, hx, hxT, rfl⟩

#print axioms primitiveMax_majorizes

/-- LEAF. Davenport chapter 27 pages 151 to 160, the multiplicative large sieve
used in chapter 28 page 162 display 2. The lab supplies constant N plus 2 Q squared.
This weaker constant has the same strength needed in the chapter 28 argument. -/
theorem large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  exact LeanLab.PNTPort.LargeSieve.multiplicative_large_sieve hQ a M N

#print axioms large_sieve

/-- LEAF. Davenport chapter 24 pages 138 and 139, display 1 and its four
Dirichlet series coefficients. This is the pointwise Vaughan decomposition
used by chapter 28 page 162 after display 2. -/
theorem vaughan_identity (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0) := by
  exact LeanLab.PNTPort.BV.vaughan_identity u v hv n hn

#print axioms vaughan_identity

open Finset MeasureTheory
open LeanLab.PNTPort.LargeSieve (primIdx cs_weighted)

/-- Davenport chapter 28 page 165 display 6. The rectangular bilinear
estimate follows from the supplied large sieve and weighted Cauchy.
CONDITIONAL ON the explicit large sieve input. -/
theorem bilinear_from_large_sieve
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    {Q : ℕ} (hQ : 1 ≤ Q) (a b : ℤ → ℂ) (M₁ M₂ : ℤ) (N₁ N₂ : ℕ) :
    (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂), a m * b n * i.2 ((m * n : ℤ))‖) ^ 2 ≤
      ((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
      ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2) := by
  have hs (c : ℤ → ℂ) (M : ℤ) (N : ℕ) :
      ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ‖∑ n ∈ Ioc M (M + N), c n * i.2 n‖ ^ 2 ≤
        (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖c n‖ ^ 2 := by
    unfold primIdx
    rw [sum_sigma]
    simp_rw [← mul_sum]
    exact hLS hQ c M N
  have hfac : ∀ i : Σ k : ℕ, DirichletCharacter ℂ (k + 1),
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂), a m * b n * i.2 ((m * n : ℤ))‖ =
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), a m * i.2 m‖ * ‖∑ n ∈ Ioc M₂ (M₂ + N₂), b n * i.2 n‖ := by
    intro i
    rw [← norm_mul, sum_mul_sum]
    congr 1
    apply sum_congr rfl; intro m _
    apply sum_congr rfl; intro n _
    rw [Int.cast_mul, map_mul]
    ring
  simp_rw [hfac]
  have hw : ∀ i ∈ primIdx Q, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  refine (cs_weighted (primIdx Q) _ _ _ hw).trans ?_
  exact mul_le_mul (hs a M₁ N₁) (hs b M₂ N₂)
    (sum_nonneg (fun i hi => mul_nonneg (hw i hi) (by positivity)))
    (mul_nonneg (by positivity) (sum_nonneg (fun _ _ => by positivity)))

#print axioms bilinear_from_large_sieve

open LeanLab.PNTPort.BV (hypX hypC hypB hypB_pos kernel_integrable cutoff_point norm_exp_I_mul)

/-- Davenport chapter 28 page 165. Perron separates a single endpoint
from the two coefficient sequences. The truncation T is independent of X. -/
theorem perron_bilinear_endpoint : ∃ C : ℝ, 0 < C ∧
    ∀ (X T : ℝ), 2 ≤ X → 1 ≤ T →
    ∀ (M₁ M₂ : ℤ) (N₁ N₂ : ℕ), 0 ≤ M₁ → 0 ≤ M₂ → ∀ (a b : ℤ → ℂ)
      (i : Σ k : ℕ, DirichletCharacter ℂ (k + 1)),
    ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
      (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0)‖ ≤
    (∫ t in (-T)..T,
      ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
        (a m * Complex.exp (Complex.I * ((t * Real.log m : ℝ)))) *
        (b n * Complex.exp (Complex.I * ((t * Real.log n : ℝ)))) * i.2 ((m * n : ℤ))‖ *
        |Real.sin (LeanLab.PNTPort.BV.hypB X * t) / (Real.pi * t)|) +
      C / (T * (1 / (4 * LeanLab.PNTPort.BV.hypX X))) *
        ((∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖) * (∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖)) := by
  obtain ⟨C, hC, hP⟩ := LeanLab.PNTPort.Perron.perron_cutoff
  refine ⟨C, hC, ?_⟩
  intro X T hX hT M₁ M₂ N₁ N₂ hM₁ hM₂ a b i
  set I₁ := Ioc M₁ (M₁ + N₁) with hI₁
  set I₂ := Ioc M₂ (M₂ + N₂) with hI₂
  have hm1 : ∀ m ∈ I₁, 1 ≤ m := fun m hm => by rw [hI₁, mem_Ioc] at hm; omega
  have hn1 : ∀ n ∈ I₂, 1 ≤ n := fun n hn => by rw [hI₂, mem_Ioc] at hn; omega
  have hTT : -T ≤ T := by linarith
  set β := hypB X with hβdef
  have hβ : 0 < β := hypB_pos hX
  set c := hypC X with hcdef
  set K : ℝ → ℝ := fun t => Real.sin (β * t) / (Real.pi * t) with hK
  obtain ⟨hKc, hKa⟩ := kernel_integrable hβ T
  set E : ℝ := C / (T * (1 / (4 * hypX X))) with hE
  set A₁ := ∑ m ∈ I₁, ‖a m‖ with hA₁
  set B₁ := ∑ n ∈ I₂, ‖b n‖ with hB₁
  set e : ℝ → ℤ → ℂ := fun t m => Complex.exp (Complex.I * ((t * Real.log m : ℝ))) with he
  have hen : ∀ t m, ‖e t m‖ = 1 := fun t m => norm_exp_I_mul _
  set G : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ → ℂ := fun i t =>
    ∑ m ∈ I₁, ∑ n ∈ I₂, (a m * e t m) * (b n * e t n) * i.2 ((m * n : ℤ)) with hG
  have hGc : ∀ i, Continuous (G i) := by
    intro i; simp only [hG, he]; fun_prop

  -- the integrand identity
  have hfac : ∀ (χ : ℤ → ℂ) (m n : ℤ), 1 ≤ m → 1 ≤ n → ∀ t : ℝ,
      a m * b n * χ (m * n) * (Complex.exp (Complex.I *
        ((Real.log ((m * n : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)) =
      (a m * e t m) * (b n * e t n) * χ (m * n) *
        (Complex.exp (Complex.I * ((-c * t : ℝ))) * (K t : ℂ)) := by
    intro χ m n hm hn t
    have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hm' : (m : ℝ) ≠ 0 := by linarith
    have hn' : (n : ℝ) ≠ 0 := by linarith
    have hl : Real.log ((m * n : ℤ) : ℝ) = Real.log m + Real.log n := by
      push_cast; exact Real.log_mul hm' hn'
    have hsplit : Complex.I * (((Real.log ((m * n : ℤ) : ℝ) - c) * t : ℝ) : ℂ) =
        Complex.I * ((t * Real.log m : ℝ) : ℂ) + Complex.I * ((t * Real.log n : ℝ) : ℂ) +
          Complex.I * ((-c * t : ℝ) : ℂ) := by
      rw [hl]; push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_add]
    simp only [he]
    ring
  -- per character bound
  have hchar : ∀ i : Σ k : ℕ, DirichletCharacter ℂ (k + 1),
      ‖∑ m ∈ I₁, ∑ n ∈ I₂,
        (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0)‖ ≤
      (∫ t in (-T)..T, ‖G i t‖ * |K t|) + E * (A₁ * B₁) := by
    intro i
    set χ : ℤ → ℂ := fun x => i.2 x with hχ
    set J : ℤ → ℂ := fun k => ∫ t in (-T)..T,
      Complex.exp (Complex.I * ((Real.log (k : ℝ) - c) * t : ℝ)) * (K t : ℂ) with hJ
    have hJb : ∀ k : ℤ, 1 ≤ k →
        ‖J k - (if (k : ℝ) ≤ X then (1 : ℂ) else 0)‖ ≤ E :=
      fun k hk => cutoff_point hC hP hX hT hk
    have hsum : ∀ m n : ℤ,
        (if ((m * n : ℤ) : ℝ) ≤ X then a m * b n * i.2 ((m * n : ℤ)) else 0) =
        a m * b n * χ (m * n) * J (m * n) -
          a m * b n * χ (m * n) * (J (m * n) - (if ((m * n : ℤ) : ℝ) ≤ X then 1 else 0)) := by
      intro m n; simp only [hχ]; split_ifs <;> ring
    simp_rw [hsum, sum_sub_distrib]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · -- main part
      rw [← sum_product']
      have hint : ∀ p ∈ I₁ ×ˢ I₂, IntervalIntegrable (fun t => a p.1 * b p.2 * χ (p.1 * p.2) *
          (Complex.exp (Complex.I * ((Real.log ((p.1 * p.2 : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)))
          volume (-T) T := by
        intro p _
        exact (hKc.continuousOn_mul (by fun_prop)).const_mul _
      have : ∑ p ∈ I₁ ×ˢ I₂, a p.1 * b p.2 * χ (p.1 * p.2) * J (p.1 * p.2) =
          ∫ t in (-T)..T, ∑ p ∈ I₁ ×ˢ I₂, a p.1 * b p.2 * χ (p.1 * p.2) *
          (Complex.exp (Complex.I * ((Real.log ((p.1 * p.2 : ℤ) : ℝ) - c) * t : ℝ)) * (K t : ℂ)) := by
        rw [intervalIntegral.integral_finsetSum hint]
        apply sum_congr rfl; intro p _
        rw [hJ, intervalIntegral.integral_const_mul]
      rw [this]
      refine intervalIntegral.norm_integral_le_of_norm_le hTT
        (Filter.Eventually.of_forall fun t _ => le_of_eq ?_)
        ((hKa.continuousOn_mul ((hGc i).norm.continuousOn)))
      rw [Finset.sum_product, hG]
      simp only []
      rw [sum_congr rfl (fun m hm => sum_congr rfl (fun n hn =>
        hfac χ m n (hm1 m hm) (hn1 n hn) t))]
      simp_rw [← sum_mul]
      rw [norm_mul, norm_mul, norm_exp_I_mul, one_mul, Complex.norm_real, Real.norm_eq_abs]
    · -- error part
      refine (norm_sum_le _ _).trans ?_
      rw [hA₁, hB₁, sum_mul_sum, mul_sum]
      apply sum_le_sum; intro m hm
      refine (norm_sum_le _ _).trans ?_
      rw [mul_sum]
      apply sum_le_sum; intro n hn
      rw [norm_mul, norm_mul, norm_mul]
      have h1 : ‖χ (m * n)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have h2 := hJb (m * n) (by nlinarith [hm1 m hm, hn1 n hn])
      have : ‖a m‖ * ‖b n‖ * ‖χ (m * n)‖ ≤ ‖a m‖ * ‖b n‖ :=
        mul_le_of_le_one_right (by positivity) h1
      calc _ ≤ ‖a m‖ * ‖b n‖ * E := mul_le_mul this h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring

  exact hchar i

#print axioms perron_bilinear_endpoint

/-- Davenport chapter 28 page 165. A common positive kernel majorizes
all endpoint kernels with half width at most B. -/
theorem perron_kernel_uniform (β B t : ℝ) (hβ : 0 < β) (hβB : β ≤ B) :
    |Real.sin (β * t) / (Real.pi * t)| ≤
      2 / Real.pi * (B / (1 + B * |t|)) := by
  refine (LeanLab.PNTPort.Perron.abs_sin_div_le β t hβ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hB : 0 < B := hβ.trans_le hβB
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

#print axioms perron_kernel_uniform

/-- Davenport chapter 28 pages 165 and 166. The common kernel has
logarithmic mass. This permits endpoints that depend on the character. -/
theorem perron_uniform_mass (B T : ℝ) (hB : 0 < B) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, 2 / Real.pi * (B / (1 + B * |t|))) ≤
      2 * Real.log (1 + B * T) := by
  set g : ℝ → ℝ := fun t => 2 / Real.pi * (B / (1 + B * |t|)) with hg
  have hgc : Continuous g := by
    simp only [hg]
    apply continuous_const.mul
    apply continuous_const.div (by fun_prop)
    intro t
    have := mul_nonneg hB.le (abs_nonneg t)
    linarith
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hgc.intervalIntegrable a b
  have hsplit : ∫ t in (-T)..T, g t = 2 * (2 / Real.pi * Real.log (1 + B * T)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi (-T) 0) (hgi 0 T)]
    have hneg : ∫ t in (-T)..0, g t = ∫ t in (0 : ℝ)..T, g t := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) g
      simp only [hg, abs_neg, neg_zero] at h
      simp only [hg]
      exact h.symm
    rw [hneg, hg, LeanLab.PNTPort.Perron.integral_majorant_half B T hB hT]
    ring
  change (∫ t in (-T)..T, g t) ≤ _
  rw [hsplit]
  have hlog : 0 ≤ Real.log (1 + B * T) := Real.log_nonneg (by nlinarith)
  have hpi : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact Real.two_le_pi
  nlinarith

#print axioms perron_uniform_mass

/-- Davenport chapter 28 pages 165 and 166. The shifted log window has
half width at most the positive endpoint. -/
theorem perron_width_le (X : ℝ) (hX : 2 ≤ X) : hypB X ≤ X := by
  obtain ⟨h1, h2, h3⟩ := LeanLab.PNTPort.BV.hypX_bounds hX
  unfold hypB
  rw [LeanLab.PNTPort.BV.log_half]
  have := Real.log_le_sub_one_of_pos (show 0 < hypX X by linarith)
  have := Real.log_two_lt_d9
  linarith

#print axioms perron_width_le

/-- Davenport chapter 28 page 164 display 5, with an explicit Perron
error. Every primitive character has its own endpoint in the fixed range.
CONDITIONAL ON the supplied multiplicative large sieve. -/
theorem maximal_hyperbolic_endpoints
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ H : ℝ, 2 ≤ H → ∀ Q : ℕ, 1 ≤ Q →
      ∀ (M₁ M₂ : ℤ) (N₁ N₂ : ℕ), 0 ≤ M₁ → 0 ≤ M₂ → ∀ (a b : ℤ → ℂ)
        (X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ),
      (∀ i ∈ primIdx Q, 2 ≤ X i) → (∀ i ∈ primIdx Q, X i ≤ H) →
      (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
          (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0)‖) ≤
      C₀ * (1 + Real.log H) *
        Real.sqrt (((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
          ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2)) +
        C₀ * (Q : ℝ) ^ 2 * (∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖) *
          (∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖) / H := by
  obtain ⟨C, hC, hper⟩ := perron_bilinear_endpoint
  refine ⟨8 + 24 * C, by positivity, ?_⟩
  intro H hH Q hQ M₁ M₂ N₁ N₂ hM₁ hM₂ a b X hXlo hXhi
  have hH0 : 0 < H := by linarith
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  set I₁ := Ioc M₁ (M₁ + N₁)
  set I₂ := Ioc M₂ (M₂ + N₂)
  set T := H ^ 2 with hTdef
  have hT : 1 ≤ T := by nlinarith
  have hTT : -T ≤ T := by linarith
  set g : ℝ → ℝ := fun t => 2 / Real.pi * (H / (1 + H * |t|)) with hg
  have hg0 : ∀ t, 0 ≤ g t := fun t => by dsimp [g]; positivity
  have hgc : Continuous g := by
    dsimp [g]
    apply continuous_const.mul
    apply continuous_const.div (by fun_prop)
    intro t
    have := mul_nonneg hH0.le (abs_nonneg t)
    linarith
  have hgi : IntervalIntegrable g volume (-T) T := hgc.intervalIntegrable _ _
  set A₁ := ∑ m ∈ I₁, ‖a m‖
  set B₁ := ∑ n ∈ I₂, ‖b n‖
  set P := ((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ I₁, ‖a m‖ ^ 2) *
    ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ I₂, ‖b n‖ ^ 2) with hPdef
  set e : ℝ → ℤ → ℂ := fun t m => Complex.exp (Complex.I * ((t * Real.log m : ℝ)))
  have hen : ∀ t m, ‖e t m‖ = 1 := fun t m => norm_exp_I_mul _
  set G : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ → ℂ := fun i t =>
    ∑ m ∈ I₁, ∑ n ∈ I₂, (a m * e t m) * (b n * e t n) * i.2 ((m * n : ℤ))
  have hGc : ∀ i, Continuous (G i) := by
    intro i; dsimp [G, e]; fun_prop
  have hGg : ∀ i, IntervalIntegrable (fun t => ‖G i t‖ * g t) volume (-T) T :=
    fun i => hgi.continuousOn_mul ((hGc i).norm.continuousOn)
  have hW : ∀ i ∈ primIdx Q, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hpt : ∀ t, ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖G i t‖ ≤
      Real.sqrt P := by
    intro t
    have h := bilinear_from_large_sieve hLS hQ
      (fun m => a m * e t m) (fun n => b n * e t n) M₁ M₂ N₁ N₂
    simp only [norm_mul, hen, mul_one] at h
    exact Real.le_sqrt_of_sq_le h
  have hWs : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient ≤ 1 + 2 * (Q : ℝ) ^ 2 := by
    have h := hLS hQ (fun _ => (1 : ℂ)) 0 1
    have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
    rw [hI] at h
    unfold primIdx
    rw [sum_sigma]
    simpa [mul_comm] using h
  have hchar : ∀ i ∈ primIdx Q,
      ‖∑ m ∈ I₁, ∑ n ∈ I₂,
        (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0)‖ ≤
      (∫ t in (-T)..T, ‖G i t‖ * g t) + 8 * C / H * (A₁ * B₁) := by
    intro i hi
    have hXi := hXlo i hi
    have hβ := hypB_pos hXi
    have hbH : hypB (X i) ≤ H := (perron_width_le _ hXi).trans (hXhi i hi)
    have hk : IntervalIntegrable
        (fun t => |Real.sin (hypB (X i) * t) / (Real.pi * t)|) volume (-T) T :=
      (kernel_integrable hβ T).2
    have hkernel : ∀ t, |Real.sin (hypB (X i) * t) / (Real.pi * t)| ≤ g t :=
      fun t => perron_kernel_uniform _ _ _ hβ hbH
    have hmain : (∫ t in (-T)..T, ‖G i t‖ *
        |Real.sin (hypB (X i) * t) / (Real.pi * t)|) ≤
        ∫ t in (-T)..T, ‖G i t‖ * g t := by
      apply intervalIntegral.integral_mono_on hTT
        (hk.continuousOn_mul ((hGc i).norm.continuousOn)) (hGg i)
      intro t _
      exact mul_le_mul_of_nonneg_left (hkernel t) (norm_nonneg _)
    have hE : C / (T * (1 / (4 * hypX (X i)))) ≤ 8 * C / H := by
      obtain ⟨-, hupper, hlower⟩ := LeanLab.PNTPort.BV.hypX_bounds hXi
      have hpos : 0 < hypX (X i) := by linarith
      have heq : C / (T * (1 / (4 * hypX (X i)))) =
          4 * C * hypX (X i) / H ^ 2 := by rw [hTdef]; field_simp
      rw [heq, div_le_div_iff₀ (by positivity) hH0]
      have hb : hypX (X i) ≤ 2 * H := by linarith [hXhi i hi]
      nlinarith [mul_le_mul_of_nonneg_left hb (le_of_lt (mul_pos hC hH0))]
    exact (hper (X i) T hXi hT M₁ M₂ N₁ N₂ hM₁ hM₂ a b i).trans
      (add_le_add hmain (mul_le_mul_of_nonneg_right hE (by positivity)))
  have hmain : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      (∫ t in (-T)..T, ‖G i t‖ * g t) ≤ Real.sqrt P * (8 * Real.log H) := by
    have heq : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (∫ t in (-T)..T, ‖G i t‖ * g t) = ∫ t in (-T)..T, ∑ i ∈ primIdx Q,
          ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * g t) := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => (hGg i).const_mul _)]
      apply sum_congr rfl; intro i _
      rw [intervalIntegral.integral_const_mul]
    rw [heq]
    have hcomp : (∫ t in (-T)..T, ∑ i ∈ primIdx Q,
          ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * g t)) ≤
        ∫ t in (-T)..T, Real.sqrt P * g t := by
      apply intervalIntegral.integral_mono_on hTT
      · convert IntervalIntegrable.sum (primIdx Q)
          (fun i _ => (hGg i).const_mul (((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient)) using 1
        ext t; rw [Finset.sum_apply]
      · exact hgi.const_mul _
      · intro t _
        have heq : ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (‖G i t‖ * g t) =
            (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖G i t‖) * g t := by
          rw [sum_mul]; apply sum_congr rfl; intro i _; ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hpt t) (hg0 t)
    have hlog : Real.log (1 + H * T) ≤ 4 * Real.log H := by
      have heq : Real.log (H ^ 4) = 4 * Real.log H := by rw [Real.log_pow]; norm_num
      rw [← heq]
      apply Real.log_le_log (by positivity)
      rw [hTdef]
      have h3 : (2 : ℝ) ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ (by norm_num) hH 3
      nlinarith
    refine hcomp.trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      ((perron_uniform_mass H T hH0 (by linarith)).trans (by linarith)) (Real.sqrt_nonneg _)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hAB : 0 ≤ A₁ * B₁ := by positivity
  calc
    _ ≤ ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ((∫ t in (-T)..T, ‖G i t‖ * g t) + 8 * C / H * (A₁ * B₁)) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hchar i hi) (hW i hi)
    _ = (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (∫ t in (-T)..T, ‖G i t‖ * g t)) +
        (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) *
          (8 * C / H * (A₁ * B₁)) := by
      rw [Finset.sum_mul (s := primIdx Q), ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    _ ≤ Real.sqrt P * (8 * Real.log H) +
        (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / H * (A₁ * B₁)) :=
      add_le_add hmain (mul_le_mul_of_nonneg_right hWs (by positivity))
    _ ≤ _ := by
      have h1 : Real.sqrt P * (8 * Real.log H) ≤
          (8 + 24 * C) * (1 + Real.log H) * Real.sqrt P := by
        have hc : 8 * Real.log H ≤ (8 + 24 * C) * (1 + Real.log H) := by
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg P)]
      have h2 : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / H * (A₁ * B₁)) ≤
          (8 + 24 * C) * (Q : ℝ) ^ 2 * A₁ * B₁ / H := by
        have hq : 1 + 2 * (Q : ℝ) ^ 2 ≤ 3 * (Q : ℝ) ^ 2 := by nlinarith
        have heq : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C / H * (A₁ * B₁)) =
            ((1 + 2 * (Q : ℝ) ^ 2) * (8 * C) * (A₁ * B₁)) / H := by ring
        rw [heq]
        apply div_le_div_of_nonneg_right _ hH0.le
        have hc : (1 + 2 * (Q : ℝ) ^ 2) * (8 * C) ≤ (8 + 24 * C) * (Q : ℝ) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ 8 * C)]
        convert mul_le_mul_of_nonneg_right hc hAB using 1; ring
      exact add_le_add h1 h2

#print axioms maximal_hyperbolic_endpoints

/-- Davenport chapter 28 page 164 display 5. The endpoint may be chosen
separately for every primitive character. The lower endpoint two suffices
for Vaughan sums whose coefficients vanish at one.
CONDITIONAL ON the supplied multiplicative large sieve. -/
theorem maximal_bilinear_large_sieve
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    : ∃ K : ℝ, 0 < K ∧ ∀ Q : ℕ, 1 ≤ Q →
      ∀ (M₁ M₂ : ℤ) (N₁ N₂ : ℕ), 0 ≤ M₁ → 0 ≤ M₂ → 2 ≤ (N₁ : ℝ) * N₂ →
      ∀ (a b : ℤ → ℂ) (X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ),
      (∀ i ∈ primIdx Q, 2 ≤ X i) → (∀ i ∈ primIdx Q, X i ≤ (N₁ : ℝ) * N₂) →
      (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ‖∑ m ∈ Ioc M₁ (M₁ + N₁), ∑ n ∈ Ioc M₂ (M₂ + N₂),
          (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0)‖) ≤
      K * Real.log (2 * (N₁ : ℝ) * N₂) *
        Real.sqrt (((N₁ + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc M₁ (M₁ + N₁), ‖a m‖ ^ 2) *
          ((N₂ + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M₂ (M₂ + N₂), ‖b n‖ ^ 2)) := by
  obtain ⟨C, hC, hmax⟩ := maximal_hyperbolic_endpoints hLS
  refine ⟨4 * C, by positivity, ?_⟩
  intro Q hQ M₁ M₂ N₁ N₂ hM₁ hM₂ hN a b X hXlo hXhi
  set H : ℝ := (N₁ : ℝ) * N₂ with hH
  have hH0 : 0 < H := by linarith
  set I₁ := Ioc M₁ (M₁ + N₁)
  set I₂ := Ioc M₂ (M₂ + N₂)
  set A := ∑ m ∈ I₁, ‖a m‖
  set B := ∑ n ∈ I₂, ‖b n‖
  set Sa := ∑ m ∈ I₁, ‖a m‖ ^ 2
  set Sb := ∑ n ∈ I₂, ‖b n‖ ^ 2
  set P := ((N₁ + 2 * (Q : ℝ) ^ 2) * Sa) * ((N₂ + 2 * (Q : ℝ) ^ 2) * Sb)
  have hSa : 0 ≤ Sa := by positivity
  have hSb : 0 ≤ Sb := by positivity
  have hcard₁ : I₁.card = N₁ := by dsimp [I₁]; simp [Int.card_Ioc]
  have hcard₂ : I₂.card = N₂ := by dsimp [I₂]; simp [Int.card_Ioc]
  have hA : A ^ 2 ≤ (N₁ : ℝ) * Sa := by
    have h := sq_sum_le_card_mul_sum_sq (s := I₁) (f := fun m => ‖a m‖)
    simpa only [hcard₁] using h
  have hB : B ^ 2 ≤ (N₂ : ℝ) * Sb := by
    have h := sq_sum_le_card_mul_sum_sq (s := I₂) (f := fun n => ‖b n‖)
    simpa only [hcard₂] using h
  have hAB : (A * B) ^ 2 ≤ H * (Sa * Sb) := by
    have h := mul_le_mul hA hB (sq_nonneg B) (by positivity : 0 ≤ (N₁ : ℝ) * Sa)
    dsimp [H]
    nlinarith
  have hABroot : A * B ≤ H * Real.sqrt (Sa * Sb) := by
    have hHsq : H ≤ H ^ 2 := by nlinarith
    have h := hAB.trans (mul_le_mul_of_nonneg_right hHsq (mul_nonneg hSa hSb))
    have heq : (H * Real.sqrt (Sa * Sb)) ^ 2 = H ^ 2 * (Sa * Sb) := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hSa hSb)]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rwa [heq]
  have hroot : (Q : ℝ) ^ 2 * Real.sqrt (Sa * Sb) ≤ Real.sqrt P := by
    have h₁ : (Q : ℝ) ^ 2 * Sa ≤ (N₁ + 2 * (Q : ℝ) ^ 2) * Sa :=
      mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (Q : ℝ), (Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)]) hSa
    have h₂ : (Q : ℝ) ^ 2 * Sb ≤ (N₂ + 2 * (Q : ℝ) ^ 2) * Sb :=
      mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (Q : ℝ), (Nat.cast_nonneg N₂ : (0 : ℝ) ≤ N₂)]) hSb
    have h := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hSa hSb)]
    dsimp [P]
    nlinarith
  have herr : (Q : ℝ) ^ 2 * A * B / H ≤ Real.sqrt P := by
    calc
      _ = (Q : ℝ) ^ 2 * (A * B) / H := by ring
      _ ≤ (Q : ℝ) ^ 2 * (H * Real.sqrt (Sa * Sb)) / H :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hABroot (by positivity)) hH0.le
      _ = (Q : ℝ) ^ 2 * Real.sqrt (Sa * Sb) := by field_simp
      _ ≤ _ := hroot
  have herrC : C * (Q : ℝ) ^ 2 * A * B / H ≤ C * Real.sqrt P := by
    calc
      _ = C * ((Q : ℝ) ^ 2 * A * B / H) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left herr hC.le
  have hlog : 2 + Real.log H ≤ 4 * Real.log (2 * (N₁ : ℝ) * N₂) := by
    have harg : 2 * (N₁ : ℝ) * N₂ = 2 * H := by dsimp [H]; ring
    rw [harg, Real.log_mul (by norm_num) hH0.ne']
    have := Real.log_two_gt_d9
    have : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    linarith
  calc
    _ ≤ C * (1 + Real.log H) * Real.sqrt P + C * (Q : ℝ) ^ 2 * A * B / H :=
      hmax H hN Q hQ M₁ M₂ N₁ N₂ hM₁ hM₂ a b X hXlo hXhi
    _ ≤ C * (1 + Real.log H) * Real.sqrt P + C * Real.sqrt P := add_le_add le_rfl herrC
    _ = C * (2 + Real.log H) * Real.sqrt P := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC.le)
        (Real.sqrt_nonneg P)
      convert h using 1; ring

#print axioms maximal_bilinear_large_sieve

/-- Davenport chapter 28 page 162. The character maximum is attained
at an integer endpoint between two and the integer part of x. -/
theorem primitiveMax_attained {q : ℕ} (x : ℝ) (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ q) :
    ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) ≤ x ∧
      primitiveMax x χ = ‖LeanLab.PNTPort.BV.psiChi (n : ℝ) χ‖ := by
  have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  obtain ⟨n, hn, hmax⟩ := (Icc 2 ⌊x⌋₊).exists_max_image
    (fun n : ℕ => ‖LeanLab.PNTPort.BV.psiChi (n : ℝ) χ‖)
    ⟨2, by simp [hfloor]⟩
  have hn' := mem_Icc.mp hn
  have hnx : (n : ℝ) ≤ x := (by exact_mod_cast hn'.2 : (n : ℝ) ≤ ⌊x⌋₊).trans
    (Nat.floor_le (by linarith))
  refine ⟨n, hn'.1, hnx, le_antisymm ?_
    (primitiveMax_majorizes x n χ (by positivity) hnx)⟩
  apply csSup_le (Set.insert_nonempty _ _)
  rintro v (rfl | ⟨y, hy, hyx, rfl⟩)
  · positivity
  · by_cases hfy : 2 ≤ ⌊y⌋₊
    · have heq : LeanLab.PNTPort.BV.psiChi y χ =
          LeanLab.PNTPort.BV.psiChi (⌊y⌋₊ : ℝ) χ := by
        unfold LeanLab.PNTPort.BV.psiChi
        rw [Nat.floor_natCast]
      rw [heq]
      exact hmax _ (mem_Icc.mpr ⟨hfy, Nat.floor_le_floor hyx⟩)
    · have hz : LeanLab.PNTPort.BV.psiChi y χ = 0 := by
        unfold LeanLab.PNTPort.BV.psiChi
        apply sum_eq_zero
        intro m hm
        have hm' := mem_Icc.mp hm
        have hm1 : m = 1 := by omega
        subst m
        simp
      rw [hz, norm_zero]
      positivity

#print axioms primitiveMax_attained

/-- Davenport chapter 28 page 166, the one row bilinear representation
used when Q squared exceeds x. -/
theorem psiChi_one_row {q : ℕ} (N : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hN : ⌊y⌋₊ ≤ N) (χ : DirichletCharacter ℂ q) :
    LeanLab.PNTPort.BV.psiChi y χ =
      ∑ m ∈ Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)),
        ∑ n ∈ Ioc (0 : ℤ) (0 + (N : ℤ)),
          (if ((m * n : ℤ) : ℝ) ≤ y then
            (1 : ℂ) * (ArithmeticFunction.vonMangoldt n.toNat : ℂ) * χ ((m * n : ℤ)) else 0) := by
  have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
  rw [hI, sum_singleton]
  simp only [one_mul, zero_add]
  have hconv := LeanLab.PNTPort.BV.sum_Ioc_int
    (fun n : ℤ => if (n : ℝ) ≤ y then
      (ArithmeticFunction.vonMangoldt n.toNat : ℂ) * χ n else 0) 0 N
  simp only [Nat.cast_zero, zero_add] at hconv
  rw [hconv]
  simp only [Nat.cast_zero, zero_add, Int.toNat_natCast, Int.cast_natCast]
  have hset : (Ioc 0 N).filter (fun n : ℕ => (n : ℝ) ≤ y) = Icc 1 ⌊y⌋₊ := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_Icc, ← Nat.le_floor_iff hy]
    omega
  rw [← sum_filter, hset]
  rfl

#print axioms psiChi_one_row

/-- Davenport chapter 28 page 166. The one row specialization of the
maximal bilinear inequality bounds the full character maximum by its
von Mangoldt coefficient energy. CONDITIONAL ON the supplied large sieve. -/
theorem maximal_character_mean_energy
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * Real.log (2 * (⌊x⌋₊ : ℝ)) *
        Real.sqrt ((1 + 2 * (Q : ℝ) ^ 2) *
          ((⌊x⌋₊ + 2 * (Q : ℝ) ^ 2) *
            ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n ^ 2)) := by
  classical
  obtain ⟨K, hK, hbil⟩ := maximal_bilinear_large_sieve hLS
  refine ⟨K, hK, ?_⟩
  intro x hx Q hQ
  set N := ⌊x⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor hx
  let endpoint : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℕ :=
    fun i => Classical.choose (primitiveMax_attained x hx i.2)
  have hatt : ∀ i, 2 ≤ endpoint i ∧ (endpoint i : ℝ) ≤ x ∧
      primitiveMax x i.2 = ‖LeanLab.PNTPort.BV.psiChi (endpoint i : ℝ) i.2‖ :=
    fun i => Classical.choose_spec (primitiveMax_attained x hx i.2)
  have heN : ∀ i, endpoint i ≤ N := fun i => Nat.le_floor (hatt i).2.1
  have hpsi : ∀ i, primitiveMax x i.2 =
      ‖∑ m ∈ Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)), ∑ n ∈ Ioc (0 : ℤ) (0 + (N : ℤ)),
        (if ((m * n : ℤ) : ℝ) ≤ (endpoint i : ℝ) then
          (1 : ℂ) * (ArithmeticFunction.vonMangoldt n.toNat : ℂ) * i.2 ((m * n : ℤ)) else 0)‖ := by
    intro i
    rw [(hatt i).2.2, psiChi_one_row N (endpoint i) (by positivity)
      (by simpa using heN i) i.2]
  have hA : (∑ m ∈ Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)), ‖(1 : ℂ)‖ ^ 2) = 1 := by
    have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
    simp [hI]
  have hB : (∑ n ∈ Ioc (0 : ℤ) (0 + (N : ℤ)),
      ‖(ArithmeticFunction.vonMangoldt n.toNat : ℂ)‖ ^ 2) =
      ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2 := by
    have hconv := LeanLab.PNTPort.BV.sum_Ioc_int
      (fun n : ℤ => ‖(ArithmeticFunction.vonMangoldt n.toNat : ℂ)‖ ^ 2) 0 N
    simp only [Nat.cast_zero, zero_add] at hconv
    simp only [zero_add]
    rw [hconv]
    simp only [Nat.cast_zero, zero_add, Int.toNat_natCast,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    congr 1
  have h := hbil Q hQ 0 0 1 N (by norm_num) (by norm_num)
    (by simpa using (show (2 : ℝ) ≤ N by exact_mod_cast hN2)) (fun _ => (1 : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n.toNat : ℂ))
    (fun i => (endpoint i : ℝ))
    (fun i _ => by exact_mod_cast (hatt i).1)
    (fun i _ => by simpa using (show (endpoint i : ℝ) ≤ N by exact_mod_cast heN i))
  rw [hA, hB] at h
  simp only [Nat.cast_one, one_mul, mul_one] at h
  have hsum : (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      primitiveMax x i.2) =
      ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ := by
    unfold primIdx
    rw [sum_sigma]
    simp_rw [mul_sum]
  rw [← hsum]
  simp_rw [hpsi]
  simpa only [Nat.cast_one, one_mul] using h

#print axioms maximal_character_mean_energy

/-- Davenport chapter 28 page 166, the Q squared at least x case of
page 162 display 2. The supplied large sieve is the proved lab theorem. -/
theorem maximal_character_mean_high_conductors :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q → x ≤ (Q : ℝ) ^ 2 →
      (∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4 := by
  obtain ⟨K, hK, henergy⟩ := maximal_character_mean_energy large_sieve
  refine ⟨3 * K, by positivity, ?_⟩
  intro x hx Q hQ hxQ
  have hx0 : 0 < x := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set N := ⌊x⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor hx
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hE : (∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) ≤ x * Real.log x ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ Icc 1 N, Real.log x ^ 2 := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_Icc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hnx : (n : ℝ) ≤ x := (by exact_mod_cast hn'.2 : (n : ℝ) ≤ N).trans hNx
        have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log x :=
          ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnx)
        exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg hΛ 2
      _ = (N : ℝ) * Real.log x ^ 2 := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hNx (sq_nonneg _)
  have hA : 1 + 2 * (Q : ℝ) ^ 2 ≤ 3 * (Q : ℝ) ^ 2 := by nlinarith
  have hB : (N : ℝ) + 2 * (Q : ℝ) ^ 2 ≤ 3 * (Q : ℝ) ^ 2 := by linarith
  have hP : (1 + 2 * (Q : ℝ) ^ 2) *
      (((N : ℝ) + 2 * (Q : ℝ) ^ 2) *
        ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2) ≤
      (3 * (Q : ℝ) ^ 2) * (3 * (Q : ℝ) ^ 2 * (x * Real.log x ^ 2)) :=
    mul_le_mul hA (mul_le_mul hB hE (by positivity) (by positivity))
      (by positivity) (by positivity)
  have hsqrt : Real.sqrt ((1 + 2 * (Q : ℝ) ^ 2) *
      (((N : ℝ) + 2 * (Q : ℝ) ^ 2) *
        ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)) ≤
      3 * (Q : ℝ) ^ 2 * Real.sqrt x * Real.log x := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have heq : (3 * (Q : ℝ) ^ 2 * Real.sqrt x * Real.log x) ^ 2 =
        (3 * (Q : ℝ) ^ 2) * (3 * (Q : ℝ) ^ 2 * (x * Real.log x ^ 2)) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx0.le]
      ring
    rw [heq]
    exact hP
  have hlogN : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith)
  have hlogNle : Real.log (2 * (N : ℝ)) ≤ Real.log (2 * x * Q) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlogxle : Real.log x ≤ Real.log (2 * x * Q) :=
    Real.log_le_log hx0 (by nlinarith)
  have hlog1 : 1 ≤ Real.log (2 * x * Q) := by
    have h4 : (4 : ℝ) ≤ 2 * x * Q := by nlinarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq] at h
    linarith [Real.log_two_gt_d9]
  have hlogs : Real.log (2 * (N : ℝ)) * Real.log x ≤ Real.log (2 * x * Q) ^ 4 := by
    have h₂ : Real.log (2 * (N : ℝ)) * Real.log x ≤ Real.log (2 * x * Q) ^ 2 := by
      simpa [sq] using mul_le_mul hlogNle hlogxle hL (by linarith : 0 ≤ Real.log (2 * x * Q))
    have hsq : 1 ≤ Real.log (2 * x * Q) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (Real.log (2 * x * Q) ^ 2 - 1)]
  have hpoly : Real.sqrt x * (Q : ℝ) ^ 2 ≤
      x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2 := by
    have : 0 ≤ x ^ (5 / 6 : ℝ) * Q := by positivity
    linarith
  calc
    _ ≤ K * Real.log (2 * (N : ℝ)) * Real.sqrt ((1 + 2 * (Q : ℝ) ^ 2) *
        (((N : ℝ) + 2 * (Q : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)) := henergy x hx Q hQ
    _ ≤ K * Real.log (2 * (N : ℝ)) *
        (3 * (Q : ℝ) ^ 2 * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hK.le hlogN)
    _ = (3 * K) * (Real.sqrt x * (Q : ℝ) ^ 2) *
        (Real.log (2 * (N : ℝ)) * Real.log x) := by ring
    _ ≤ (3 * K) * (Real.sqrt x * (Q : ℝ) ^ 2) * Real.log (2 * x * Q) ^ 4 :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)

#print axioms maximal_character_mean_high_conductors

open LeanLab.PNTPort.BV

/-- Davenport chapter 28 page 166 display 11. One Vaughan Type II block
has a uniform mean bound when each character chooses its own endpoint. -/
theorem maximal_vaughan_block : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
    ∀ M : ℕ, w ≤ M →
    ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
      (∀ i ∈ primIdx R, 2 ≤ X i) → (∀ i ∈ primIdx R, X i ≤ x) →
    ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖blk (X i) w M (⌊x⌋₊ / M) i.2‖ ≤
      K * (2 + Real.log x) ^ 3 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  obtain ⟨C₀, hC₀, hyp⟩ := maximal_hyperbolic_endpoints large_sieve
  set c := Real.log 4 + 4 with hc
  have hc0 : 0 ≤ c := by rw [hc]; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine ⟨24 * C₀ * Real.sqrt c + 4 * C₀ * c, by positivity, ?_⟩
  intro x hx w hw R hR M hwM X hXlo hXhi
  set N := ⌊x⌋₊ with hNdef
  set N₂ := N / M with hN₂
  set L := Real.log x with hL
  set ℓ := 2 + L with hℓ
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hM1 : 1 ≤ M := le_trans hw hwM
  have hRHS : 0 ≤ (24 * C₀ * Real.sqrt c + 4 * C₀ * c) * ℓ ^ 3 *
      (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by positivity
  by_cases hMw : N ≤ M * w
  · have hz : ∀ i ∈ primIdx R, blk (X i) w M N₂ i.2 = 0 := by
      intro i hi
      unfold blk
      apply sum_eq_zero; intro t ht; apply sum_eq_zero; intro r hr
      simp only [mem_Ioc] at ht hr
      apply gS4_eq_zero (by linarith [hXlo i hi])
      have hfloor : ⌊X i⌋₊ ≤ N := Nat.floor_le_floor (hXhi i hi)
      nlinarith
    rw [sum_eq_zero (fun i hi => by rw [hz i hi, norm_zero, mul_zero])]
    exact hRHS
  push Not at hMw
  set a : ℤ → ℂ := fun m => (vonMangoldt m.toNat : ℂ) with ha
  set b : ℤ → ℂ := fun n => (gV w n.toNat : ℂ) with hb
  have key : ∀ i : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)), blk (X i) w M N₂ i.2 =
      ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)),
        (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0) := by
    intro i
    rw [sum_Ioc_int]
    unfold blk
    refine sum_congr rfl fun t _ => ?_
    rw [sum_Ioc_int]
    refine sum_congr rfl fun r _ => ?_
    unfold gS4
    simp only [ha, hb, Int.toNat_natCast]
    push_cast
    rfl
  have h := hyp x hx R hR M w M N₂ (by positivity) (by positivity) a b X hXlo hXhi
  have hlogsize : 0 ≤ Real.log
      (1 + (M : ℝ) + (N₂ : ℝ) + ((M : ℤ) : ℝ) + ((w : ℤ) : ℝ)) := by
    apply Real.log_nonneg
    push_cast
    have hnonneg : (0 : ℝ) ≤ (M : ℝ) + N₂ + M + w := by positivity
    linarith
  have h := h.trans (add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlogsize) hC₀.le)
      (Real.sqrt_nonneg _)) le_rfl)
  rw [sum_congr rfl (fun i _ => by rw [key i])]
  refine h.trans ?_
  -- the numerical facts
  have hwN : w ≤ N₂ := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
  have hMN : ((M : ℕ) : ℝ) * (N₂ : ℝ) ≤ x := by
    have : M * N₂ ≤ N := Nat.mul_div_le N M
    exact le_trans (by exact_mod_cast this) hNx
  have hMwx : ((M : ℕ) : ℝ) * (w : ℝ) ≤ x := le_trans (by exact_mod_cast hMw.le) hNx
  have hNw : (N₂ : ℝ) * (w : ℝ) ≤ x := by
    refine le_trans ?_ hMN
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hwM) (by positivity)
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hw1r : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hMx : (M : ℝ) ≤ x := by nlinarith
  have hN₂x : (N₂ : ℝ) ≤ x := by nlinarith
  have hwN₂ : (w : ℝ) ≤ N₂ := by exact_mod_cast hwN
  -- the sums
  have hSa : ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ‖a m‖ ^ 2 =
      ∑ t ∈ Ioc M (M + M), vonMangoldt t ^ 2 := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [ha, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hA : ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + ((M : ℕ) : ℤ)), ‖a m‖ =
      ∑ t ∈ Ioc M (M + M), vonMangoldt t := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [ha, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
  have hSb : ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)), ‖b n‖ ^ 2 =
      ∑ r ∈ Ioc w (w + N₂), gV w r ^ 2 := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [hb, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB : ∑ n ∈ Ioc (w : ℤ) ((w : ℤ) + ((N₂ : ℕ) : ℤ)), ‖b n‖ =
      ∑ r ∈ Ioc w (w + N₂), |gV w r| := by
    rw [sum_Ioc_int]; refine sum_congr rfl fun t _ => ?_
    simp only [hb, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hSa, hA, hSb, hB]
  have hlog2M : Real.log (2 * M) ≤ ℓ := by
    have := log_two_mul_le (by linarith : (1 : ℝ) ≤ x) (by linarith : (1 : ℝ) ≤ 2 * M)
      (by linarith); rw [hℓ]; linarith
  have hlogwN : 1 + Real.log ((w + N₂ : ℕ) : ℝ) ≤ ℓ := by
    have := log_two_mul_le (by linarith : (1 : ℝ) ≤ x) (y := ((w + N₂ : ℕ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    rw [hℓ]; linarith
  have hlogwN0 : 0 ≤ 1 + Real.log ((w + N₂ : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg (w + N₂); linarith
  have hwN2 : ((w + N₂ : ℕ) : ℝ) ≤ 2 * N₂ := by push_cast; linarith
  have hgsq : ((w + N₂ : ℕ) : ℝ) * (1 + Real.log ((w + N₂ : ℕ) : ℝ)) ^ 3 ≤ 2 * N₂ * ℓ ^ 3 :=
    mul_le_mul hwN2 (pow_le_pow_left₀ hlogwN0 hlogwN 3) (by positivity) (by positivity)
  have hlg : 1 + Real.log x + Real.log (1 + (M : ℝ) + (N₂ : ℝ) + ((M : ℤ) : ℝ) + ((w : ℤ) : ℝ))
      ≤ 3 * ℓ := by
    push_cast
    have h5 : Real.log (1 + (M : ℝ) + N₂ + M + w) ≤ Real.log (5 * x) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h5
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    rw [hℓ, hL]; linarith
  have hlogM0 : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ c * (2 * M) := by positivity
  apply blk_arith hC₀ hc0 (by linarith) (by rw [hℓ]; linarith) (by positivity) (by positivity)
    (by positivity) (by positivity) (sum_nonneg fun _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => vonMangoldt_nonneg)
    (sum_nonneg fun _ _ => by positivity)
  · refine (sum_vonMangoldt_sq_block M).trans ?_
    calc Real.log (2 * M) * (c * (2 * M)) ≤ ℓ * (c * (2 * M)) :=
          mul_le_mul_of_nonneg_right hlog2M hc4
      _ = _ := by ring
  · exact (sum_gV_sq_le w N₂).trans hgsq
  · refine (sum_vonMangoldt_block M).trans (le_of_eq ?_); ring
  · exact (sum_abs_gV_le w N₂).trans hgsq
  · exact hMN
  · exact hMwx
  · exact hNw
  · exact hlg


#print axioms maximal_vaughan_block

/-- Davenport chapter 28 page 166 display 10. A fixed outer rectangle
represents S4 at every smaller nonnegative endpoint. -/
theorem S4_fixed_rectangle {q : ℕ} (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x)
    (u v : ℕ) (χ : DirichletCharacter ℂ q) :
    S4 y u v χ = ∑ t ∈ Ioc u ⌊x⌋₊, ∑ r ∈ Ioc v (v + ⌊x⌋₊), gS4 y v χ t r := by
  have hf : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  calc
    _ = ∑ t ∈ Ioc u ⌊y⌋₊, ∑ r ∈ Ioc v (v + ⌊x⌋₊), gS4 y v χ t r := by
      rw [S4_eq_Ioc y hy u v χ]
      apply sum_congr rfl
      intro t ht
      have ht1 : 1 ≤ t := by have := (mem_Ioc.mp ht).1; omega
      apply sum_subset (Ioc_subset_Ioc le_rfl (by omega))
      intro r hr hnot
      have hr' := mem_Ioc.mp hr
      have hlarge : ⌊y⌋₊ < r := by
        have : ¬ r ≤ v + ⌊y⌋₊ := fun h => hnot (mem_Ioc.mpr ⟨hr'.1, h⟩)
        omega
      apply gS4_eq_zero hy
      have hrprod : r ≤ t * r := by nlinarith
      omega
    _ = _ := by
      apply sum_subset (Ioc_subset_Ioc le_rfl hf)
      intro t ht hnot
      have ht' := mem_Ioc.mp ht
      have hlarge : ⌊y⌋₊ < t := by
        have : ¬ t ≤ ⌊y⌋₊ := fun h => hnot (mem_Ioc.mpr ⟨ht'.1, h⟩)
        omega
      apply sum_eq_zero
      intro r hr
      have hr1 : 1 ≤ r := by have := (mem_Ioc.mp hr).1; omega
      apply gS4_eq_zero hy
      have htprod : t ≤ t * r := Nat.le_mul_of_pos_right t hr1
      omega

#print axioms S4_fixed_rectangle

/-- Davenport chapter 28 page 166 display 10 and page 167 display 12.
The dyadic block lengths depend only on x, not on the chosen endpoint y. -/
theorem S4_fixed_blocks {q : ℕ} (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) {u : ℕ} (hu : 1 ≤ u) (v : ℕ) {J : ℕ}
    (hJ : ⌊x⌋₊ ≤ u * 2 ^ J) (χ : DirichletCharacter ℂ q) :
    S4 y u v χ = ∑ j ∈ range J, blk y v (u * 2 ^ j) (⌊x⌋₊ / (u * 2 ^ j)) χ := by
  set N := ⌊x⌋₊
  have hfloor : ⌊y⌋₊ ≤ N := Nat.floor_le_floor hyx
  rw [S4_fixed_rectangle x y hy hyx u v χ]
  have hsub : Ioc u N ⊆ Ioc u (u * 2 ^ J) := Ioc_subset_Ioc le_rfl hJ
  rw [sum_subset hsub]
  swap
  · intro t ht hn
    simp only [mem_Ioc, not_and, not_le] at ht hn
    apply sum_eq_zero
    intro r hr
    have hr1 : 1 ≤ r := by simp only [mem_Ioc] at hr; omega
    apply gS4_eq_zero hy
    apply lt_of_le_of_lt hfloor
    have : t ≤ t * r := Nat.le_mul_of_pos_right t hr1
    have := hn ht.1
    omega
  rw [sum_Ioc_dyadic]
  refine sum_congr rfl fun j _ => ?_
  unfold blk
  refine sum_congr rfl fun t ht => ?_
  set M := u * 2 ^ j
  have hM : M < t := (mem_Ioc.1 ht).1
  have hdiv : N / M ≤ N := Nat.div_le_self _ _
  symm
  apply sum_subset (Ioc_subset_Ioc le_rfl (by omega))
  intro r hr hn
  simp only [mem_Ioc, not_and, not_le] at hr hn
  apply gS4_eq_zero hy
  apply lt_of_le_of_lt hfloor
  show N < t * r
  by_contra hc
  push Not at hc
  have h1 : r ≤ N / t := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hc)
  have h2 : N / t ≤ N / M := Nat.div_le_div_left hM.le (Nat.mul_pos hu (by positivity))
  have := hn hr.1
  omega

#print axioms S4_fixed_blocks

/-- Davenport chapter 28 page 167 display 12. The Vaughan Type II mean
bound holds with a separate endpoint for each primitive character. -/
theorem maximal_vaughan_typeII : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → ∀ R : ℕ, 1 ≤ R →
    ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
      (∀ i ∈ primIdx R, 2 ≤ X i) → (∀ i ∈ primIdx R, X i ≤ x) →
    ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 (X i) w w i.2‖ ≤
      K * (2 + Real.log x) ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  obtain ⟨K₁, hK₁, hblk⟩ := maximal_vaughan_block
  refine ⟨2 * K₁, by positivity, ?_⟩
  intro x hx w hw R hR X hXlo hXhi
  set N := ⌊x⌋₊ with hNdef
  set J := Nat.log 2 N + 1 with hJ
  set G := x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x with hG
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNJ : N ≤ w * 2 ^ J := by
    have : N < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
    have : 2 ^ J ≤ w * 2 ^ J := Nat.le_mul_of_pos_left _ hw
    omega
  have hW : ∀ i ∈ primIdx R, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  have hJr : (J : ℝ) ≤ 2 * (2 + Real.log x) := by
    have := natLog_two_le hN1 (Nat.floor_le hx0)
    rw [hJ]; push_cast; linarith
  calc ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 (X i) w w i.2‖
      ≤ ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ∑ j ∈ range J, ‖blk (X i) w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        apply sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (hW i hi)
        rw [S4_fixed_blocks x (X i) (by linarith [hXlo i hi]) (hXhi i hi) hw w hNJ]
        exact norm_sum_le _ _
    _ = ∑ j ∈ range J, ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ‖blk (X i) w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        simp_rw [mul_sum]; exact sum_comm
    _ ≤ ∑ _j ∈ range J, K₁ * (2 + Real.log x) ^ 3 * G := by
        apply sum_le_sum; intro j _
        exact hblk x hx w hw R hR (w * 2 ^ j) (Nat.le_mul_of_pos_right w (by positivity)) X hXlo hXhi
    _ = J * (K₁ * (2 + Real.log x) ^ 3 * G) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (2 * (2 + Real.log x)) * (K₁ * (2 + Real.log x) ^ 3 * G) :=
        mul_le_mul_of_nonneg_right hJr (by rw [hG]; positivity)
    _ = _ := by ring

#print axioms maximal_vaughan_typeII

/-- Davenport chapter 28 page 166 displays 7 to 10. Sum the exact
supplied Vaughan identity with the character coefficients.
CONDITIONAL ON the explicit pointwise Vaughan identity. -/
theorem psiChi_decomp_from_vaughan
    (hVaughan : ∀ (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0))
    {q : ℕ} (y : ℝ) (u v : ℕ) (χ : DirichletCharacter ℂ q) (hv : 1 ≤ v) :
    psiChi y χ = S1 y u χ - S2 y u v χ + S3 y v χ - S4 y u v χ := by
  unfold psiChi S1 S2 S3 S4
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
  have h := hVaughan u v hv n hn1
  rw [← sub_mul, ← add_mul, ← sub_mul]
  congr 1
  unfold gV
  exact_mod_cast h

#print axioms psiChi_decomp_from_vaughan

/-- Davenport chapter 28 page 166 displays 7 to 10. The four Vaughan
norms control the mean at independently selected character endpoints.
CONDITIONAL ON the explicit pointwise Vaughan identity. -/
theorem vaughan_character_mean_split
    (hVaughan : ∀ (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0))
    (Q u v : ℕ) (hv : 1 ≤ v)
    (Y : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ) :
    (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (Y i) i.2‖) ≤
      ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (‖S1 (Y i) u i.2‖ + ‖S2 (Y i) u v i.2‖ +
          ‖S3 (Y i) v i.2‖ + ‖S4 (Y i) u v i.2‖) := by
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [psiChi_decomp_from_vaughan hVaughan (Y i) u v i.2 hv]
  have h₁ := norm_sub_le (S1 (Y i) u i.2 - S2 (Y i) u v i.2 + S3 (Y i) v i.2)
    (S4 (Y i) u v i.2)
  have h₂ := norm_add_le (S1 (Y i) u i.2 - S2 (Y i) u v i.2) (S3 (Y i) v i.2)
  have h₃ := norm_sub_le (S1 (Y i) u i.2) (S2 (Y i) u v i.2)
  linarith

#print axioms vaughan_character_mean_split

/-- Davenport chapter 28 page 165. A product cutoff below two retains
at most the term with both integer indices equal to one. -/
theorem bilinear_small_cutoff {q : ℕ} (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (a b : ℤ → ℂ) (χ : DirichletCharacter ℂ q) (y : ℝ) (hy : y < 2) :
    ‖∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ∑ n ∈ Ioc (0 : ℤ) (N : ℤ),
      (if ((m * n : ℤ) : ℝ) ≤ y then a m * b n * χ ((m * n : ℤ)) else 0)‖ ≤
      ‖a 1‖ * ‖b 1‖ := by
  have hm1 : (1 : ℤ) ∈ Ioc (0 : ℤ) (M : ℤ) := by
    simp only [mem_Ioc]
    exact ⟨by norm_num, by exact_mod_cast hM⟩
  have hn1 : (1 : ℤ) ∈ Ioc (0 : ℤ) (N : ℤ) := by
    simp only [mem_Ioc]
    exact ⟨by norm_num, by exact_mod_cast hN⟩
  have heq : (∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ∑ n ∈ Ioc (0 : ℤ) (N : ℤ),
      (if ((m * n : ℤ) : ℝ) ≤ y then a m * b n * χ ((m * n : ℤ)) else 0)) =
        if (1 : ℝ) ≤ y then a 1 * b 1 else 0 := by
    rw [sum_eq_single 1]
    · rw [sum_eq_single 1]
      · simp
      · intro n hn hne
        have hn2 : (2 : ℤ) ≤ n := by have := (mem_Ioc.mp hn).1; omega
        have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hnot : ¬ (((1 : ℤ) * n : ℤ) : ℝ) ≤ y := by simpa using (by linarith : ¬ (n : ℝ) ≤ y)
        simp only [ite_eq_right hnot]
      · exact fun h => (h hn1).elim
    · intro m hm hne
      apply sum_eq_zero
      intro n hn
      have hm2 : (2 : ℤ) ≤ m := by have := (mem_Ioc.mp hm).1; omega
      have hnpos : (1 : ℤ) ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hprod : (2 : ℤ) ≤ m * n := by nlinarith
      have hprodR : (2 : ℝ) ≤ ((m * n : ℤ) : ℝ) := by exact_mod_cast hprod
      have hnot : ¬ ((m * n : ℤ) : ℝ) ≤ y := by linarith
      simp only [ite_eq_right hnot]
    · exact fun h => (h hm1).elim
  rw [heq]
  split_ifs
  · rw [norm_mul]
  · simp only [norm_zero]
    positivity

#print axioms bilinear_small_cutoff

/-- Davenport chapter 28 page 164 display 5. The logarithmic bilinear
bound includes every lower endpoint and every positive rectangle size.
CONDITIONAL ON the supplied multiplicative large sieve. -/
theorem maximal_bilinear_bounded_endpoints
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    : ∃ K : ℝ, 0 < K ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ M N : ℕ, 1 ≤ M → 1 ≤ N →
      ∀ (a b : ℤ → ℂ) (X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ),
      (∀ i ∈ primIdx Q, X i ≤ (M : ℝ) * N) →
      (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ‖∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ∑ n ∈ Ioc (0 : ℤ) (N : ℤ),
          (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0)‖) ≤
      K * Real.log (2 * (M : ℝ) * N) *
        Real.sqrt (((M + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ‖a m‖ ^ 2) *
          ((N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc (0 : ℤ) (N : ℤ), ‖b n‖ ^ 2)) := by
  obtain ⟨K, hK, hmax⟩ := maximal_bilinear_large_sieve hLS
  refine ⟨K + 2, by positivity, ?_⟩
  intro Q hQ M N hM hN a b X hXhi
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set H : ℝ := (M : ℝ) * N
  have hH : 1 ≤ H := by dsimp [H]; nlinarith
  let w : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ :=
    fun i => ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient
  let F : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ → ℝ := fun i y =>
    ‖∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ∑ n ∈ Ioc (0 : ℤ) (N : ℤ),
      (if ((m * n : ℤ) : ℝ) ≤ y then a m * b n * i.2 ((m * n : ℤ)) else 0)‖
  set A := ‖a 1‖ * ‖b 1‖
  set P := ((M + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ‖a m‖ ^ 2) *
    ((N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc (0 : ℤ) (N : ℤ), ‖b n‖ ^ 2)
  have hw : ∀ i, 0 ≤ w i := fun i => by dsimp [w]; positivity
  have hm1 : (1 : ℤ) ∈ Ioc (0 : ℤ) (M : ℤ) := by
    simp only [mem_Ioc]; exact ⟨by norm_num, by exact_mod_cast hM⟩
  have hn1 : (1 : ℤ) ∈ Ioc (0 : ℤ) (N : ℤ) := by
    simp only [mem_Ioc]; exact ⟨by norm_num, by exact_mod_cast hN⟩
  have ha : ‖a 1‖ ^ 2 ≤ ∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ‖a m‖ ^ 2 :=
    single_le_sum (f := fun m : ℤ => ‖a m‖ ^ 2) (fun _ _ => by positivity) hm1
  have hb : ‖b 1‖ ^ 2 ≤ ∑ n ∈ Ioc (0 : ℤ) (N : ℤ), ‖b n‖ ^ 2 :=
    single_le_sum (f := fun n : ℤ => ‖b n‖ ^ 2) (fun _ _ => by positivity) hn1
  have hcoef : (1 + 2 * (Q : ℝ) ^ 2) * A ≤ Real.sqrt P := by
    have h₁ := mul_le_mul (show 1 + 2 * (Q : ℝ) ^ 2 ≤ (M : ℝ) + 2 * (Q : ℝ) ^ 2 by linarith)
      ha (by positivity) (by positivity : 0 ≤ (M : ℝ) + 2 * (Q : ℝ) ^ 2)
    have h₂ := mul_le_mul (show 1 + 2 * (Q : ℝ) ^ 2 ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 by linarith)
      hb (by positivity) (by positivity : 0 ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2)
    have hprod := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    apply Real.le_sqrt_of_sq_le
    dsimp [A, P]
    nlinarith only [hprod]
  have hweights : ∑ i ∈ primIdx Q, w i ≤ 1 + 2 * (Q : ℝ) ^ 2 := by
    have h := hLS hQ (fun _ => (1 : ℂ)) 0 1
    have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
    rw [hI] at h
    dsimp [w]
    unfold primIdx
    rw [sum_sigma]
    simpa [mul_comm] using h
  have hweightA : (∑ i ∈ primIdx Q, w i) * A ≤ Real.sqrt P :=
    (mul_le_mul_of_nonneg_right hweights (by positivity)).trans hcoef
  have hsmall (Z : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ)
      (hZ : ∀ i ∈ primIdx Q, Z i < 2) : ∑ i ∈ primIdx Q, w i * F i (Z i) ≤ Real.sqrt P := by
    calc
      _ ≤ (∑ i ∈ primIdx Q, w i) * A := by
        rw [sum_mul]
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (bilinear_small_cutoff M N hM hN a b i.2 (Z i) (hZ i hi)) (hw i)
      _ ≤ _ := hweightA
  have hlog : 1 ≤ 2 * Real.log (2 * H) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ 2 * H by linarith)
    linarith [Real.log_two_gt_d9]
  have hlog0 : 0 ≤ Real.log (2 * H) := by linarith
  have harg : 2 * (M : ℝ) * N = 2 * H := by dsimp [H]; ring
  change (∑ i ∈ primIdx Q, w i * F i (X i)) ≤ _
  rw [harg]
  by_cases hH2 : 2 ≤ H
  · let Y : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ := fun i => max 2 (X i)
    have hYlo : ∀ i ∈ primIdx Q, 2 ≤ Y i := fun i _ => le_max_left _ _
    have hYhi : ∀ i ∈ primIdx Q, Y i ≤ H := fun i hi => max_le hH2 (hXhi i hi)
    have hmaxY : ∑ i ∈ primIdx Q, w i * F i (Y i) ≤ K * Real.log (2 * H) * Real.sqrt P := by
      have h := hmax Q hQ 0 0 M N (by norm_num) (by norm_num) hH2 a b Y hYlo hYhi
      simpa only [w, F, P, H, zero_add, mul_assoc] using h
    have hpoint : ∀ i, F i (X i) ≤ F i (Y i) + A := by
      intro i
      by_cases hXi : 2 ≤ X i
      · simp only [Y, max_eq_right hXi]
        have : 0 ≤ A := by positivity
        linarith
      · have h := bilinear_small_cutoff M N hM hN a b i.2 (X i) (lt_of_not_ge hXi)
        change F i (X i) ≤ A at h
        have : 0 ≤ F i (Y i) := norm_nonneg _
        linarith
    calc
      _ ≤ ∑ i ∈ primIdx Q, w i * (F i (Y i) + A) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw i)
      _ = (∑ i ∈ primIdx Q, w i * F i (Y i)) + (∑ i ∈ primIdx Q, w i) * A := by
        simp only [mul_add, sum_add_distrib, sum_mul]
      _ ≤ K * Real.log (2 * H) * Real.sqrt P + Real.sqrt P := add_le_add hmaxY hweightA
      _ = (K * Real.log (2 * H) + 1) * Real.sqrt P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hlog]) (Real.sqrt_nonneg _)
  · have hsmallX : ∑ i ∈ primIdx Q, w i * F i (X i) ≤ Real.sqrt P :=
      hsmall X (fun i hi => lt_of_le_of_lt (hXhi i hi) (lt_of_not_ge hH2))
    refine hsmallX.trans ?_
    have hnum : 1 ≤ (K + 2) * Real.log (2 * H) := by
      nlinarith only [hlog, mul_nonneg hK.le hlog0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hnum (Real.sqrt_nonneg P)

#print axioms maximal_bilinear_bounded_endpoints

/-- Davenport chapter 28 page 164 display 5. Each primitive character
chooses an arbitrary real endpoint. Endpoints outside the rectangle
support are clipped without changing any term.
CONDITIONAL ON the supplied multiplicative large sieve. -/
theorem maximal_bilinear_full
    (hLS : ∀ {Q : ℕ} (_hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    : ∃ K : ℝ, 0 < K ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ M N : ℕ, 1 ≤ M → 1 ≤ N →
      ∀ (a b : ℤ → ℂ) (X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ),
      (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ‖∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ∑ n ∈ Ioc (0 : ℤ) (N : ℤ),
          (if ((m * n : ℤ) : ℝ) ≤ X i then a m * b n * i.2 ((m * n : ℤ)) else 0)‖) ≤
      K * Real.log (2 * (M : ℝ) * N) *
        Real.sqrt (((M + 2 * (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (M : ℤ), ‖a m‖ ^ 2) *
          ((N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Ioc (0 : ℤ) (N : ℤ), ‖b n‖ ^ 2)) := by
  obtain ⟨K, hK, hbound⟩ := maximal_bilinear_bounded_endpoints hLS
  refine ⟨K, hK, ?_⟩
  intro Q hQ M N hM hN a b X
  have h := hbound Q hQ M N hM hN a b (fun i => min ((M : ℝ) * N) (X i))
    (fun i _ => min_le_left _ _)
  convert h using 1
  apply sum_congr rfl
  intro i hi
  apply congrArg (fun z : ℝ => ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * z)
  apply congrArg (fun z : ℂ => ‖z‖)
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  have hm' := mem_Ioc.mp hm
  have hn' := mem_Ioc.mp hn
  have hprodInt : m * n ≤ (M : ℤ) * N :=
    mul_le_mul hm'.2 hn'.2 (by omega) (by positivity)
  have hprod : ((m * n : ℤ) : ℝ) ≤ (M : ℝ) * N := by exact_mod_cast hprodInt
  simp only [le_min_iff, hprod, true_and]

#print axioms maximal_bilinear_full

/-- Davenport chapter 28 page 167 before display 13. Split S2 at the
outer coefficient cutoff u. The support restriction t at most u v
is still carried by its explicit coefficient. -/
theorem S2_split_at_cutoff {q : ℕ} (y : ℝ) (u v : ℕ)
    (χ : DirichletCharacter ℂ q) :
    let c : ℕ → ℝ := fun t => ∑ z ∈ t.divisorsAntidiagonal,
      (if z.1 ≤ u ∧ z.2 ≤ v then ArithmeticFunction.vonMangoldt z.1 * (μ z.2 : ℝ) else 0)
    S2 y u v χ =
      (∑ t ∈ Icc 1 ⌊y⌋₊, if t ≤ u then
        ∑ r ∈ Icc 1 (⌊y⌋₊ / t), (c t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0) +
      (∑ t ∈ Icc 1 ⌊y⌋₊, if u < t then
        ∑ r ∈ Icc 1 (⌊y⌋₊ / t), (c t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0) := by
  dsimp only
  unfold S2
  rw [sum_conv_eq χ
    (fun p => ∑ z ∈ p.1.divisorsAntidiagonal,
      (if z.1 ≤ u ∧ z.2 ≤ v then ArithmeticFunction.vonMangoldt z.1 * (μ z.2 : ℝ) else 0))]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases h : t ≤ u
  · simp only [h, not_lt.mpr h, ite_true, ite_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_false, ite_true, zero_add]

#print axioms S2_split_at_cutoff

/-- Davenport chapter 28 page 167 displays 13 and 14. A negative route
certificate: the unsplit Type I polynomial cost cannot be absorbed by
an absolute constant times the target polynomial on this scaling. -/
theorem unsplit_typeI_cost_unbounded (K : ℝ) :
    ∃ t : ℝ, 2 ≤ t ∧ K * (t ^ 26 + 2 * t ^ 24) < t ^ 31 := by
  set t := 2 * |K| + 2 with htdef
  have ht : 2 ≤ t := by dsimp [t]; linarith [abs_nonneg K]
  have ht0 : 0 < t := by linarith
  have ht2 : 2 ≤ t ^ 2 := by nlinarith only [ht, sq_nonneg (t - 2)]
  have h4 : 1 ≤ t ^ 4 := one_le_pow₀ (by linarith)
  have h5 : t ≤ t ^ 5 := by
    have h := mul_le_mul_of_nonneg_right h4 ht0.le
    nlinarith only [h]
  have hden : t ^ 26 + 2 * t ^ 24 ≤ 2 * t ^ 26 := by
    have h := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ t ^ 24 by positivity)
    nlinarith only [h]
  refine ⟨t, ht, ?_⟩
  calc
    _ ≤ |K| * (t ^ 26 + 2 * t ^ 24) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (2 * t ^ 26) := mul_le_mul_of_nonneg_left hden (abs_nonneg K)
    _ = (2 * |K|) * t ^ 26 := by ring
    _ < t ^ 5 * t ^ 26 := mul_lt_mul_of_pos_right
      (by have hk : 2 * |K| < t := by rw [htdef]; linarith
          exact hk.trans_le h5) (by positivity)
    _ = _ := by ring

#print axioms unsplit_typeI_cost_unbounded

-- Concrete parameter instances for every task596 statement.
#check bilinear_from_large_sieve large_sieve (by norm_num : 1 ≤ (1 : ℕ)) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) 0 0 1 1
#check (Classical.choose_spec perron_bilinear_endpoint).2 2 1 (by norm_num) (by norm_num) 0 0 1 1 (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) ⟨0, 1⟩
#check perron_kernel_uniform 1 1 0 (by norm_num) (by norm_num)
#check perron_uniform_mass 1 1 (by norm_num) (by norm_num)
#check perron_width_le 2 (by norm_num)
#check (Classical.choose_spec (maximal_hyperbolic_endpoints large_sieve)).2 4 (by norm_num) 3 (by norm_num) 0 0 2 2 (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (fun _ => 3) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check (Classical.choose_spec (maximal_bilinear_large_sieve large_sieve)).2 3 (by norm_num) 0 0 2 2 (by norm_num) (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (fun _ => 3) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check primitiveMax_attained 2 (by norm_num) (1 : DirichletCharacter ℂ 1)
#check psiChi_one_row 2 2 (by norm_num) (by norm_num) (1 : DirichletCharacter ℂ 1)
#check (Classical.choose_spec (maximal_character_mean_energy large_sieve)).2 2 (by norm_num) 1 (by norm_num)
#check (Classical.choose_spec maximal_character_mean_high_conductors).2 2 (by norm_num) 2 (by norm_num) (by norm_num)
#check (Classical.choose_spec maximal_vaughan_block).2 16 (by norm_num) 1 (by norm_num) 3 (by norm_num) 1 (by norm_num) (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check S4_fixed_rectangle 16 8 (by norm_num) (by norm_num) 1 1 (1 : DirichletCharacter ℂ 1)
#check S4_fixed_blocks (q := 1) 16 8 (by norm_num) (by norm_num) (u := 1) (by norm_num) 1 (J := 4) (by norm_num) 1
#check (Classical.choose_spec maximal_vaughan_typeII).2 16 (by norm_num) 1 (by norm_num) 3 (by norm_num) (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check psiChi_decomp_from_vaughan vaughan_identity 8 1 1 (1 : DirichletCharacter ℂ 1) (by norm_num)
#check vaughan_character_mean_split vaughan_identity 1 1 1 (by norm_num) (fun _ => 8)
#check bilinear_small_cutoff 1 1 (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (1 : DirichletCharacter ℂ 1) 1 (by norm_num)
#check (Classical.choose_spec (maximal_bilinear_bounded_endpoints large_sieve)).2 1 (by norm_num) 1 1 (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (fun _ => 1) (by intro i hi; norm_num)
#check (Classical.choose_spec (maximal_bilinear_full large_sieve)).2 1 (by norm_num) 1 1 (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (fun _ => 10)
#check S2_split_at_cutoff 8 2 2 (1 : DirichletCharacter ℂ 1)
#check unsplit_typeI_cost_unbounded 1

/-- Davenport chapter 28 page 166 display 8. The truncated coefficient
of the Type I convolution. -/
noncomputable def S2coeff (u v t : ℕ) : ℝ :=
  ∑ z ∈ t.divisorsAntidiagonal,
    (if z.1 ≤ u ∧ z.2 ≤ v then ArithmeticFunction.vonMangoldt z.1 * (μ z.2 : ℝ) else 0)

#print axioms S2coeff

/-- Davenport chapter 28 page 167 before display 13. The truncated
coefficient has the elementary logarithmic majorant. -/
theorem abs_S2coeff_le (u v t : ℕ) : |S2coeff u v t| ≤ Real.log t := by
  unfold S2coeff
  calc
    _ ≤ ∑ z ∈ t.divisorsAntidiagonal,
        |(if z.1 ≤ u ∧ z.2 ≤ v then ArithmeticFunction.vonMangoldt z.1 * (μ z.2 : ℝ) else 0)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ t.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt z.1 := by
      apply sum_le_sum
      intro z hz
      split_ifs
      · rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        apply mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := z.2)
      · simp only [abs_zero]
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log t := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => ArithmeticFunction.vonMangoldt a),
        ArithmeticFunction.vonMangoldt_sum]

#print axioms abs_S2coeff_le

/-- Davenport chapter 28 page 167 before display 13. The coefficient
vanishes outside the product of its two cutoffs. -/
theorem S2coeff_eq_zero (u v t : ℕ) (ht : u * v < t) : S2coeff u v t = 0 := by
  unfold S2coeff
  apply sum_eq_zero
  intro z hz
  have hzprod := (Nat.mem_divisorsAntidiagonal.mp hz).1
  split_ifs with h
  · exfalso
    have hle := Nat.mul_le_mul h.1 h.2
    omega
  · rfl

#print axioms S2coeff_eq_zero

/-- Davenport chapter 28 page 167 display 13. One dyadic block of the
long part of S2, with its product cutoff kept explicit. -/
noncomputable def S2block {q : ℕ} (y : ℝ) (w M N₂ : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ Ioc M (M + M), ∑ r ∈ Ioc 0 N₂,
    (if ((t * r : ℕ) : ℝ) ≤ y then
      (S2coeff w w t : ℂ) * χ ((t * r : ℕ) : ZMod q) else 0)

#print axioms S2block

/-- Davenport chapter 28 page 167 display 13, a block consequence with
three logarithms. The equal cutoff satisfies w cubed at most x. -/
theorem maximal_S2_block : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
    ∀ w : ℕ, 1 ≤ w → (w : ℝ) ^ 3 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
    ∀ M : ℕ, w ≤ M → ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
      (∀ i ∈ primIdx Q, 2 ≤ X i) → (∀ i ∈ primIdx Q, X i ≤ x) →
    (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      ‖S2block (X i) w M (⌊x⌋₊ / M) i.2‖) ≤
      K * (2 + Real.log x) ^ 3 *
        (x + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x) := by
  obtain ⟨C₀, hC₀, hmax⟩ := maximal_hyperbolic_endpoints large_sieve
  refine ⟨28 * C₀, by positivity, ?_⟩
  intro x hx w hw hwx Q hQ M hwM X hXlo hXhi
  have hx0 : 0 < x := by linarith
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hM1 : 1 ≤ M := hw.trans hwM
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set L := 2 + Real.log x with hL
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  set c := L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set N₂ := ⌊x⌋₊ / M
  have hRHS : 0 ≤ 28 * C₀ * L ^ 3 *
      (x + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x) := by positivity
  by_cases hMw : w * w ≤ M
  · have hz : ∀ i, S2block (X i) w M N₂ i.2 = 0 := by
      intro i
      unfold S2block
      apply sum_eq_zero
      intro t ht
      apply sum_eq_zero
      intro r hr
      have hct : S2coeff w w t = 0 := S2coeff_eq_zero w w t (by
        have := (mem_Ioc.mp ht).1; omega)
      simp only [hct, Complex.ofReal_zero, zero_mul, ite_self]
    rw [sum_eq_zero (fun i hi => by rw [hz i, norm_zero, mul_zero])]
    exact hRHS
  have hMW : (M : ℝ) * w ≤ x := by
    have hnat : M * w ≤ w ^ 3 := by nlinarith
    have hreal : (M : ℝ) * w ≤ (w : ℝ) ^ 3 := by exact_mod_cast hnat
    exact hreal.trans hwx
  have hMN : (M : ℝ) * N₂ ≤ x :=
    (by exact_mod_cast Nat.mul_div_le ⌊x⌋₊ M : (M : ℝ) * N₂ ≤ ⌊x⌋₊).trans (Nat.floor_le hx0.le)
  have hNW : (N₂ : ℝ) * w ≤ x := by
    have hwm : (w : ℝ) ≤ M := by exact_mod_cast hwM
    have h := mul_le_mul_of_nonneg_right hwm (show 0 ≤ (N₂ : ℝ) by positivity)
    nlinarith only [h, hMN]
  have hMx : (M : ℝ) ≤ x := by nlinarith only [hMW, hw1, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  let a : ℤ → ℂ := fun m => (S2coeff w w m.toNat : ℂ)
  have hkey : ∀ i, S2block (X i) w M N₂ i.2 =
      ∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + (M : ℤ)), ∑ n ∈ Ioc (0 : ℤ) (N₂ : ℤ),
        (if ((m * n : ℤ) : ℝ) ≤ X i then a m * (1 : ℂ) * i.2 ((m * n : ℤ)) else 0) := by
    intro i
    rw [sum_Ioc_int]
    unfold S2block
    apply sum_congr rfl
    intro t ht
    have hconv := sum_Ioc_int
      (fun n : ℤ => if (((t : ℤ) * n : ℤ) : ℝ) ≤ X i then
        a t * (1 : ℂ) * i.2 (((t : ℤ) * n : ℤ)) else 0) 0 N₂
    simp only [Nat.cast_zero, zero_add] at hconv
    rw [hconv]
    apply sum_congr rfl
    intro r hr
    dsimp [a]
    push_cast
    simp only [mul_one]
  have h := hmax x hx Q hQ M 0 M N₂ (by positivity) (by norm_num)
    a (fun _ => (1 : ℂ)) X hXlo hXhi
  simp only [zero_add] at h
  rw [sum_congr rfl (fun i hi => by rw [hkey i])]
  refine h.trans ?_
  have hSa : (∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + (M : ℤ)), ‖a m‖ ^ 2) =
      ∑ t ∈ Ioc M (M + M), S2coeff w w t ^ 2 := by
    rw [sum_Ioc_int]
    apply sum_congr rfl
    intro t ht
    simp only [a, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hA : (∑ m ∈ Ioc (M : ℤ) ((M : ℤ) + (M : ℤ)), ‖a m‖) =
      ∑ t ∈ Ioc M (M + M), |S2coeff w w t| := by
    rw [sum_Ioc_int]
    apply sum_congr rfl
    intro t ht
    simp only [a, Int.toNat_natCast, Complex.norm_real, Real.norm_eq_abs]
  have hB : (∑ n ∈ Ioc (0 : ℤ) (N₂ : ℤ), ‖(1 : ℂ)‖) = N₂ := by simp [Int.card_Ioc]
  have hSb : (∑ n ∈ Ioc (0 : ℤ) (N₂ : ℤ), ‖(1 : ℂ)‖ ^ 2) = N₂ := by simp [Int.card_Ioc]
  rw [hSa, hA, hB, hSb]
  set Sa := ∑ t ∈ Ioc M (M + M), S2coeff w w t ^ 2
  set A := ∑ t ∈ Ioc M (M + M), |S2coeff w w t|
  set P := (((M : ℝ) + 2 * (Q : ℝ) ^ 2) * Sa) *
    (((N₂ : ℝ) + 2 * (Q : ℝ) ^ 2) * N₂)
  set E := C₀ * (Q : ℝ) ^ 2 * A * N₂ / x
  set G := x + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x
  have hcoef : ∀ t ∈ Ioc M (M + M), |S2coeff w w t| ≤ L := by
    intro t ht
    have ht' := mem_Ioc.mp ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have htx : (t : ℝ) ≤ 2 * x := by
      have htM : (t : ℝ) ≤ (M : ℝ) + M := by exact_mod_cast ht'.2
      linarith
    have hlog := log_two_mul_le (by linarith : (1 : ℝ) ≤ x) ht1 htx
    exact (abs_S2coeff_le w w t).trans (by dsimp [L]; linarith)
  have hSaBd : Sa ≤ (M : ℝ) * c := by
    calc
      _ ≤ ∑ _t ∈ Ioc M (M + M), c := by
        apply sum_le_sum
        intro t ht
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoef t ht) 2
      _ = _ := by simp [Nat.card_Ioc]
  have hABd : A ≤ (M : ℝ) * L := by
    calc
      _ ≤ ∑ _t ∈ Ioc M (M + M), L := sum_le_sum hcoef
      _ = _ := by simp [Nat.card_Ioc]
  have hSa2 : Sa ≤ 2 * c * M := by nlinarith only [hSaBd, mul_nonneg hc0 (Nat.cast_nonneg M)]
  have hA2 : A ≤ 2 * c * M := by
    have hLc : L ≤ 2 * c := by dsimp [c]; nlinarith only [hL1, sq_nonneg (L - 1)]
    have h := mul_le_mul_of_nonneg_left hLc (show 0 ≤ (M : ℝ) by positivity)
    nlinarith only [hABd, h]
  have hbase := blk_arith (C₀ := C₀) (c := c) (x := x) (ℓ := 1) (L := 0) (lg := 0)
    (M := (M : ℝ)) (N₂ := (N₂ : ℝ)) (R := (Q : ℝ)) (w := (w : ℝ))
    (Sa := Sa) (Sb := (N₂ : ℝ)) (A1 := A) (B1 := (N₂ : ℝ))
    hC₀ hc0 (by linarith) (by norm_num) (by positivity) (by positivity)
    (by positivity) hw0 (by dsimp [Sa]; positivity) (by positivity)
    (by dsimp [A]; positivity) (by positivity)
    (by simpa using hSa2) (by nlinarith only [show (0 : ℝ) ≤ N₂ by positivity]) (by exact hA2)
    (by nlinarith only [show (0 : ℝ) ≤ N₂ by positivity]) hMN hMW hNW (by norm_num)
  have hrootc : Real.sqrt c = L := by
    dsimp [c]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  simp only [zero_add, add_zero, one_pow, mul_one, hrootc] at hbase
  have hbase' : C₀ * Real.sqrt P + E ≤ (24 * C₀ * L + 4 * C₀ * c) * G := hbase
  have hE0 : 0 ≤ E := by dsimp [E, A]; positivity
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hLpow : L ^ 2 ≤ L ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hL1 (sq_nonneg L)
    nlinarith only [h]
  have hnum : L * (24 * C₀ * L + 4 * C₀ * c) ≤ 28 * C₀ * L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hLpow (show 0 ≤ 24 * C₀ by positivity)
    dsimp [c]
    nlinarith only [h]
  have hfactor : C₀ * (1 + Real.log x) * Real.sqrt P + E ≤ L * (C₀ * Real.sqrt P + E) := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show 1 + Real.log x ≤ L by dsimp [L]; linarith) hC₀.le)
      (Real.sqrt_nonneg P)
    have h₂ := mul_le_mul_of_nonneg_right hL1 hE0
    nlinarith only [h₁, h₂]
  exact hfactor.trans ((mul_le_mul_of_nonneg_left hbase' (by linarith)).trans
    (by simpa [mul_assoc] using mul_le_mul_of_nonneg_right hnum hG0))

#print axioms maximal_S2_block

/-- Davenport chapter 28 page 167 before display 13. The summand of
the long Type I block, with the product cutoff explicit. -/
noncomputable def S2summand {q : ℕ} (y : ℝ) (w : ℕ)
    (χ : DirichletCharacter ℂ q) (t r : ℕ) : ℂ :=
  if ((t * r : ℕ) : ℝ) ≤ y then
    (S2coeff w w t : ℂ) * χ ((t * r : ℕ) : ZMod q) else 0

/-- Davenport chapter 28 page 167 before display 13. The part of S2
whose outer index is above the cutoff w. -/
noncomputable def S2long {q : ℕ} (y : ℝ) (w : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ Ioc w ⌊y⌋₊, ∑ r ∈ Icc 1 (⌊y⌋₊ / t),
    (S2coeff w w t : ℂ) * χ ((t * r : ℕ) : ZMod q)

/-- Davenport chapter 28 page 167 display 13. The product cutoff
kills every term beyond the endpoint. -/
theorem S2summand_eq_zero {q : ℕ} {y : ℝ} (_hy : 0 ≤ y) {w : ℕ}
    (χ : DirichletCharacter ℂ q) {t r : ℕ} (h : ⌊y⌋₊ < t * r) :
    S2summand y w χ t r = 0 := by
  unfold S2summand
  rw [ite_eq_right_iff]
  intro hle
  have := Nat.le_floor hle
  omega

#print axioms S2summand_eq_zero

/-- Davenport chapter 28 page 167 display 13. The long S2 sum at y
can be represented in a rectangle whose size depends only on x. -/
theorem S2long_fixed_rectangle {q : ℕ} (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x)
    (w : ℕ) (χ : DirichletCharacter ℂ q) :
    S2long y w χ = ∑ t ∈ Ioc w ⌊x⌋₊, ∑ r ∈ Ioc 0 ⌊x⌋₊, S2summand y w χ t r := by
  have hf : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hyx
  unfold S2long
  calc
    _ = ∑ t ∈ Ioc w ⌊y⌋₊, ∑ r ∈ Ioc 0 ⌊x⌋₊, S2summand y w χ t r := by
      apply sum_congr rfl
      intro t ht
      have ht1 : 1 ≤ t := by have := (mem_Ioc.mp ht).1; omega
      have hs : Icc 1 (⌊y⌋₊ / t) = (Ioc 0 ⌊x⌋₊).filter (fun r => t * r ≤ ⌊y⌋₊) := by
        ext r
        simp only [mem_Icc, mem_filter, mem_Ioc, Nat.le_div_iff_mul_le ht1]
        constructor
        · rintro ⟨hr1, hrprod⟩
          have hrself : r ≤ r * t := Nat.le_mul_of_pos_right r ht1
          exact ⟨⟨by omega, by omega⟩, by nlinarith only [hrprod]⟩
        · rintro ⟨⟨hr0, hrx⟩, hrprod⟩
          exact ⟨by omega, by nlinarith only [hrprod]⟩
      rw [hs, sum_filter]
      apply sum_congr rfl
      intro r hr
      unfold S2summand
      have hiff : ((t * r : ℕ) : ℝ) ≤ y ↔ t * r ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).symm
      simp only [hiff]
    _ = _ := by
      apply sum_subset (Ioc_subset_Ioc le_rfl hf)
      intro t ht hnot
      have ht' := mem_Ioc.mp ht
      have hlarge : ⌊y⌋₊ < t := by
        have : ¬ t ≤ ⌊y⌋₊ := fun h => hnot (mem_Ioc.mpr ⟨ht'.1, h⟩)
        omega
      apply sum_eq_zero
      intro r hr
      have hr1 : 1 ≤ r := by have := (mem_Ioc.mp hr).1; omega
      apply S2summand_eq_zero hy
      have htprod : t ≤ t * r := Nat.le_mul_of_pos_right t hr1
      omega

#print axioms S2long_fixed_rectangle

/-- Davenport chapter 28 page 167 display 13. The long S2 sum has
fixed dyadic block lengths for every endpoint at most x. -/
theorem S2long_fixed_blocks {q : ℕ} (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x)
    {w : ℕ} (hw : 1 ≤ w) {J : ℕ} (hJ : ⌊x⌋₊ ≤ w * 2 ^ J)
    (χ : DirichletCharacter ℂ q) :
    S2long y w χ = ∑ j ∈ range J, S2block y w (w * 2 ^ j) (⌊x⌋₊ / (w * 2 ^ j)) χ := by
  set N := ⌊x⌋₊
  have hfloor : ⌊y⌋₊ ≤ N := Nat.floor_le_floor hyx
  rw [S2long_fixed_rectangle x y hy hyx w χ]
  have hsub : Ioc w N ⊆ Ioc w (w * 2 ^ J) := Ioc_subset_Ioc le_rfl hJ
  rw [sum_subset hsub]
  swap
  · intro t ht hn
    simp only [mem_Ioc, not_and, not_le] at ht hn
    apply sum_eq_zero
    intro r hr
    have hr1 : 1 ≤ r := by have := (mem_Ioc.mp hr).1; omega
    apply S2summand_eq_zero hy
    have hlarge := hn ht.1
    have htprod : t ≤ t * r := Nat.le_mul_of_pos_right t hr1
    omega
  rw [sum_Ioc_dyadic]
  apply sum_congr rfl
  intro j hj
  unfold S2block
  apply sum_congr rfl
  intro t ht
  set M := w * 2 ^ j
  have hM : M < t := (mem_Ioc.mp ht).1
  have hdiv : N / M ≤ N := Nat.div_le_self _ _
  symm
  apply sum_subset (Ioc_subset_Ioc le_rfl hdiv)
  intro r hr hn
  simp only [mem_Ioc, not_and, not_le] at hr hn
  apply S2summand_eq_zero hy
  apply lt_of_le_of_lt hfloor
  show N < t * r
  by_contra hc
  push Not at hc
  have h1 : r ≤ N / t := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith only [hc])
  have h2 : N / t ≤ N / M := Nat.div_le_div_left hM.le (Nat.mul_pos hw (by positivity))
  have := hn hr.1
  omega

#print axioms S2long_fixed_blocks

/-- Davenport chapter 28 page 167 display 13. A four logarithm consequence
for the long S2 mean in the equal cutoff range used on page 168. -/
theorem maximal_S2_long : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ w : ℕ, 1 ≤ w → (w : ℝ) ^ 3 ≤ x → ∀ R : ℕ, 1 ≤ R →
    ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
      (∀ i ∈ primIdx R, 2 ≤ X i) → (∀ i ∈ primIdx R, X i ≤ x) →
    ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S2long (X i) w i.2‖ ≤
      K * (2 + Real.log x) ^ 4 * (x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x) := by
  obtain ⟨K₁, hK₁, hblk⟩ := maximal_S2_block
  refine ⟨2 * K₁, by positivity, ?_⟩
  intro x hx w hw hwx R hR X hXlo hXhi
  set N := ⌊x⌋₊ with hNdef
  set J := Nat.log 2 N + 1 with hJ
  set G := x + R * x / Real.sqrt w + R ^ 2 * Real.sqrt x with hG
  have hx0 : 0 ≤ x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNJ : N ≤ w * 2 ^ J := by
    have : N < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) N
    have : 2 ^ J ≤ w * 2 ^ J := Nat.le_mul_of_pos_left _ hw
    omega
  have hW : ∀ i ∈ primIdx R, (0 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
    fun _ _ => by positivity
  have hJr : (J : ℝ) ≤ 2 * (2 + Real.log x) := by
    have := natLog_two_le hN1 (Nat.floor_le hx0)
    rw [hJ]; push_cast; linarith
  calc ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S2long (X i) w i.2‖
      ≤ ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ∑ j ∈ range J, ‖S2block (X i) w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        apply sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (hW i hi)
        rw [S2long_fixed_blocks x (X i) (by linarith [hXlo i hi]) (hXhi i hi) hw hNJ]
        exact norm_sum_le _ _
    _ = ∑ j ∈ range J, ∑ i ∈ primIdx R, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ‖S2block (X i) w (w * 2 ^ j) (N / (w * 2 ^ j)) i.2‖ := by
        simp_rw [mul_sum]; exact sum_comm
    _ ≤ ∑ _j ∈ range J, K₁ * (2 + Real.log x) ^ 3 * G := by
        apply sum_le_sum; intro j _
        exact hblk x hx w hw hwx R hR (w * 2 ^ j) (Nat.le_mul_of_pos_right w (by positivity)) X hXlo hXhi
    _ = J * (K₁ * (2 + Real.log x) ^ 3 * G) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (2 * (2 + Real.log x)) * (K₁ * (2 + Real.log x) ^ 3 * G) :=
        mul_le_mul_of_nonneg_right hJr (by rw [hG]; positivity)
    _ = _ := by ring

#print axioms maximal_S2_long

#print axioms S2summand
#print axioms S2long
#check S2coeff 2 2 2
#check abs_S2coeff_le 2 2 2
#check S2coeff_eq_zero 2 2 5 (by norm_num)
#check S2block 8 2 2 8 (1 : DirichletCharacter ℂ 1)
#check (Classical.choose_spec maximal_S2_block).2 16 (by norm_num) 2 (by norm_num) (by norm_num) 3 (by norm_num) 2 (by norm_num) (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check S2long_fixed_rectangle 16 8 (by norm_num) (by norm_num) 2 (1 : DirichletCharacter ℂ 1)
#check S2long_fixed_blocks (q := 1) 16 8 (by norm_num) (by norm_num) (w := 2) (by norm_num) (J := 4) (by norm_num) 1
#check (Classical.choose_spec maximal_S2_long).2 16 (by norm_num) 2 (by norm_num) (by norm_num) 3 (by norm_num) (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)

/-- Davenport chapter 28 page 167 before display 14. The short part
of the unsigned S2 sum has outer coefficient index at most w. -/
noncomputable def S2short {q : ℕ} (y : ℝ) (w : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ Icc 1 ⌊y⌋₊, if t ≤ w then
    ∑ r ∈ Icc 1 (⌊y⌋₊ / t), (S2coeff w w t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0

#print axioms S2short

/-- Davenport chapter 28 page 167 before display 13. The exact short
and long decomposition for equal cutoffs, in the lab sign convention. -/
theorem S2_eq_short_add_long {q : ℕ} (y : ℝ) (w : ℕ)
    (χ : DirichletCharacter ℂ q) : S2 y w w χ = S2short y w χ + S2long y w χ := by
  have hlong : (∑ t ∈ Icc 1 ⌊y⌋₊, if w < t then
      ∑ r ∈ Icc 1 (⌊y⌋₊ / t), (S2coeff w w t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0) =
      S2long y w χ := by
    unfold S2long
    have hs : Ioc w ⌊y⌋₊ = (Icc 1 ⌊y⌋₊).filter (fun t => w < t) := by
      ext t
      simp only [mem_Ioc, mem_filter, mem_Icc]
      omega
    rw [hs, sum_filter]
    apply sum_congr rfl
    intro t ht
    split_ifs
    · apply sum_congr rfl
      intro r hr
      rw [Nat.cast_mul, map_mul]
      ring
    · rfl
  have h := S2_split_at_cutoff y w w χ
  change S2 y w w χ = S2short y w χ +
    (∑ t ∈ Icc 1 ⌊y⌋₊, if w < t then
      ∑ r ∈ Icc 1 (⌊y⌋₊ / t), (S2coeff w w t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0) at h
  rw [hlong] at h
  exact h

#print axioms S2_eq_short_add_long

/-- Davenport chapter 28 page 167 display 14 before averaging.
Polya Vinogradov costs only w for the short outer range. -/
theorem norm_S2short_le {q : ℕ} [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (x y : ℝ) (hx : 2 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) (w : ℕ) :
    ‖S2short y w χ‖ ≤ w * Real.log x * (Real.sqrt q * (1 + Real.log q)) := by
  set P := Real.sqrt q * (1 + Real.log q)
  have hP : 0 ≤ P := le_trans (norm_nonneg _) (polya_vinogradov_Icc hq hχ 0)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hNx : (⌊y⌋₊ : ℝ) ≤ x := (Nat.floor_le hy).trans hyx
  unfold S2short
  calc
    _ ≤ ∑ t ∈ Icc 1 ⌊y⌋₊,
        ‖if t ≤ w then ∑ r ∈ Icc 1 (⌊y⌋₊ / t),
          (S2coeff w w t : ℂ) * χ (t : ZMod q) * χ (r : ZMod q) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ Icc 1 ⌊y⌋₊, if t ≤ w then Real.log x * P else 0 := by
      apply sum_le_sum
      intro t ht
      split_ifs with htw
      · have ht' := mem_Icc.mp ht
        have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
        have htx : (t : ℝ) ≤ x := (by exact_mod_cast ht'.2 : (t : ℝ) ≤ ⌊y⌋₊).trans hNx
        have hcoef : |S2coeff w w t| ≤ Real.log x :=
          (abs_S2coeff_le w w t).trans (Real.log_le_log ht0 htx)
        have hcoefχ : |S2coeff w w t| * ‖χ (t : ZMod q)‖ ≤ Real.log x :=
          (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)).trans hcoef
        rw [← mul_sum, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hcoefχ (polya_vinogradov_Icc hq hχ _) (norm_nonneg _) hlogx
      · simp only [norm_zero, le_refl]
    _ ≤ _ := by
      simpa [mul_assoc] using sum_ite_le ⌊y⌋₊ w (mul_nonneg hlogx hP)

#print axioms norm_S2short_le

/-- Davenport chapter 28 page 167 displays 14 and 15. The three short
Vaughan norms have a uniform endpoint bound for a primitive character
whose modulus exceeds one. -/
theorem norm_short_parts_le {q : ℕ} [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (x y : ℝ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x) (w : ℕ) :
    ‖S1 y w χ‖ + ‖S2short y w χ‖ + ‖S3 y w χ‖ ≤
      (Real.log 4 + 4) * w + 3 * w * Real.log x * (Real.sqrt q * (1 + Real.log q)) := by
  have h₁ := norm_S1_le χ y w
  have h₂ := norm_S2short_le hq hχ x y hx (by linarith) hyx w
  have h₃ := norm_S3_le hq hχ (by linarith : 1 ≤ y) w
  have hlog : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
  have hP : 0 ≤ Real.sqrt q * (1 + Real.log q) :=
    le_trans (norm_nonneg _) (polya_vinogradov_Icc hq hχ 0)
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hlog hP) (show 0 ≤ 2 * (w : ℝ) by positivity)
  nlinarith only [h₁, h₂, h₃, hmul]

#print axioms norm_short_parts_le

/-- Davenport chapter 28 page 167 displays 14 and 15. The primitive
characters of modulus above one contribute a uniform short part mean. -/
theorem maximal_short_parts : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
    ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ x → ∀ w : ℕ,
    ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
      (∀ i ∈ primIdx Q, 2 ≤ X i) → (∀ i ∈ primIdx Q, X i ≤ x) →
    (∑ i ∈ (primIdx Q).filter (fun i => i.1 ≠ 0),
      ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖)) ≤
      K * (2 + Real.log x) ^ 2 * ((Q : ℝ) ^ 2 * Real.sqrt Q * w) := by
  set C := Real.log 4 + 4 with hC
  have hC0 : 0 ≤ C := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [C]; linarith
  refine ⟨3 * (C + 3), by positivity, ?_⟩
  intro x hx Q hQ hQx w X hXlo hXhi
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsQ : 1 ≤ Real.sqrt Q := (Real.one_le_sqrt).mpr hQR
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set L := 2 + Real.log x with hL
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith only [hL1, sq_nonneg (L - 1)]
  have hfac : 1 ≤ Real.sqrt Q * L ^ 2 := by
    simpa using mul_le_mul hsQ hLsq zero_le_one (Real.sqrt_nonneg (Q : ℝ))
  set S := (primIdx Q).filter (fun i => i.1 ≠ 0)
  have hpoint : ∀ i ∈ S,
      ‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖ ≤
        (C + 3) * w * Real.sqrt Q * L ^ 2 := by
    intro i hi
    obtain ⟨hiS, hi0⟩ := mem_filter.mp hi
    have himem : i.1 < Q ∧ i.2.IsPrimitive := by
      simpa only [primIdx, mem_sigma, mem_range, mem_filter, mem_univ, true_and] using hiS
    have hq : 1 < i.1 + 1 := by omega
    letI : NeZero (i.1 + 1) := ⟨by omega⟩
    have hqQ : (((i.1 + 1 : ℕ)) : ℝ) ≤ Q := by
      exact_mod_cast (show i.1 + 1 ≤ Q by omega)
    have hqpos : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have hlogq : 1 + Real.log ((i.1 + 1 : ℕ) : ℝ) ≤ L := by
      have h := Real.log_le_log hqpos (hqQ.trans hQx)
      dsimp [L]
      linarith
    have hlogq0 : 0 ≤ 1 + Real.log ((i.1 + 1 : ℕ) : ℝ) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) by norm_cast; omega)
      linarith
    have hsqrt : Real.sqrt ((i.1 + 1 : ℕ) : ℝ) ≤ Real.sqrt Q := Real.sqrt_le_sqrt hqQ
    have hP := mul_le_mul hsqrt hlogq hlogq0 (Real.sqrt_nonneg (Q : ℝ))
    have hprod : Real.log x * (Real.sqrt ((i.1 + 1 : ℕ) : ℝ) *
        (1 + Real.log ((i.1 + 1 : ℕ) : ℝ))) ≤ Real.sqrt Q * L ^ 2 := by
      have h := mul_le_mul (show Real.log x ≤ L by dsimp [L]; linarith)
        hP (mul_nonneg (Real.sqrt_nonneg _) hlogq0) (show 0 ≤ L by linarith)
      nlinarith only [h]
    have hshort := norm_short_parts_le hq himem.2 x (X i) hx (hXlo i hiS) (hXhi i hiS) w
    have h₁ := mul_le_mul_of_nonneg_left hfac (show 0 ≤ C * (w : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3 * (w : ℝ) by positivity)
    change ‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖ ≤
      C * w + 3 * w * Real.log x *
        (Real.sqrt ((i.1 + 1 : ℕ) : ℝ) * (1 + Real.log ((i.1 + 1 : ℕ) : ℝ))) at hshort
    nlinarith only [hshort, h₁, h₂]
  have hweights : (∑ i ∈ primIdx Q,
      ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) ≤ 1 + 2 * (Q : ℝ) ^ 2 := by
    have h := large_sieve hQ (fun _ => (1 : ℂ)) 0 1
    have hI : Ioc (0 : ℤ) (0 + ((1 : ℕ) : ℤ)) = {1} := by decide
    rw [hI] at h
    unfold primIdx
    rw [sum_sigma]
    simpa [mul_comm] using h
  have hws : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) ≤ 3 * (Q : ℝ) ^ 2 := by
    have hsub : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) ≤
        ∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    nlinarith only [hsub, hweights, hQR, sq_nonneg ((Q : ℝ) - 1)]
  calc
    _ ≤ ∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        ((C + 3) * w * Real.sqrt Q * L ^ 2) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpoint i hi) (by positivity)
    _ = (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) *
        ((C + 3) * w * Real.sqrt Q * L ^ 2) := by rw [sum_mul]
    _ ≤ (3 * (Q : ℝ) ^ 2) * ((C + 3) * w * Real.sqrt Q * L ^ 2) :=
      mul_le_mul_of_nonneg_right hws (by positivity)
    _ = _ := by ring

#print axioms maximal_short_parts

/-- Davenport chapter 28 page 165. A concrete nonprincipal primitive
character of level three witnesses the short part parameter domain. -/
theorem exists_primitive_level_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive := by
  have hcard : Fintype.card (DirichletCharacter ℂ 3) = 2 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  obtain ⟨χ, hχ⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [hcard]; norm_num : 1 < Fintype.card (DirichletCharacter ℂ 3))
    (1 : DirichletCharacter ℂ 3)
  refine ⟨χ, ?_⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (DirichletCharacter.conductor_dvd_level χ) with h | h
  · exact (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
  · exact h

#print axioms exists_primitive_level_three

#check S2_eq_short_add_long 8 2 (1 : DirichletCharacter ℂ 1)
#check norm_S2short_le (q := 3) (by norm_num) (Classical.choose_spec exists_primitive_level_three) 16 8 (by norm_num) (by norm_num) (by norm_num) 2
#check norm_short_parts_le (q := 3) (by norm_num) (Classical.choose_spec exists_primitive_level_three) 16 8 (by norm_num) (by norm_num) (by norm_num) 2
#check (Classical.choose_spec maximal_short_parts).2 16 (by norm_num) 3 (by norm_num) (by norm_num) 2 (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)

/-- Davenport chapter 28 page 168. The two cutoff choices, expressed
through x equal to t to the sixth, admit an integer rounding with an
absolute constant loss. -/
theorem vaughan_cutoff_root (t : ℝ) (ht : 1 ≤ t) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQt : (Q : ℝ) ^ 2 ≤ t ^ 6) :
    ∃ w : ℕ, 1 ≤ w ∧ (w : ℝ) ^ 3 ≤ t ^ 6 ∧
      (Q : ℝ) * t ^ 6 / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt Q * w ≤
        3 * (t ^ 6 + t ^ 5 * Q + t ^ 3 * (Q : ℝ) ^ 2) := by
  set q : ℝ := (Q : ℝ)
  change q ^ 2 ≤ t ^ 6 at hQt
  have hq1 : 1 ≤ q := by dsimp [q]; exact_mod_cast hQ
  have hq0 : 0 < q := by linarith
  have ht0 : 0 < t := by linarith
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  by_cases hqt : q ≤ t ^ 2
  · set w : ℕ := ⌊t ^ 2⌋₊
    have hw1 : 1 ≤ w := by apply Nat.le_floor; simpa using ht2
    have hwu : (w : ℝ) ≤ t ^ 2 := Nat.floor_le (sq_nonneg t)
    have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    have hwr : t ^ 2 ≤ 2 * (w : ℝ) := by
      have h := Nat.lt_floor_add_one (t ^ 2)
      change t ^ 2 < (w : ℝ) + 1 at h
      linarith
    have hw3 : (w : ℝ) ^ 3 ≤ t ^ 6 := by
      have h := pow_le_pow_left₀ (show 0 ≤ (w : ℝ) by positivity) hwu 3
      nlinarith only [h]
    have hsw : 0 < Real.sqrt (w : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hroot : t ≤ 2 * Real.sqrt (w : ℝ) := by
      apply (sq_le_sq₀ ht0.le (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w)]
      nlinarith only [hwr, hwR]
    have hqroot : Real.sqrt q ≤ t := (Real.sqrt_le_iff).mpr ⟨ht0.le, hqt⟩
    have hqfac : q * Real.sqrt q ≤ t ^ 3 := by
      have h := mul_le_mul hqt hqroot (Real.sqrt_nonneg q) (sq_nonneg t)
      nlinarith only [h]
    have h₁ : q * t ^ 6 / Real.sqrt w ≤ 2 * q * t ^ 5 := by
      rw [div_le_iff₀ hsw]
      have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ q * t ^ 5 by positivity)
      nlinarith only [h]
    have h₂ : q ^ 2 * Real.sqrt q * w ≤ q * t ^ 5 := by
      calc
        _ = (q * (q * Real.sqrt q)) * (w : ℝ) := by ring
        _ ≤ (q * t ^ 3) * t ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hqfac hq0.le) hwu (by positivity) (by positivity)
        _ = _ := by ring
    refine ⟨w, hw1, hw3, ?_⟩
    change q * t ^ 6 / Real.sqrt w + q ^ 2 * Real.sqrt q * w ≤
      3 * (t ^ 6 + t ^ 5 * q + t ^ 3 * q ^ 2)
    nlinarith only [h₁, h₂, show 0 ≤ t ^ 6 by positivity,
      show 0 ≤ t ^ 3 * q ^ 2 by positivity]
  · have hqt' : t ^ 2 ≤ q := le_of_lt (lt_of_not_ge hqt)
    have hq3 : q ≤ t ^ 3 := by
      apply (sq_le_sq₀ hq0.le (by positivity)).mp
      nlinarith only [hQt]
    have ht34 : t ^ 3 ≤ t ^ 4 := by
      have h := mul_le_mul_of_nonneg_right ht (show 0 ≤ t ^ 3 by positivity)
      nlinarith only [h]
    set u := t ^ 4 / q with hu
    have hu1 : 1 ≤ u := by
      dsimp [u]
      rw [le_div_iff₀ hq0]
      nlinarith only [hq3, ht34]
    have hu2 : u ≤ t ^ 2 := by
      dsimp [u]
      rw [div_le_iff₀ hq0]
      have h := mul_le_mul_of_nonneg_left hqt' (sq_nonneg t)
      nlinarith only [h]
    set w : ℕ := ⌊u⌋₊
    have hw1 : 1 ≤ w := by apply Nat.le_floor; simpa using hu1
    have hwu : (w : ℝ) ≤ u := Nat.floor_le (by linarith)
    have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    have hwr : u ≤ 2 * (w : ℝ) := by
      have h := Nat.lt_floor_add_one u
      change u < (w : ℝ) + 1 at h
      linarith
    have hw3 : (w : ℝ) ^ 3 ≤ t ^ 6 := by
      have h := pow_le_pow_left₀ (show 0 ≤ (w : ℝ) by positivity) (hwu.trans hu2) 3
      nlinarith only [h]
    have hsw : 0 < Real.sqrt (w : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have huq : u * q = t ^ 4 := by dsimp [u]; field_simp [hq0.ne']
    have hfloorq : t ^ 4 ≤ 2 * q * (w : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hwr hq0.le
      nlinarith only [h, huq]
    have h6 : t ^ 6 ≤ 2 * q ^ 2 * (w : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_right hqt' (show 0 ≤ t ^ 4 by positivity)
      have h₂ := mul_le_mul_of_nonneg_left hfloorq hq0.le
      nlinarith only [h₁, h₂]
    have hroot : t ^ 3 ≤ 2 * q * Real.sqrt (w : ℝ) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w)]
      nlinarith only [h6, show 0 ≤ q ^ 2 * (w : ℝ) by positivity]
    have hqroot : t ≤ Real.sqrt q := Real.le_sqrt_of_sq_le hqt'
    have h₁ : q * t ^ 6 / Real.sqrt w ≤ 2 * q ^ 2 * t ^ 3 := by
      rw [div_le_iff₀ hsw]
      have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ q * t ^ 3 by positivity)
      nlinarith only [h]
    have h₂ : q ^ 2 * Real.sqrt q * w ≤ q ^ 2 * t ^ 3 := by
      calc
        _ ≤ q ^ 2 * Real.sqrt q * u := mul_le_mul_of_nonneg_left hwu (by positivity)
        _ = q * Real.sqrt q * t ^ 4 := by dsimp [u]; field_simp [hq0.ne'] <;> ring
        _ = (q * t ^ 3) * (Real.sqrt q * t) := by ring
        _ ≤ (q * t ^ 3) * (Real.sqrt q * Real.sqrt q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqroot (Real.sqrt_nonneg q)) (by positivity)
        _ = _ := by rw [Real.mul_self_sqrt hq0.le]; ring
    refine ⟨w, hw1, hw3, ?_⟩
    change q * t ^ 6 / Real.sqrt w + q ^ 2 * Real.sqrt q * w ≤
      3 * (t ^ 6 + t ^ 5 * q + t ^ 3 * q ^ 2)
    nlinarith only [h₁, h₂, show 0 ≤ t ^ 6 by positivity,
      show 0 ≤ t ^ 5 * q by positivity]

#print axioms vaughan_cutoff_root

/-- Davenport chapter 28 page 168. There is a positive integer equal
cutoff whose two remaining parameter costs fit the target polynomial. -/
theorem vaughan_cutoff_choice (x : ℝ) (hx : 2 ≤ x) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQx : (Q : ℝ) ^ 2 ≤ x) :
    ∃ w : ℕ, 1 ≤ w ∧ (w : ℝ) ^ 3 ≤ x ∧
      (Q : ℝ) * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt Q * w ≤
        3 * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) := by
  have hx0 : 0 < x := by linarith
  set t := x ^ (1 / 6 : ℝ)
  have ht : 1 ≤ t := Real.one_le_rpow (by linarith) (by norm_num)
  have ht6 : t ^ 6 = x := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have ht5 : t ^ 5 = x ^ (5 / 6 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hsq : Real.sqrt x = t ^ 3 := by
    rw [← ht6, show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)]
  obtain ⟨w, hw1, hw3, hcost⟩ := vaughan_cutoff_root t ht Q hQ (by rwa [ht6])
  refine ⟨w, hw1, by simpa only [ht6] using hw3, ?_⟩
  simpa only [ht6, ht5, ← hsq] using hcost

#print axioms vaughan_cutoff_choice
#check vaughan_cutoff_choice 64 (by norm_num) 4 (by norm_num) (by norm_num)
#check vaughan_cutoff_choice 64 (by norm_num) 8 (by norm_num) (by norm_num)

/-- Davenport chapter 28 page 167 displays 14 and 15. The single
primitive character of modulus one contributes at most six x. -/
theorem principal_endpoint_mean (x : ℝ) (hx : 0 ≤ x) (Q : ℕ)
    (X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ)
    (hXlo : ∀ i ∈ primIdx Q, 0 ≤ X i) (hXhi : ∀ i ∈ primIdx Q, X i ≤ x) :
    (∑ i ∈ (primIdx Q).filter (fun i => i.1 = 0),
      ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) ≤ 6 * x := by
  classical
  let e : Σ k : ℕ, DirichletCharacter ℂ (k + 1) := ⟨0, 1⟩
  have hsub : (primIdx Q).filter (fun i => i.1 = 0) ⊆ {e} := by
    rintro ⟨k, χ⟩ hi
    have hk : k = 0 := (mem_filter.mp hi).2
    subst k
    have hχ : χ = (1 : DirichletCharacter ℂ 1) := DirichletCharacter.level_one χ
    subst χ
    simp [e]
  have hweights : (∑ i ∈ (primIdx Q).filter (fun i => i.1 = 0),
      ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) ≤ 1 := by
    calc
      _ ≤ ∑ i ∈ ({e} : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))),
          ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp [e]
  calc
    _ ≤ ∑ i ∈ (primIdx Q).filter (fun i => i.1 = 0),
        ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * (6 * x) := by
      apply sum_le_sum
      intro i hi
      have hiS := (mem_filter.mp hi).1
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_psiChi_le_trivial (X i) i.2 (hXlo i hiS)).trans (by linarith [hXhi i hiS])
    _ = (∑ i ∈ (primIdx Q).filter (fun i => i.1 = 0),
        ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient) * (6 * x) := by rw [sum_mul]
    _ ≤ 1 * (6 * x) := mul_le_mul_of_nonneg_right hweights (by positivity)
    _ = _ := one_mul _

#print axioms principal_endpoint_mean

/-- Davenport chapter 28 page 167 after displays 12 to 15. The four
Vaughan components yield the required mean before choosing the cutoff.
CONDITIONAL ON the explicit pointwise Vaughan identity. -/
theorem selected_vaughan_mean
    (hVaughan : ∀ (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0))
    : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ x →
      ∀ w : ℕ, 1 ≤ w → (w : ℝ) ^ 3 ≤ x →
      ∀ X : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ,
        (∀ i ∈ primIdx Q, 2 ≤ X i) → (∀ i ∈ primIdx Q, X i ≤ x) →
      (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) ≤
        K * (2 + Real.log x) ^ 4 *
          (x + (Q : ℝ) ^ 2 * Real.sqrt Q * w + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x) := by
  classical
  obtain ⟨KS, hKS, hshort⟩ := maximal_short_parts
  obtain ⟨KL, hKL, hlong⟩ := maximal_S2_long
  obtain ⟨KT, hKT, htypeII⟩ := maximal_vaughan_typeII
  refine ⟨6 + KS + KL + KT, by positivity, ?_⟩
  intro x hx Q hQ hQx w hw hwx X hXlo hXhi
  have hx0 : 0 ≤ x := by linarith
  set L := 2 + Real.log x
  have hL1 : 1 ≤ L := by
    have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
    dsimp [L]; linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hL24 : L ^ 2 ≤ L ^ 4 := by
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have h := mul_le_mul_of_nonneg_right hL2 (sq_nonneg L)
    nlinarith only [h]
  set P := x + (Q : ℝ) ^ 2 * Real.sqrt Q * w + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hxP : x ≤ P := by
    have h₁ : 0 ≤ (Q : ℝ) ^ 2 * Real.sqrt Q * w := by positivity
    have h₂ : 0 ≤ Q * x / Real.sqrt w := by positivity
    have h₃ : 0 ≤ (Q : ℝ) ^ 2 * Real.sqrt x := by positivity
    dsimp [P]; linarith only [h₁, h₂, h₃]
  have hcostP : (Q : ℝ) ^ 2 * Real.sqrt Q * w ≤ P := by
    have h₂ : 0 ≤ Q * x / Real.sqrt w := by positivity
    have h₃ : 0 ≤ (Q : ℝ) ^ 2 * Real.sqrt x := by positivity
    dsimp [P]; linarith only [hx0, h₂, h₃]
  have hlongP : x + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x ≤ P := by
    have h₁ : 0 ≤ (Q : ℝ) ^ 2 * Real.sqrt Q * w := by positivity
    dsimp [P]; linarith only [h₁]
  set S := (primIdx Q).filter (fun i => i.1 ≠ 0)
  set A := (primIdx Q).filter (fun i => i.1 = 0)
  have hshort0 := hshort x hx Q hQ hQx w X hXlo hXhi
  have hshort' : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
      (‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖)) ≤ KS * L ^ 4 * P := by
    refine hshort0.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL24 hKS.le) hcostP
      (by positivity) (by positivity)
  have hlong0 := hlong x hx w hw hwx Q hQ X hXlo hXhi
  have hlong' : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S2long (X i) w i.2‖) ≤
      KL * L ^ 4 * P := by
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans
      (hlong0.trans ?_)
    exact mul_le_mul_of_nonneg_left hlongP (by positivity)
  have htypeII0 := htypeII x hx w hw Q hQ X hXlo hXhi
  have htypeII' : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 (X i) w w i.2‖) ≤
      KT * L ^ 4 * P := by
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans
      (htypeII0.trans ?_)
    exact mul_le_mul_of_nonneg_left hlongP (by positivity)
  have hprincipal0 := principal_endpoint_mean x hx0 Q X (fun i hi => by linarith [hXlo i hi]) hXhi
  have hprincipal' : (∑ i ∈ A, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) ≤
      6 * L ^ 4 * P := by
    refine hprincipal0.trans ?_
    have h := hxP.trans (show P ≤ L ^ 4 * P by
      simpa using mul_le_mul_of_nonneg_right hL4 hP0)
    nlinarith only [h]
  have hpoint : ∀ i ∈ S, ‖psiChi (X i) i.2‖ ≤
      (‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖) +
        ‖S2long (X i) w i.2‖ + ‖S4 (X i) w w i.2‖ := by
    intro i hi
    rw [psiChi_decomp_from_vaughan hVaughan (X i) w w i.2 hw, S2_eq_short_add_long]
    have h₁ := norm_sub_le (S1 (X i) w i.2 - (S2short (X i) w i.2 + S2long (X i) w i.2) + S3 (X i) w i.2)
      (S4 (X i) w w i.2)
    have h₂ := norm_add_le (S1 (X i) w i.2 - (S2short (X i) w i.2 + S2long (X i) w i.2)) (S3 (X i) w i.2)
    have h₃ := norm_sub_le (S1 (X i) w i.2) (S2short (X i) w i.2 + S2long (X i) w i.2)
    have h₄ := norm_add_le (S2short (X i) w i.2) (S2long (X i) w i.2)
    linarith only [h₁, h₂, h₃, h₄]
  have hnonprincipal : (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) ≤
      (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
        (‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖)) +
      (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S2long (X i) w i.2‖) +
      (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖S4 (X i) w w i.2‖) := by
    calc
      _ ≤ ∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient *
          ((‖S1 (X i) w i.2‖ + ‖S2short (X i) w i.2‖ + ‖S3 (X i) w i.2‖) +
            ‖S2long (X i) w i.2‖ + ‖S4 (X i) w w i.2‖) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpoint i hi) (by positivity)
      _ = _ := by simp only [mul_add, sum_add_distrib]
  have hsplit : (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) =
      (∑ i ∈ A, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) +
      (∑ i ∈ S, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * ‖psiChi (X i) i.2‖) := by
    exact (sum_filter_add_sum_filter_not (primIdx Q) (fun i => i.1 = 0) _).symm
  rw [hsplit]
  change _ ≤ (6 + KS + KL + KT) * L ^ 4 * P
  nlinarith only [hprincipal', hnonprincipal, hshort', hlong', htypeII']

#print axioms selected_vaughan_mean

#check principal_endpoint_mean 16 (by norm_num) 1 (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)
#check (Classical.choose_spec (selected_vaughan_mean vaughan_identity)).2 16 (by norm_num) 3 (by norm_num) (by norm_num) 2 (by norm_num) (by norm_num) (fun _ => 8) (by intro i hi; norm_num) (by intro i hi; norm_num)

/-- LEAF. Davenport chapter 28 page 162 display 2, the maximal primitive
character mean estimate. Its proof uses the large sieve and the chapter 24
Vaughan decomposition supplied as explicit inputs. The factor log of 2 x Q
retains a positive logarithm at the endpoints. CONDITIONAL ON these inputs.
The hyperbolic Type II estimate and Type I summation remain OPEN. -/
theorem maximal_character_mean
    (hLS : ∀ {Q : ℕ} (hQ : 1 ≤ Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ),
    ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      (N + 2 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)
    (hVaughan : ∀ (u v : ℕ) (hv : 1 ≤ v) (n : ℕ) (hn : 1 ≤ n),
    (ArithmeticFunction.vonMangoldt n : ℝ) =
      (if n ≤ u then Λ n else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          ∑ y ∈ x.1.divisorsAntidiagonal, (if y.1 ≤ u ∧ y.2 ≤ v then Λ y.1 * (μ y.2 : ℝ) else 0)
      + ∑ x ∈ n.divisorsAntidiagonal, (if x.1 ≤ v then (μ x.1 : ℝ) * Real.log x.2 else 0)
      - ∑ x ∈ n.divisorsAntidiagonal,
          (if u < x.1 ∧ v < x.2 then
            Λ x.1 * ∑ d ∈ x.2.divisors, (if d ≤ v then (μ d : ℝ) else 0) else 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4 := by
  classical
  obtain ⟨K₀, hK₀, hcore⟩ := selected_vaughan_mean hVaughan
  obtain ⟨K₁, hK₁, hhigh⟩ := maximal_character_mean_high_conductors
  refine ⟨324 * K₀ + K₁, by positivity, ?_⟩
  intro x hx Q hQ
  have hx0 : 0 < x := by linarith
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set M := x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  set B := Real.log (2 * x * Q)
  by_cases hlarge : x ≤ (Q : ℝ) ^ 2
  · refine (hhigh x hx Q hQ hlarge).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show K₁ ≤ 324 * K₀ + K₁ by linarith) hM0) (by positivity)
  · have hQsq : (Q : ℝ) ^ 2 ≤ x := (lt_of_not_ge hlarge).le
    have hQx : (Q : ℝ) ≤ x := by
      have h := sq_nonneg ((Q : ℝ) - 1)
      nlinarith only [hQsq, hQR, h]
    obtain ⟨w, hw1, hw3, hcost⟩ := vaughan_cutoff_choice x hx Q hQ hQsq
    change (Q : ℝ) * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt Q * w ≤ 3 * M at hcost
    let n : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℕ :=
      fun i => Classical.choose (primitiveMax_attained x hx i.2)
    have hatt : ∀ i, 2 ≤ n i ∧ (n i : ℝ) ≤ x ∧ primitiveMax x i.2 = ‖psiChi (n i : ℝ) i.2‖ :=
      fun i => Classical.choose_spec (primitiveMax_attained x hx i.2)
    let Y : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) → ℝ := fun i => (n i : ℝ)
    have hYlo : ∀ i ∈ primIdx Q, 2 ≤ Y i := by
      intro i hi
      change (2 : ℝ) ≤ (n i : ℝ)
      exact_mod_cast (hatt i).1
    have hYhi : ∀ i ∈ primIdx Q, Y i ≤ x := fun i _ => (hatt i).2.1
    have heq : ∀ i, primitiveMax x i.2 = ‖psiChi (Y i) i.2‖ := fun i => (hatt i).2.2
    have h := hcore x hx Q hQ hQx w hw1 hw3 Y hYlo hYhi
    set P := x + (Q : ℝ) ^ 2 * Real.sqrt Q * w + Q * x / Real.sqrt w + (Q : ℝ) ^ 2 * Real.sqrt x
    have hP0 : 0 ≤ P := by dsimp [P]; positivity
    have hbase : x + (Q : ℝ) ^ 2 * Real.sqrt x ≤ M := by
      have hpos : 0 ≤ x ^ (5 / 6 : ℝ) * Q := by positivity
      dsimp [M]
      nlinarith only [hpos]
    have hP : P ≤ 4 * M := by
      dsimp [P]
      nlinarith only [hcost, hbase]
    have hB1 : 1 ≤ B := by
      have harg : (4 : ℝ) ≤ 2 * x * Q := by nlinarith only [hx, hQR, mul_nonneg (by linarith : 0 ≤ x - 2) (by linarith : 0 ≤ (Q : ℝ) - 1)]
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) harg
      have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [he] at hl
      dsimp [B]
      linarith [Real.log_two_gt_d9]
    have hlogx : Real.log x ≤ B := Real.log_le_log hx0 (by nlinarith only [hx0.le, hQR, mul_nonneg hx0.le (by linarith : 0 ≤ (Q : ℝ) - 1)])
    have hL0 : 0 ≤ 2 + Real.log x := by
      have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
      linarith
    have hL4 : (2 + Real.log x) ^ 4 ≤ 81 * B ^ 4 := by
      calc
        _ ≤ (3 * B) ^ 4 := pow_le_pow_left₀ hL0 (by linarith only [hB1, hlogx]) 4
        _ = _ := by ring
    have hbound : K₀ * (2 + Real.log x) ^ 4 * P ≤ 324 * K₀ * M * B ^ 4 := by
      calc
        _ ≤ (K₀ * (81 * B ^ 4)) * (4 * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL4 hK₀.le) hP hP0 (by positivity)
        _ = _ := by ring
    have hsum : (∑ i ∈ primIdx Q, ((i.1 + 1 : ℕ) : ℝ) / (i.1 + 1).totient * primitiveMax x i.2) =
        ∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive), primitiveMax x χ := by
      unfold primIdx
      rw [sum_sigma]
      simp_rw [mul_sum]
    rw [← hsum]
    simp_rw [heq]
    refine h.trans (hbound.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 324 * K₀ ≤ 324 * K₀ + K₁ by linarith) hM0) (by positivity)

#print axioms maximal_character_mean

/-- Davenport chapter 28 page 162 display 2. The lab large sieve and
Vaughan identity supply both sealed inputs, giving the unconditional
maximal primitive character mean. -/
theorem maximal_character_mean_unconditional :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4 := by
  exact maximal_character_mean large_sieve vaughan_identity

#print axioms maximal_character_mean_unconditional
#check (Classical.choose_spec maximal_character_mean_unconditional).2 2 (by norm_num) 1 (by norm_num)
#check (Classical.choose_spec maximal_character_mean_unconditional).2 2 (by norm_num) 2 (by norm_num)
#check (Classical.choose_spec maximal_character_mean_unconditional).2 64 (by norm_num) 4 (by norm_num)
#check (Classical.choose_spec maximal_character_mean_unconditional).2 64 (by norm_num) 8 (by norm_num)

/-- Davenport chapter 28 page 162 display 2. Below endpoint two, the
maximal von Mangoldt character sum vanishes since Lambda at one is zero. -/
theorem primitiveMax_eq_zero_of_lt_two {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : x < 2) : primitiveMax x χ = 0 := by
  apply le_antisymm _ (primitiveMax_nonneg x χ)
  apply csSup_le (Set.insert_nonempty _ _)
  rintro v (rfl | ⟨y, hy, hyx, rfl⟩)
  · exact le_rfl
  · have hfy : ⌊y⌋₊ < 2 := by
      exact_mod_cast ((Nat.floor_le hy).trans_lt (hyx.trans_lt hx))
    have hz : psiChi y χ = 0 := by
      unfold psiChi
      apply sum_eq_zero
      intro n hn
      have hn' := mem_Icc.mp hn
      have hn1 : n = 1 := by omega
      subst n
      simp
    rw [hz, norm_zero]

#print axioms primitiveMax_eq_zero_of_lt_two

/-- Davenport chapter 28 page 162 display 2, including the full lower
source range x at least one, with the verified positive logarithm convention. -/
theorem maximal_character_mean_one_le :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → ∀ Q : ℕ, 1 ≤ Q →
      (∑ k ∈ range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter
          (fun χ => χ.IsPrimitive), primitiveMax x χ) ≤
      K * (x + x ^ (5 / 6 : ℝ) * Q + Real.sqrt x * (Q : ℝ) ^ 2) *
        Real.log (2 * x * Q) ^ 4 := by
  obtain ⟨K, hK, hmean⟩ := maximal_character_mean_unconditional
  refine ⟨K, hK, ?_⟩
  intro x hx Q hQ
  by_cases hx2 : 2 ≤ x
  · exact hmean x hx2 Q hQ
  · have hx0 : 0 < x := by linarith
    have hzero {q : ℕ} (χ : DirichletCharacter ℂ q) : primitiveMax x χ = 0 :=
      primitiveMax_eq_zero_of_lt_two x χ (lt_of_not_ge hx2)
    simp_rw [hzero]
    simp only [sum_const_zero, mul_zero]
    positivity

#print axioms maximal_character_mean_one_le
#check primitiveMax_eq_zero_of_lt_two (3 / 2) (1 : DirichletCharacter ℂ 1) (by norm_num)
#check (Classical.choose_spec maximal_character_mean_one_le).2 1 (by norm_num) 1 (by norm_num)
#check (Classical.choose_spec maximal_character_mean_one_le).2 (3 / 2) (by norm_num) 3 (by norm_num)

end LeanLab.KumchevLiu2007.Task557a
