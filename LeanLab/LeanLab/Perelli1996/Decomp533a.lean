/-
Perelli 1996, pages 481, 486 and 487, equations 3, 27 and 28.
Supply helpers for the secondary major arc mean.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp289a
import LeanLab.Perelli1996.Ramanujan103
import LeanLab.Perelli1996.Localization103
import LeanLab.Perelli1996.Decomp320a
import LeanLab.Perelli1996.Decomp400d

namespace LeanLab.Perelli1996.Decomp400e
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
noncomputable section

/-- Page 486 before equation 26. Periodic enclosing arcs of radius one over q Q.
These contain the printed Farey cells and are the domains of the remainder mass. -/
def meanMajorArcs (F : ℤ[X]) (N H B : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.log N ^ B ∧
    ∃ a : ℤ, Nat.Coprime a.natAbs q ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * meanOrder F N H B)}

/-- Page 486 equation 26. Real part of the major arc prime mean integral. -/
def majorPrimeMean (F : ℤ[X]) (M : ℕ) (N H B : ℝ) : ℝ :=
  (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B,
    primeSum M α ^ 2 * Section2.polynomialKernel F N H (-α)).re

/-- Pages 486 and 487 equations 27 and 28. The truncated singular mean.
The Ramanujan sum at a negative integer equals its value at that integer's absolute value.
The cutoff hypotheses in the leaves ensure nonnegative polynomial values. -/
def truncatedWeightedMean (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  (∑ n ∈ win F N H, ((Fv F n : ℝ) : ℂ) *
    ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
      ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
        Ramanujan103.ramanujanSum q (Fv F n).toNat).re

end
end LeanLab.Perelli1996.Decomp400e

namespace LeanLab.Perelli1996.Decomp533a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
open LeanLab.Perelli1996.Decomp400e
noncomputable section

/-- Page 486 before equation 26. The enclosing secondary arcs are periodic. -/
theorem mem_meanMajorArcs_add_one (F : ℤ[X]) (N H B α : ℝ) :
    α + 1 ∈ meanMajorArcs F N H B ↔ α ∈ meanMajorArcs F N H B := by
  constructor
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a - q, ?_, ?_⟩
    · rw [ArcModel320.coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left (-1)
      rwa [mul_neg_one, ← sub_eq_add_neg] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have he : α - ((a - q : ℤ) : ℝ) / q = α + 1 - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [he]
  · rintro ⟨q, hq, hqB, a, hcop, hα⟩
    refine ⟨q, hq, hqB, a + q, ?_, ?_⟩
    · rw [ArcModel320.coprime_iff_isCoprime] at hcop ⊢
      have := hcop.add_mul_left_left 1
      rwa [mul_one] at this
    · have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have he : α + 1 - ((a + q : ℤ) : ℝ) / q = α - (a : ℝ) / q := by
        push_cast; field_simp; ring
      rwa [he]

/-- Page 486 before equation 26. For separated enclosing arcs, integrate a
continuous periodic function by summing the full rational intervals.
The period shift keeps the endpoint arc intact. -/
theorem mean_arc_integral_split (F : ℤ[X]) (N H B : ℝ)
    (hP1 : 1 ≤ Real.log N ^ B)
    (hsep : 2 * (Real.log N ^ B) ^ 2 < meanOrder F N H B)
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    ∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α =
      ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
            (1 / ((q : ℝ) * meanOrder F N H B)), f ((a : ℝ) / q + η) := by
  set P := Real.log N ^ B with hP
  set Q := meanOrder F N H B with hQ
  set r := 1 / Q with hr
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by nlinarith [sq_nonneg P]
  have hr0 : 0 < r := by positivity
  have hsmall : 2 * r * (P * P) < 1 := by
    rw [hr]
    have he : 2 * (1 / Q) * (P * P) = (2 * P ^ 2) / Q := by ring
    rw [he, div_lt_one hQ0]
    exact hsep
  have hrad (q : ℕ) (hq : 1 ≤ q) : 1 / ((q : ℝ) * Q) ≤ r := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    apply one_div_le_one_div_of_le hQ0
    nlinarith
  have hqr : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r * q < 1 := by
    intro q hq hqP
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have : (q : ℝ) ≤ P * P := by nlinarith
    calc 2 * r * q ≤ 2 * r * (P * P) := by gcongr
      _ < 1 := hsmall
  have hinv : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → 2 * r < 1 / q := by
    intro q hq hqP
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    rw [lt_div_iff₀ hq0]
    exact hqr q hq hqP
  have hMA : MeasurableSet (meanMajorArcs F N H B) := by
    unfold meanMajorArcs; measurability
  have hgper : Function.Periodic ((meanMajorArcs F N H B).indicator f) 1 := by
    intro α
    simp only [Set.indicator, hper α]
    by_cases h : α ∈ meanMajorArcs F N H B
    · rw [if_pos ((mem_meanMajorArcs_add_one F N H B α).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mem_meanMajorArcs_add_one F N H B α).mp h')), if_neg h]
  set Z := ⌊P⌋₊ with hZ
  let idx := (Icc 1 Z).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))
  let J : (Σ _ : ℕ, ℕ) → Set ℝ := fun i => Set.Icc ((i.2 : ℝ) / i.1 - 1 / ((i.1 : ℝ) * Q))
    ((i.2 : ℝ) / i.1 + 1 / ((i.1 : ℝ) * Q))
  have hmemidx : ∀ i ∈ idx, 1 ≤ i.1 ∧ (i.1 : ℝ) ≤ P ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    intro i hi
    simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1.1, (Nat.cast_le.mpr hi.1.2).trans (Nat.floor_le hP0.le), hi.2.1, hi.2.2⟩
  have step1 : ∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α =
      ∫ α in (0 : ℝ)..1, (meanMajorArcs F N H B).indicator f α := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator hMA]
  have step2 : ∫ α in (0 : ℝ)..1, (meanMajorArcs F N H B).indicator f α =
      ∫ α in Set.Ioc (-r) (-r + 1) ∩ meanMajorArcs F N H B, f α := by
    have := hgper.intervalIntegral_add_eq 0 (-r)
    rw [zero_add] at this
    rw [this, intervalIntegral.integral_of_le (by linarith), setIntegral_indicator hMA]
  have hae : (Set.Ioc (-r) (-r + 1) ∩ meanMajorArcs F N H B : Set ℝ) =ᵐ[volume] ⋃ i ∈ idx, J i := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · apply measure_mono_null _ (measure_singleton (-r + 1))
      rintro α ⟨⟨⟨hlo, hhi⟩, q, hq, hqP, a, hcop, hα⟩, hU⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hU
      have hαraw := hα
      have hα : |α - (a : ℝ) / q| ≤ r := hα.trans (hrad q hq)
      rw [abs_le] at hα
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
      have h2r := hinv q hq hqP
      rcases lt_or_ge a 0 with ha | ha
      · exfalso
        have ha1 : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
        have : (a : ℝ) / q ≤ -1 / q := div_le_div_of_nonneg_right ha1 hq0.le
        have h1q : -1 / (q : ℝ) = -(1 / q) := by ring
        linarith
      rcases lt_or_ge a q with haq | haq
      · lift a to ℕ using ha
        simp only [Set.mem_iUnion]
        refine ⟨⟨q, a⟩, ?_, ?_⟩
        · simp only [idx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
          refine ⟨⟨hq, Nat.le_floor hqP⟩, by exact_mod_cast haq, ?_⟩
          simpa using hcop
        · simp only [J, Set.mem_Icc]
          rw [abs_le] at hαraw
          push_cast at hαraw
          constructor <;> linarith
      · exfalso
        have ha1 : (q : ℝ) ≤ a := by exact_mod_cast haq
        have : (1 : ℝ) ≤ (a : ℝ) / q := by rw [le_div_iff₀ hq0]; linarith
        apply hne
        linarith
    · apply measure_mono_null _ (measure_singleton (-r))
      intro α hα
      simp only [Set.mem_diff, Set.mem_iUnion] at hα
      obtain ⟨⟨i, hi, hαi⟩, hn⟩ := hα
      obtain ⟨hq1, hqP, haq, hcop⟩ := hmemidx i hi
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hn
      have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast hq1
      have h2r := hinv i.1 hq1 hqP
      simp only [J, Set.mem_Icc] at hαi
      have hri := hrad i.1 hq1
      have hαicommon : (i.2 : ℝ) / i.1 - r ≤ α ∧ α ≤ (i.2 : ℝ) / i.1 + r := by
        constructor <;> linarith
      have ha0 : (0 : ℝ) ≤ (i.2 : ℝ) / i.1 := by positivity
      have haq' : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast haq
      have hfrac0 : (i.2 : ℝ) / i.1 ≤ ((i.1 : ℝ) - 1) / i.1 :=
        div_le_div_of_nonneg_right (by linarith) hq0.le
      have hfrace : ((i.1 : ℝ) - 1) / i.1 = 1 - 1 / i.1 := by field_simp
      refine ⟨⟨lt_of_le_of_ne (by linarith) (Ne.symm hne), by linarith⟩, i.1, hq1, hqP,
        (i.2 : ℤ), by simpa using hcop, ?_⟩
      rw [abs_le]; push_cast; constructor <;> linarith [hαi.1, hαi.2]
  have hdisj : Set.Pairwise (↑idx) (Function.onFun Disjoint J) := by
    intro i hi j hj hij
    show Disjoint (J i) (J j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨hq1, hqP, -, hcop⟩ := hmemidx i hi
    obtain ⟨hq1', hqP', -, hcop'⟩ := hmemidx j hj
    obtain ⟨h1, h2⟩ := ArcModel320.arcs_eq_of_mem P r hsmall i.1 j.1 i.2 j.2 hq1 hq1' hqP hqP' hcop hcop'
      x (by
        have := hrad i.1 hq1
        simp only [J, Set.mem_Icc] at hxi
        constructor <;> linarith [hxi.1, hxi.2]) (by
        have := hrad j.1 hq1'
        simp only [J, Set.mem_Icc] at hxj
        constructor <;> linarith [hxj.1, hxj.2])
    exact hij (Sigma.ext h1 (heq_of_eq h2))
  rw [step1, step2, setIntegral_congr_set hae,
    integral_biUnion_finset idx (fun i _ => measurableSet_Icc) hdisj
      (fun i _ => hf.integrableOn_Icc), Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hδ : 0 < 1 / ((q : ℝ) * Q) := by positivity
  apply Finset.sum_congr rfl
  intro a _
  simp only [J]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_left f ((a : ℝ) / q), sub_eq_add_neg]

/-- Page 486 equation 27. Reduced residues can use either endpoint convention
when the values at zero and the modulus agree. -/
theorem sum_reduced_range_eq_Icc {E : Type*} [AddCommMonoid E]
    (q : ℕ) (hq : 0 < q) (g : ℕ → E) (hends : g 0 = g q) :
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), g a =
      ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q), g a := by
  classical
  by_cases hq1 : q = 1
  · subst q
    simpa using hends
  · have heq : (range q).filter (fun a => Nat.Coprime a q) =
        (Icc 1 q).filter (fun a => Nat.Coprime a q) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨ha, hc⟩
        have ha0 : a ≠ 0 := by
          intro hz
          subst a
          simp only [Nat.coprime_zero_left] at hc
          exact hq1 hc
        exact ⟨⟨by omega, by omega⟩, hc⟩
      · rintro ⟨⟨ha1, haq⟩, hc⟩
        have hane : a ≠ q := by
          intro he
          subst a
          simp only [Nat.coprime_self] at hc
          exact hq1 hc
        exact ⟨by omega, hc⟩
    rw [heq]

/-- Page 486 equation 27. The rational interval decomposition also holds
with the paper's reduced residue representatives from one through q. -/
theorem mean_arc_integral_split_Icc (F : ℤ[X]) (N H B : ℝ)
    (hP1 : 1 ≤ Real.log N ^ B)
    (hsep : 2 * (Real.log N ^ B) ^ 2 < meanOrder F N H B)
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    ∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α =
      ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
            (1 / ((q : ℝ) * meanOrder F N H B)), f ((a : ℝ) / q + η) := by
  rw [mean_arc_integral_split F N H B hP1 hsep f hf hper]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos := (Finset.mem_Icc.mp hq).1
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  apply sum_reduced_range_eq_Icc q hqpos
  simp only [Nat.cast_zero, zero_div, zero_add, div_self hqne]
  apply intervalIntegral.integral_congr
  intro η hη
  simpa only [add_comm] using (hper η).symm

/-- Page 486 equation 27. The principal coefficient before extending each
rational arc to the full period. The radius depends on its denominator. -/
def principalMean (F : ℤ[X]) (M : ℕ) (N H B : ℝ) : ℂ :=
  ∑ n ∈ win F N H, ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
    Series320.coefficient (Fv F n).toNat q *
      (∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
        (1 / ((q : ℝ) * meanOrder F N H B)),
        Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * η))

/-- Page 486 equation 27. The sum of the rational principal integrals
is exactly the variable radius coefficient model before completion. -/
theorem principal_integral_eq (F : ℤ[X]) (M : ℕ) (N H B : ℝ)
    (hcut : ∀ n ∈ win F N H, 0 ≤ Fv F n) :
    (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
          (1 / ((q : ℝ) * meanOrder F N H B)),
          (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
            Kernel.T 0 (M + 1) η) ^ 2 *
            Section2.polynomialKernel F N H (-((a : ℝ) / q + η))) =
      principalMean F M N H B := by
  unfold principalMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  let d := 1 / ((q : ℝ) * meanOrder F N H B)
  have hterm (a n : ℕ) (hn : n ∈ win F N H) (η : ℝ) :
      (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Kernel.T 0 (M + 1) η) ^ 2 *
          Kernel.e ((Fv F n : ℝ) * (-((a : ℝ) / q + η))) =
      (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
        Kernel.e (-((Fv F n).toNat : ℝ) * ((a : ℝ) / q))) *
          (Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * η)) := by
    have hcast : (Fv F n : ℝ) = ((Fv F n).toNat : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (hcut n hn)).symm
    rw [hcast, show ((Fv F n).toNat : ℝ) * (-((a : ℝ) / q + η)) =
      -((Fv F n).toNat : ℝ) * ((a : ℝ) / q) + -((Fv F n).toNat : ℝ) * η by ring,
      Parseval103.e_add]
    ring
  have hsum (a : ℕ) :
      (∫ η in (-d)..d,
        (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Kernel.T 0 (M + 1) η) ^ 2 *
          Section2.polynomialKernel F N H (-((a : ℝ) / q + η))) =
      ∑ n ∈ win F N H,
        (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 2 *
          Kernel.e (-((Fv F n).toNat : ℝ) * ((a : ℝ) / q))) *
            (∫ η in (-d)..d, Kernel.T 0 (M + 1) η ^ 2 *
              Kernel.e (-((Fv F n).toNat : ℝ) * η)) := by
    unfold Section2.polynomialKernel
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      simp_rw [hterm a n hn]
      exact intervalIntegral.integral_const_mul _ _
    · intro n hn
      apply Continuous.intervalIntegrable
      unfold Kernel.T Kernel.e
      fun_prop
  change (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), _) = _
  refine (Finset.sum_congr rfl (fun a _ => hsum a)).trans ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_mul, ← ArcModel320.coefficient_eq_sum _ q (Finset.mem_Icc.mp hq).1]

/-- Page 486 equation 27. The variable radius principal model keeps both
the reciprocal endpoint tail and the one unit inclusive kernel correction. -/
theorem variable_model_error :
    ∃ C : ℝ, 0 < C ∧ ∀ m M : ℕ, 0 < m → m ≤ M →
      ∀ P Q : ℝ, 0 ≤ P → 2 ≤ Q → ∀ s : Finset ℕ,
      (∀ q ∈ s, 0 < q ∧ (q : ℝ) ≤ P) →
      ‖(∑ q ∈ s, Series320.coefficient m q *
          (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
            Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η))) -
          (m : ℂ) * ∑ q ∈ s, Series320.coefficient m q‖ ≤
        C * (1 + Real.log m) * (1 + P * Q / 2) := by
  obtain ⟨C, hC, habs⟩ := Absolute320.sum_norm_le_log
  refine ⟨C, hC, ?_⟩
  intro m M hm hmM P Q hP hQ s hs
  have hQ0 : 0 < Q := by linarith
  have hsum : ∑ q ∈ s, ‖Series320.coefficient m q‖ ≤ C * (1 + Real.log m) :=
    ((Series320.summable_norm_coefficient m hm).sum_le_tsum s
      (fun _ _ => norm_nonneg _)).trans (habs m hm)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ s, ‖Series320.coefficient m q *
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η)) -
        (m : ℂ) * Series320.coefficient m q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ s, ‖Series320.coefficient m q‖ * (1 + P * Q / 2) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqpos, hqP⟩ := hs q hq
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
      have hq0 : (0 : ℝ) < q := by linarith
      have hδ : 0 < 1 / ((q : ℝ) * Q) := by positivity
      have hhalf : 1 / ((q : ℝ) * Q) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        nlinarith
      have hk := PrincipalTail320.central_coefficient_error M m hmM
        (1 / ((q : ℝ) * Q)) hδ hhalf
      have he : 1 / (2 * (1 / ((q : ℝ) * Q))) = (q : ℝ) * Q / 2 := by field_simp
      rw [he] at hk
      have heq : Series320.coefficient m q *
          (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
            Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η)) -
          (m : ℂ) * Series320.coefficient m q =
          Series320.coefficient m q *
            ((∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
              Kernel.T 0 (M + 1) η ^ 2 * Kernel.e (-(m : ℝ) * η)) - (m : ℂ)) := by ring
      rw [heq, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact hk.trans (by nlinarith)
    _ = (∑ q ∈ s, ‖Series320.coefficient m q‖) * (1 + P * Q / 2) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Page 486 equation 27, derived algebra. Subtracting the principal square
leaves one squared remainder and one cross term. -/
theorem square_remainder_bound (u v z : ℂ) (k : ℝ) (hk : ‖z‖ ≤ k) :
    ‖(u ^ 2 - v ^ 2) * z‖ ≤
      k * (‖u - v‖ ^ 2 + 2 * ‖v‖ * ‖u - v‖) := by
  have he : u ^ 2 - v ^ 2 = (u - v) ^ 2 + 2 * v * (u - v) := by ring
  rw [norm_mul]
  calc
    _ ≤ (‖u - v‖ ^ 2 + 2 * ‖v‖ * ‖u - v‖) * k := by
      apply mul_le_mul _ hk (norm_nonneg _) (by positivity)
      rw [he]
      refine (norm_add_le _ _).trans ?_
      simp [norm_pow]
    _ = _ := by ring

/-- Page 486 equation 27, derived Cauchy Schwarz step on a single arc.
The remainder and the principal kernel stay explicit. -/
theorem integral_square_remainder_bound (u v z : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v) (hz : Continuous z)
    (a b k : ℝ) (hk : 0 ≤ k) (hbound : ∀ x ∈ Set.Icc a b, ‖z x‖ ≤ k) :
    ‖∫ x in Set.Icc a b, (u x ^ 2 - v x ^ 2) * z x‖ ≤
      k * ((∫ x in Set.Icc a b, ‖u x - v x‖ ^ 2) +
        2 * Real.sqrt ((∫ x in Set.Icc a b, ‖v x‖ ^ 2) *
          (∫ x in Set.Icc a b, ‖u x - v x‖ ^ 2))) := by
  have hmem (f : ℝ → ℂ) (hf : Continuous f) :
      MemLp f 2 (volume.restrict (Set.Icc a b)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable C
    exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => hC x hx)
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Set.Icc a b)) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by norm_num [Real.holderConjugate_iff])
    (by simpa using hmem v hv) (by simpa using hmem (u - v) (hu.sub hv))
  simp only [Real.rpow_two, Pi.sub_apply] at hcs
  rw [show (1 : ℝ) / 2 = 1 / 2 by rfl, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (integral_nonneg (fun _ => sq_nonneg _))] at hcs
  have hcont : Continuous (fun x => ‖u x - v x‖ ^ 2 + 2 * ‖v x‖ * ‖u x - v x‖) := by
    fun_prop
  calc
    _ ≤ ∫ x in Set.Icc a b, ‖(u x ^ 2 - v x ^ 2) * z x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Icc a b, k * (‖u x - v x‖ ^ 2 + 2 * ‖v x‖ * ‖u x - v x‖) := by
      apply setIntegral_mono_on
        ((hu.pow 2 |>.sub (hv.pow 2) |>.mul hz).norm.integrableOn_Icc)
        ((hcont.const_mul k).integrableOn_Icc) measurableSet_Icc
      intro x hx
      exact square_remainder_bound (u x) (v x) (z x) k (hbound x hx)
    _ = k * ((∫ x in Set.Icc a b, ‖u x - v x‖ ^ 2) +
        2 * ∫ x in Set.Icc a b, ‖v x‖ * ‖u x - v x‖) := by
      have hi1 : IntegrableOn (fun x => ‖u x - v x‖ ^ 2) (Set.Icc a b) := by
        apply Continuous.integrableOn_Icc
        fun_prop
      have hi2 : IntegrableOn (fun x => 2 * (‖v x‖ * ‖u x - v x‖)) (Set.Icc a b) := by
        apply Continuous.integrableOn_Icc
        fun_prop
      simp_rw [mul_assoc (2 : ℝ)]
      rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul]
    _ ≤ _ := by gcongr

/-- Page 486 dissection. The secondary order eventually exceeds every
fixed bound on the Theorem 2 window. -/
theorem meanOrder_eventually (F : ℤ[X]) (hF : Admissible F)
    (ε B T : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      T ≤ meanOrder F N H B := by
  let δ := 1 / (12 * (F.natDegree : ℝ)) + ε / 2
  have hk : 0 < (F.natDegree : ℝ) := by
    exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NG, hNG, hg⟩ := Section3.power_error_log_saving δ B hδ
  obtain ⟨NT, hNT⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually (Filter.eventually_ge_atTop T))
  refine ⟨max NG NT, hNG.trans (le_max_left _ _), ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := hNG.trans ((le_max_left _ _).trans hN)
  have hN1 : 1 ≤ N := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have hpow : N ^ δ ≤ H * Real.log N ^ (-B) := by
    apply hg N H ((le_max_left _ _).trans hN)
    convert hH using 1
    dsimp [δ]
    congr 1
    ring
  calc
    T ≤ N ^ δ := hNT N ((le_max_right _ _).trans hN)
    _ ≤ H * Real.log N ^ (-B) := hpow
    _ ≤ meanOrder F N H B := by
      unfold meanOrder
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hH1 (by have := hF.1; omega)) (Real.rpow_nonneg (Real.log_nonneg hN1) _)

/-- Page 486 dissection. On the Theorem 2 window the enclosing rational
intervals are eventually separated, even at the largest allowed denominator. -/
theorem meanOrder_separated (F : ℤ[X]) (hF : Admissible F)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      1 ≤ Real.log N ^ B ∧ 2 * (Real.log N ^ B) ^ 2 < meanOrder F N H B := by
  obtain ⟨NQ, hNQ, hq⟩ := meanOrder_eventually F hF ε (3 * B) 3 hε
  refine ⟨max NQ (Real.exp 1), hNQ.trans (le_max_left _ _), ?_⟩
  intro N H hN hH
  have hNE : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL0 : 0 < Real.log N := by linarith
  have hP : 1 ≤ Real.log N ^ B := Real.one_le_rpow hL1 hB.le
  refine ⟨hP, ?_⟩
  have hQ := hq N H ((le_max_left _ _).trans hN) hH
  have he : meanOrder F N H (3 * B) * (Real.log N ^ B) ^ 2 = meanOrder F N H B := by
    unfold meanOrder
    rw [← Real.rpow_mul_natCast hL0.le, mul_assoc, ← Real.rpow_add hL0]
    congr 2
    ring
  rw [← he]
  nlinarith [sq_nonneg (Real.log N ^ B)]

/-- Page 486 equation 27. Completing the variable radius principal kernel
costs an arbitrary logarithmic saving on the stated upper window.
Both the enclosing arc tails and the inclusive endpoint are retained. -/
theorem principal_completion (F : ℤ[X]) (hF : Admissible F)
    (A ε B c : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      |(principalMean F ⌊c * N⌋₊ N H B).re - truncatedWeightedMean F N H B| ≤
        C * H * N * Real.log N ^ (-A) := by
  obtain ⟨CK, hCK, hk⟩ := variable_model_error
  obtain ⟨NQ, hNQ, hq⟩ := meanOrder_eventually F hF ε B 2 hε
  obtain ⟨NP, hNP, hp⟩ := Decomp320a.window_pos F hF
  let k : ℝ := F.natDegree
  have hkpos : 0 < k := by
    dsimp [k]
    exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  let δ := min 1 (k * ε)
  have hδ : 0 < δ := lt_min (by norm_num) (mul_pos hkpos hε)
  have hg := (isLittleO_log_rpow_rpow_atTop (A + 1) hδ).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨NG, hNG⟩ := Filter.eventually_atTop.mp hg
  let N₀ := max (max NQ NP) (max NG (Real.exp 1))
  refine ⟨4 * CK * (2 + |Real.log c|), N₀, by positivity,
    hNQ.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut
  have hNQ' : NQ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNG' : NG ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 3 ≤ N := hNQ.trans hNQ'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL0 : 0 < Real.log N := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have hH0 : 0 < H := by linarith
  have hQ2 := hq N H hNQ' hH
  have hPQ : Real.log N ^ B * meanOrder F N H B = H ^ F.natDegree := by
    unfold meanOrder
    rw [mul_left_comm, ← Real.rpow_add hL0]
    simp
  have hkne : (F.natDegree : ℝ) ≠ 0 := by change k ≠ 0; exact ne_of_gt hkpos
  have hpoly : H ^ F.natDegree ≤ N ^ (1 - δ) := by
    calc
      _ ≤ (N ^ (1 / (F.natDegree : ℝ) - ε)) ^ F.natDegree :=
        pow_le_pow_left₀ hH0.le hHu _
      _ = N ^ (1 - k * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        dsimp [k]
        field_simp [hkne] <;> ring
      _ ≤ N ^ (1 - δ) := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [δ]; linarith [min_le_right 1 (k * ε)])
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hscale : Real.log N * (1 + Real.log N ^ B * meanOrder F N H B / 2) ≤
      2 * N * Real.log N ^ (-A) := by
    have hg' := hNG N hNG'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul] at hg'
    have hNpow : 1 ≤ N ^ (1 - δ) := Real.one_le_rpow hN1 (by linarith)
    have hh : Real.log N ^ (A + 1) * (1 + H ^ F.natDegree / 2) ≤ 2 * N := by
      calc
        _ ≤ N ^ δ * (2 * N ^ (1 - δ)) := by gcongr; nlinarith
        _ = 2 * N := by rw [← mul_assoc, mul_comm (N ^ δ) 2, mul_assoc, ← Real.rpow_add hN0]; norm_num
    rw [hPQ]
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hL0 A)).mp
    have he : Real.log N ^ (-A) * Real.log N ^ A = 1 := by
      rw [← Real.rpow_add hL0]; simp
    calc
      _ = Real.log N ^ (A + 1) * (1 + H ^ F.natDegree / 2) := by
        rw [Real.rpow_add hL0, Real.rpow_one]
        ring
      _ ≤ 2 * N := hh
      _ = _ := by
        rw [show Real.log N ^ A * (2 * N * Real.log N ^ (-A)) =
          2 * N * (Real.log N ^ (-A) * Real.log N ^ A) by ring, he, mul_one]
  have hpoint (n : ℕ) (hn : n ∈ win F N H) :
      ‖(∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient (Fv F n).toNat q *
        (∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
          (1 / ((q : ℝ) * meanOrder F N H B)),
          Kernel.T 0 (⌊c * N⌋₊ + 1) η ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * η))) -
        ((Fv F n : ℝ) : ℂ) * ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
          Series320.coefficient (Fv F n).toNat q‖ ≤
        2 * CK * (2 + |Real.log c|) * N * Real.log N ^ (-A) := by
    let m := (Fv F n).toNat
    have hm := hp N H hNP' n hn
    have hmFloor : (m : ℝ) ≤ (⌊c * N⌋₊ : ℝ) := by exact_mod_cast (hcut n hn).2
    have hmN : (m : ℝ) ≤ c * N := hmFloor.trans (Nat.floor_le (by positivity))
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hcast : ((Fv F n : ℝ) : ℂ) = (m : ℂ) := by
      dsimp [m]
      exact_mod_cast (Int.toNat_of_nonneg (hcut n hn).1).symm
    rw [hcast]
    have hlogm := Real.log_le_log hmR hmN
    rw [Real.log_mul hc.ne' hN0.ne'] at hlogm
    have hlog : 1 + Real.log m ≤ (2 + |Real.log c|) * Real.log N := by
      nlinarith [le_abs_self (Real.log c), mul_nonneg (abs_nonneg (Real.log c)) (sub_nonneg.mpr hL1)]
    have hb := hk m ⌊c * N⌋₊ hm (hcut n hn).2 (Real.log N ^ B)
      (meanOrder F N H B) (by positivity) hQ2 (Icc 1 ⌊Real.log N ^ B⌋₊)
      (by
        intro q hq
        refine ⟨(Finset.mem_Icc.mp hq).1, ?_⟩
        have hf : (q : ℝ) ≤ (⌊Real.log N ^ B⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).2
        exact hf.trans (Nat.floor_le (Real.rpow_nonneg hL0.le _)))
    calc
      _ ≤ CK * (1 + Real.log m) * (1 + Real.log N ^ B * meanOrder F N H B / 2) := hb
      _ ≤ CK * ((2 + |Real.log c|) * Real.log N) *
          (1 + Real.log N ^ B * meanOrder F N H B / 2) := by gcongr
      _ = CK * (2 + |Real.log c|) *
          (Real.log N * (1 + Real.log N ^ B * meanOrder F N H B / 2)) := by ring
      _ ≤ CK * (2 + |Real.log c|) * (2 * N * Real.log N ^ (-A)) := by gcongr
      _ = _ := by ring
  have hcard : ((win F N H).card : ℝ) ≤ 2 * H :=
    (Decomp103.card_win_le F hN0.le hH0.le).trans (by linarith)
  have hnorm := norm_sum_le (win F N H) (fun n =>
    (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient (Fv F n).toNat q *
      (∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
        (1 / ((q : ℝ) * meanOrder F N H B)),
        Kernel.T 0 (⌊c * N⌋₊ + 1) η ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * η))) -
      ((Fv F n : ℝ) : ℂ) * ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
        Series320.coefficient (Fv F n).toNat q)
  have hreal : |(principalMean F ⌊c * N⌋₊ N H B).re - truncatedWeightedMean F N H B| ≤
      ‖∑ n ∈ win F N H,
        ((∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient (Fv F n).toNat q *
          (∫ η in (-(1 / ((q : ℝ) * meanOrder F N H B)))..
            (1 / ((q : ℝ) * meanOrder F N H B)),
            Kernel.T 0 (⌊c * N⌋₊ + 1) η ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * η))) -
          ((Fv F n : ℝ) : ℂ) * ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
            Series320.coefficient (Fv F n).toNat q)‖ := by
    simpa only [principalMean, truncatedWeightedMean, Series320.coefficient,
      Finset.sum_sub_distrib, Complex.sub_re] using
      Complex.abs_re_le_norm (principalMean F ⌊c * N⌋₊ N H B -
        ∑ n ∈ win F N H, ((Fv F n : ℝ) : ℂ) *
          ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient (Fv F n).toNat q)
  calc
    _ ≤ _ := hreal.trans hnorm
    _ ≤ ∑ _n ∈ win F N H, 2 * CK * (2 + |Real.log c|) * N * Real.log N ^ (-A) :=
      Finset.sum_le_sum hpoint
    _ = ((win F N H).card : ℝ) * (2 * CK * (2 + |Real.log c|) * N * Real.log N ^ (-A)) := by simp
    _ ≤ 2 * H * (2 * CK * (2 + |Real.log c|) * N * Real.log N ^ (-A)) := by gcongr
    _ = _ := by ring

/-- Page 486 equation 27, principal energy. An elementary harmonic bound
controls the reciprocal totient sum up to the major denominator cutoff. -/
theorem sum_inv_totient_le (P : ℝ) (hP : 1 ≤ P) :
    ∑ q ∈ Icc 1 ⌊P⌋₊, (1 / (q.totient : ℝ)) ≤ 2 * (1 + Real.log P) ^ 2 := by
  have hP0 : 0 < P := by linarith
  have hfloor : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hP)
  have hfloorR : (0 : ℝ) < ⌊P⌋₊ := by exact_mod_cast (show 0 < ⌊P⌋₊ by omega)
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hsum : (∑ q ∈ Icc 1 ⌊P⌋₊, (q : ℝ)⁻¹) ≤ 1 + Real.log P := by
    have heq : (∑ q ∈ Icc 1 ⌊P⌋₊, (q : ℝ)⁻¹) = (harmonic ⌊P⌋₊ : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [heq]
    exact (harmonic_le_one_add_log _).trans
      (by linarith [Real.log_le_log hfloorR (Nat.floor_le hP0.le)])
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, (2 * (1 + Real.log P)) * (q : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hqFloor : (q : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).2
      have hqP : (q : ℝ) ≤ P := hqFloor.trans (Nat.floor_le hP0.le)
      have hr := TotientRatio320.ratio_le_log q hqpos
      have hlog := Real.log_le_log hq0 hqP
      have he : 1 / (q.totient : ℝ) = ((q : ℝ) / q.totient) * (q : ℝ)⁻¹ := by
        field_simp
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ = 2 * (1 + Real.log P) * ∑ q ∈ Icc 1 ⌊P⌋₊, (q : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (1 + Real.log P) * (1 + Real.log P) := by gcongr
    _ = _ := by ring

/-- Page 486 equation 27. The squared principal kernel mass on all
enclosing intervals, using the paper's residue representatives. -/
def principalMass (M : ℕ) (P Q : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
    ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
      ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Kernel.T 0 (M + 1) η‖ ^ 2

/-- Page 486 equation 27. The principal mass is bounded by the full
period geometric energy and the reciprocal totient sum. -/
theorem principalMass_le (M : ℕ) (P Q : ℝ) (hP : 1 ≤ P) (hQ : 2 ≤ Q) :
    principalMass M P Q ≤ 4 * (M + 1 : ℝ) * (1 + Real.log P) ^ 2 := by
  have hQ0 : 0 < Q := by linarith
  unfold principalMass
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, (2 * (M + 1 : ℝ)) * (1 / (q.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos := (Finset.mem_Icc.mp hq).1
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
      have hq0 : (0 : ℝ) < q := by linarith
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
      let d := 1 / ((q : ℝ) * Q)
      have hd : 0 < d := by dsimp [d]; positivity
      have hhalf : d ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        nlinarith
      let v : ℂ := (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)
      have hv : ‖v‖ ≤ 1 / (q.totient : ℝ) := by
        dsimp [v]
        rw [norm_div, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ hφ.le
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have henergy : (∫ η in Set.Icc (-d) d, ‖Kernel.T 0 (M + 1) η‖ ^ 2) ≤ 2 * (M + 1 : ℝ) := by
        have ht : Continuous (fun η : ℝ => ‖Kernel.T 0 (M + 1) η‖ ^ 2) := by
          unfold Kernel.T Kernel.e
          fun_prop
        calc
          _ ≤ ∫ η in Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ), ‖Kernel.T 0 (M + 1) η‖ ^ 2 :=
            setIntegral_mono_set ht.integrableOn_Icc
              (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
              (Filter.Eventually.of_forall (by intro η hη; constructor <;> linarith [hη.1, hη.2]))
          _ = ∫ η in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ‖Kernel.T 0 (M + 1) η‖ ^ 2 := by
            rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
          _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using Kernel.integral_norm_T_sq_le_two_mul 0 (M + 1)
      have hreps := sum_reduced_range_eq_Icc q hqpos
        (fun _ => ∫ η in Set.Icc (-d) d, ‖v * Kernel.T 0 (M + 1) η‖ ^ 2) rfl
      change (∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∫ η in Set.Icc (-d) d, ‖v * Kernel.T 0 (M + 1) η‖ ^ 2) ≤ _
      rw [← hreps]
      have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
        simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      simp_rw [norm_mul, mul_pow]
      rw [integral_const_mul]
      calc
        _ ≤ (q.totient : ℝ) * ((1 / (q.totient : ℝ)) ^ 2 * (2 * (M + 1 : ℝ))) := by gcongr
        _ = _ := by field_simp
    _ = 2 * (M + 1 : ℝ) * ∑ q ∈ Icc 1 ⌊P⌋₊, 1 / (q.totient : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (M + 1 : ℝ) * (2 * (1 + Real.log P) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_totient_le P hP) (by positivity)
    _ = _ := by ring

/-- Page 486 equation 27. The principal kernel energy over all enclosing
arcs has size at most N log N for every fixed logarithmic cutoff exponent. -/
theorem principalMass_scaled (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N Q : ℝ, N₀ ≤ N → 2 ≤ Q →
      principalMass ⌊c * N⌋₊ (Real.log N ^ B) Q ≤ C * N * Real.log N := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1))
  let U := max 1 T
  refine ⟨4 * (c + 1) * (2 + 2 * B ^ 2), max 3 (Real.exp U), by positivity,
    le_max_left _ _, ?_⟩
  intro N Q hN hQ
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hU : U ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos U) ((le_max_right _ _).trans hN)
    simpa using hh
  have hL1 : 1 ≤ Real.log N := (le_max_left 1 T).trans hU
  have hL0 : 0 < Real.log N := by linarith
  have hP : 1 ≤ Real.log N ^ B := Real.one_le_rpow hL1 hB.le
  have hh := hT (Real.log N) ((le_max_right 1 T).trans hU)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1) 2),
    abs_of_nonneg (Real.rpow_nonneg hL0.le 1), Real.rpow_one] at hh
  have hs : (1 + Real.log (Real.log N ^ B)) ^ 2 ≤ (2 + 2 * B ^ 2) * Real.log N := by
    rw [Real.log_rpow hL0]
    have hsq := add_sq_le (a := (1 : ℝ)) (b := B * Real.log (Real.log N))
    have hh' : Real.log (Real.log N) ^ 2 ≤ Real.log N := by simpa only [Real.rpow_two, one_mul] using hh
    nlinarith [mul_le_mul_of_nonneg_left hh' (sq_nonneg B), sq_nonneg B]
  have hM : (⌊c * N⌋₊ + 1 : ℝ) ≤ (c + 1) * N := by
    have hf := Nat.floor_le (show 0 ≤ c * N by positivity)
    linarith
  calc
    _ ≤ 4 * (⌊c * N⌋₊ + 1 : ℝ) * (1 + Real.log (Real.log N ^ B)) ^ 2 :=
      principalMass_le _ _ _ hP hQ
    _ ≤ 4 * ((c + 1) * N) * ((2 + 2 * B ^ 2) * Real.log N) := by gcongr
    _ = _ := by ring

/-- Page 486 equation 27. Cauchy Schwarz over a finite collection of arcs
uses the total principal mass and the total squared remainder mass. -/
theorem sum_integral_square_remainder_bound {ι : Type*} (s : Finset ι)
    (u v z : ι → ℝ → ℂ) (a b : ι → ℝ)
    (hu : ∀ i ∈ s, Continuous (u i)) (hv : ∀ i ∈ s, Continuous (v i))
    (hz : ∀ i ∈ s, Continuous (z i)) (k : ℝ) (hk : 0 ≤ k)
    (hbound : ∀ i ∈ s, ∀ x ∈ Set.Icc (a i) (b i), ‖z i x‖ ≤ k) :
    ‖∑ i ∈ s, ∫ x in Set.Icc (a i) (b i), (u i x ^ 2 - v i x ^ 2) * z i x‖ ≤
      k * ((∑ i ∈ s, ∫ x in Set.Icc (a i) (b i), ‖u i x - v i x‖ ^ 2) +
        2 * Real.sqrt ((∑ i ∈ s, ∫ x in Set.Icc (a i) (b i), ‖v i x‖ ^ 2) *
          (∑ i ∈ s, ∫ x in Set.Icc (a i) (b i), ‖u i x - v i x‖ ^ 2))) := by
  let U := fun i => ∫ x in Set.Icc (a i) (b i), ‖v i x‖ ^ 2
  let R := fun i => ∫ x in Set.Icc (a i) (b i), ‖u i x - v i x‖ ^ 2
  have hU (i : ι) : 0 ≤ U i := integral_nonneg (fun _ => sq_nonneg _)
  have hR (i : ι) : 0 ≤ R i := integral_nonneg (fun _ => sq_nonneg _)
  have hcs := Real.sum_sqrt_mul_sqrt_le s hU hR
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hU i))] at hcs
  have hpt : ∀ i ∈ s,
      ‖∫ x in Set.Icc (a i) (b i), (u i x ^ 2 - v i x ^ 2) * z i x‖ ≤
        k * (R i + 2 * (Real.sqrt (U i) * Real.sqrt (R i))) := by
    intro i hi
    rw [← Real.sqrt_mul (hU i)]
    exact integral_square_remainder_bound (u i) (v i) (z i)
      (hu i hi) (hv i hi) (hz i hi) (a i) (b i) k hk (hbound i hi)
  calc
    _ ≤ ∑ i ∈ s, ‖∫ x in Set.Icc (a i) (b i), (u i x ^ 2 - v i x ^ 2) * z i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, k * (R i + 2 * (Real.sqrt (U i) * Real.sqrt (R i))) := Finset.sum_le_sum hpt
    _ = k * ((∑ i ∈ s, R i) + 2 * ∑ i ∈ s, Real.sqrt (U i) * Real.sqrt (R i)) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
    _ ≤ _ := by gcongr

/-- Page 480 prime sum. The finite prime sum has period one. -/
theorem primeSum_periodic (M : ℕ) : Function.Periodic (primeSum M) 1 := by
  intro x
  unfold primeSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [show Kernel.e ((n : ℝ) * (x + 1)) = Kernel.e ((n : ℝ) * x) by
    simpa using ArcModel320.e_int_mul_add_one (n : ℤ) x]

/-- Page 480 polynomial kernel. Its integer frequencies give period one. -/
theorem polynomialKernel_periodic (F : ℤ[X]) (N H : ℝ) :
    Function.Periodic (Section2.polynomialKernel F N H) 1 := by
  intro x
  unfold Section2.polynomialKernel
  apply Finset.sum_congr rfl
  intro n hn
  exact ArcModel320.e_int_mul_add_one (Fv F n) x

/-- Page 486 equation 27. Inserting the principal kernel and applying
Cauchy Schwarz costs only the total principal and remainder masses. -/
theorem principal_remainder (F : ℤ[X]) (M : ℕ) (c N H B : ℝ)
    (hM : M = ⌊c * N⌋₊) (hN : 0 ≤ N) (hH : 1 ≤ H)
    (hP : 1 ≤ Real.log N ^ B)
    (hsep : 2 * (Real.log N ^ B) ^ 2 < meanOrder F N H B)
    (hcut : ∀ n ∈ win F N H, 0 ≤ Fv F n) :
    |majorPrimeMean F M N H B - (principalMean F M N H B).re| ≤
      2 * H * (remainderMass F c N H B +
        2 * Real.sqrt (principalMass M (Real.log N ^ B) (meanOrder F N H B) *
          remainderMass F c N H B)) := by
  let P := Real.log N ^ B
  let Q := meanOrder F N H B
  let idx := (Icc 1 ⌊P⌋₊).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))
  let d := fun i : (Σ _ : ℕ, ℕ) => 1 / ((i.1 : ℝ) * Q)
  let u := fun (i : (Σ _ : ℕ, ℕ)) (η : ℝ) => primeSum M ((i.2 : ℝ) / i.1 + η)
  let v := fun (i : (Σ _ : ℕ, ℕ)) (η : ℝ) =>
    ((ArithmeticFunction.moebius i.1 : ℂ) / (i.1.totient : ℂ)) * Kernel.T 0 (M + 1) η
  let z := fun (i : (Σ _ : ℕ, ℕ)) (η : ℝ) =>
    Section2.polynomialKernel F N H (-((i.2 : ℝ) / i.1 + η))
  have hQ0 : 0 < Q := by dsimp [Q]; nlinarith [sq_nonneg (Real.log N ^ B)]
  have hδ (i : (Σ _ : ℕ, ℕ)) (hi : i ∈ idx) : 0 < d i := by
    have hq := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hi).1).1
    have hqr : (0 : ℝ) < i.1 := by exact_mod_cast hq
    dsimp [d]
    positivity
  have hu (i : (Σ _ : ℕ, ℕ)) : Continuous (u i) := by dsimp [u, primeSum, Kernel.e]; fun_prop
  have hv (i : (Σ _ : ℕ, ℕ)) : Continuous (v i) := by dsimp [v, Kernel.T, Kernel.e]; fun_prop
  have hz (i : (Σ _ : ℕ, ℕ)) : Continuous (z i) := by
    dsimp [z, Section2.polynomialKernel, Kernel.e]
    fun_prop
  let f := fun α : ℝ => primeSum M α ^ 2 * Section2.polynomialKernel F N H (-α)
  have hf : Continuous f := by dsimp [f, primeSum, Section2.polynomialKernel, Kernel.e]; fun_prop
  have hper : Function.Periodic f 1 := by
    intro α
    have hker : Section2.polynomialKernel F N H (-(α + 1)) =
        Section2.polynomialKernel F N H (-α) := by
      convert (polynomialKernel_periodic F N H (-α - 1)).symm using 1 <;> congr 1 <;> ring
    dsimp [f]
    rw [primeSum_periodic M α, hker]
  have hS : (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α) =
      ∑ i ∈ idx, ∫ η in Set.Icc (-d i) (d i), u i η ^ 2 * z i η := by
    rw [mean_arc_integral_split F N H B hP hsep f hf hper, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    have hd : 0 < d ⟨q, a⟩ := hδ _ (Finset.mem_sigma.mpr ⟨hq, ha⟩)
    rw [intervalIntegral.integral_of_le (by linarith : -d ⟨q, a⟩ ≤ d ⟨q, a⟩),
      ← integral_Icc_eq_integral_Ioc]
  have hV : principalMean F M N H B =
      ∑ i ∈ idx, ∫ η in Set.Icc (-d i) (d i), v i η ^ 2 * z i η := by
    rw [← principal_integral_eq F M N H B hcut, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    have hd : 0 < d ⟨q, a⟩ := hδ _ (Finset.mem_sigma.mpr ⟨hq, ha⟩)
    rw [intervalIntegral.integral_of_le (by linarith : -d ⟨q, a⟩ ≤ d ⟨q, a⟩),
      ← integral_Icc_eq_integral_Ioc]
  have heq : (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α) - principalMean F M N H B =
      ∑ i ∈ idx, ∫ η in Set.Icc (-d i) (d i), (u i η ^ 2 - v i η ^ 2) * z i η := by
    rw [hS, hV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : IntegrableOn (fun η => u i η ^ 2 * z i η) (Set.Icc (-d i) (d i)) := by
      apply Continuous.integrableOn_Icc
      fun_prop
    have hi2 : IntegrableOn (fun η => v i η ^ 2 * z i η) (Set.Icc (-d i) (d i)) := by
      apply Continuous.integrableOn_Icc
      fun_prop
    rw [← integral_sub hi1 hi2]
    apply setIntegral_congr_fun measurableSet_Icc
    intro η hη
    ring
  have hR : (∑ i ∈ idx, ∫ η in Set.Icc (-d i) (d i), ‖u i η - v i η‖ ^ 2) =
      remainderMass F c N H B := by
    rw [Finset.sum_sigma]
    unfold remainderMass
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos := (Finset.mem_Icc.mp hq).1
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hrem (a : ℕ) (η : ℝ) : u ⟨q, a⟩ η - v ⟨q, a⟩ η = characterRemainder M q (a : ℤ) η := by
      dsimp [u, v, characterRemainder]
      push_cast <;> rfl
    simp_rw [hrem]
    rw [← hM]
    apply sum_reduced_range_eq_Icc q hqpos
    apply setIntegral_congr_fun measurableSet_Icc
    intro η hη
    simp only [characterRemainder, Nat.cast_zero, Int.cast_zero, Int.cast_natCast,
      zero_div, zero_add, div_self hqne]
    have he : primeSum M (1 + η) = primeSum M η := by simpa only [add_comm] using primeSum_periodic M η
    rw [he]
  have hU : (∑ i ∈ idx, ∫ η in Set.Icc (-d i) (d i), ‖v i η‖ ^ 2) = principalMass M P Q := by
    rw [Finset.sum_sigma]
    unfold principalMass
    apply Finset.sum_congr rfl
    intro q hq
    exact sum_reduced_range_eq_Icc q (Finset.mem_Icc.mp hq).1
      (fun _ => ∫ η in Set.Icc (-(1 / ((q : ℝ) * Q))) (1 / ((q : ℝ) * Q)),
        ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * Kernel.T 0 (M + 1) η‖ ^ 2) rfl
  have hb := sum_integral_square_remainder_bound idx u v z (fun i => -d i) d
    (fun i _ => hu i) (fun i _ => hv i) (fun i _ => hz i) (2 * H) (by positivity)
    (by
      intro i hi η hη
      dsimp [z]
      exact (Decomp400d.norm_polynomialKernel_le F N H _ hN (by linarith)).trans (by linarith))
  rw [hR, hU] at hb
  change |(∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α).re - (principalMean F M N H B).re| ≤ _
  rw [← Complex.sub_re, heq]
  exact (Complex.abs_re_le_norm _).trans hb

/-- Page 486 equation 27. The exact principal comparison follows from
kernel insertion, two applications of Cauchy Schwarz and endpoint completion. -/
theorem principal_mean (F : ℤ[X]) (hF : Admissible F)
    (A ε B c : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      |majorPrimeMean F ⌊c * N⌋₊ N H B - truncatedWeightedMean F N H B| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) := by
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := principal_completion F hF A ε B c hA hε hB hc
  obtain ⟨CM, NM, hCM, hNM, hm⟩ := principalMass_scaled c B hc hB
  obtain ⟨NS, hNS, hs⟩ := meanOrder_separated F hF ε B hε hB
  obtain ⟨NQ, hNQ, hq⟩ := meanOrder_eventually F hF ε B 2 hε
  let N₀ := max (max NP NM) (max NS NQ)
  let C := CP + (2 + 4 * Real.sqrt CM)
  refine ⟨C, N₀, by dsimp [C]; positivity,
    hNP.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' : NP ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNM' : NM ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNS' : NS ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNQ' : NQ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 3 ≤ N := hNP.trans hNP'
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨hP, hsep⟩ := hs N H hNS' hH
  have hQ2 := hq N H hNQ' hH
  have hM := hm N (meanOrder F N H B) hNM' hQ2
  have hR := remainderMass_nonneg F c N H B
  have hr := principal_remainder F ⌊c * N⌋₊ c N H B rfl hN0 hH1 hP hsep
    (fun n hn => (hcut n hn).1)
  have hp' := hp N H hNP' hH hHu hcut
  have hroot : Real.sqrt (principalMass ⌊c * N⌋₊ (Real.log N ^ B)
        (meanOrder F N H B) * remainderMass F c N H B) ≤
      Real.sqrt CM * Real.sqrt (N * Real.log N * remainderMass F c N H B) := by
    calc
      _ ≤ Real.sqrt ((CM * N * Real.log N) * remainderMass F c N H B) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hM hR)
      _ = _ := by rw [mul_assoc CM N, mul_assoc CM (N * Real.log N), Real.sqrt_mul hCM.le]
  have hsmall : 0 ≤ H * N * Real.log N ^ (-A) := by positivity
  have hnon : 0 ≤ H * (remainderMass F c N H B +
      Real.sqrt (N * Real.log N * remainderMass F c N H B)) := by positivity
  calc
    _ ≤ |majorPrimeMean F ⌊c * N⌋₊ N H B - (principalMean F ⌊c * N⌋₊ N H B).re| +
        |(principalMean F ⌊c * N⌋₊ N H B).re - truncatedWeightedMean F N H B| := abs_sub_le _ _ _
    _ ≤ 2 * H * (remainderMass F c N H B +
        2 * Real.sqrt (principalMass ⌊c * N⌋₊ (Real.log N ^ B) (meanOrder F N H B) *
          remainderMass F c N H B)) + CP * H * N * Real.log N ^ (-A) := add_le_add hr hp'
    _ ≤ (2 + 4 * Real.sqrt CM) * H * (remainderMass F c N H B +
        Real.sqrt (N * Real.log N * remainderMass F c N H B)) + CP * H * N * Real.log N ^ (-A) := by
      nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hroot),
        mul_nonneg (mul_nonneg hH0 hR) (Real.sqrt_nonneg CM),
        mul_nonneg hH0 (Real.sqrt_nonneg (N * Real.log N * remainderMass F c N H B))]
    _ ≤ _ := by
      dsimp [C]
      nlinarith [mul_nonneg hCP.le hnon,
        mul_nonneg (show 0 ≤ 2 + 4 * Real.sqrt CM by positivity) hsmall]

/-- LEAF. Page 487 equation 28, by the polynomial divisor mean used on page 481
between equations 3 and 4. Only the arithmetic divisor weight is averaged here.
This is the shorter Theorem 2 interval. The general polynomial reduction
beyond the hypotheses of Nair 1992 remains OPEN. -/
theorem leaf_divisor_mean (F : ℤ[X]) (hF : Admissible F) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      ∑ n ∈ win F N H,
        ((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
          (Fv F n).toNat.totient ≤ C * H * Real.log N ^ d := by
  sorry

/-- Page 487 equation 28. The weighted finite singular series is bounded
by the pointwise Ramanujan tail and the sum of its divisor weights. -/
theorem weighted_tail (F : ℤ[X]) (N H P c K : ℝ)
    (hP : 1 ≤ P) (hc : 0 ≤ c) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hcut : ∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n : ℝ) ≤ c * N)
    (hpos : ∀ n ∈ win F N H, 0 < (Fv F n).toNat)
    (htail : ∀ m : ℕ, 0 < m →
      ‖(Sing m : ℂ) - ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient m q‖ ≤
        K * ((m : ℝ) * m.divisors.card / m.totient) / P) :
    |(∑ n ∈ win F N H, ((Fv F n : ℝ) : ℂ) *
        ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient (Fv F n).toNat q).re -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
      c * N * (K / P) * ∑ n ∈ win F N H,
        ((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
          (Fv F n).toNat.totient := by
  let v := fun n => (Fv F n : ℝ)
  let t := fun n => ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient (Fv F n).toNat q
  have heq : (∑ n ∈ win F N H, ((Fv F n : ℝ) : ℂ) *
        ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient (Fv F n).toNat q).re -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat =
      (∑ n ∈ win F N H, (v n : ℂ) * (t n - (Sing (Fv F n).toNat : ℂ))).re := by
    simp [v, t, mul_sub, Finset.sum_sub_distrib, Complex.mul_re]
  rw [heq]
  calc
    _ ≤ ‖∑ n ∈ win F N H, (v n : ℂ) * (t n - (Sing (Fv F n).toNat : ℂ))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ n ∈ win F N H, ‖(v n : ℂ) * (t n - (Sing (Fv F n).toNat : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ win F N H, c * N * (K / P) *
        (((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
          (Fv F n).toNat.totient) := by
      apply Finset.sum_le_sum
      intro n hn
      have hv : 0 ≤ v n := by
        dsimp [v]
        exact_mod_cast (hcut n hn).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
      have ht : ‖t n - (Sing (Fv F n).toNat : ℂ)‖ ≤
          K * (((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
            (Fv F n).toNat.totient) / P := by
        rw [norm_sub_rev]
        exact htail _ (hpos n hn)
      calc
        _ ≤ (c * N) * (K * (((Fv F n).toNat : ℝ) *
            (Fv F n).toNat.divisors.card / (Fv F n).toNat.totient) / P) :=
          mul_le_mul (hcut n hn).2 ht (norm_nonneg _) (mul_nonneg hc hN)
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Page 487 equation 28. Assemble the weighted Ramanujan tail from
its proved arithmetic tail and the shorter polynomial divisor mean.
CONDITIONAL ON leaf_divisor_mean. -/
theorem singular_tail (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |truncatedWeightedMean F N H B -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
          C * H * N * Real.log N ^ (-A) := by
  obtain ⟨d, hd, hmean⟩ := leaf_divisor_mean F hF
  obtain ⟨CM, NM, hCM, hNM, hm⟩ := hmean ε hε
  obtain ⟨c, NC, hc, hNC, hcut⟩ := Decomp88.leaf_cutoff F hF
  obtain ⟨NP, hNP, hpos⟩ := Decomp320a.window_pos F hF
  obtain ⟨K, hK, htail⟩ := Series320.partial_tail
  refine ⟨A + d + 1, by positivity, ?_⟩
  intro B hB
  let N₀ := max (max NM NC) (max NP (Real.exp 1))
  refine ⟨c * K * CM, N₀, by positivity,
    hNM.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu
  have hNM' : NM ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNC' : NC ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 3 ≤ N := hNM.trans hNM'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL : 0 < Real.log N := by linarith
  have hP : 1 ≤ Real.log N ^ B :=
    Real.one_le_rpow hL1 (by linarith)
  have hH0 : 0 ≤ H := (Real.rpow_nonneg hN0.le _).trans hH
  have hHu' : H ≤ N ^ (1 / (F.natDegree : ℝ)) :=
    hHu.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hcut' := hcut N H hNC' hH0 hHu'
  have hcutR : ∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n : ℝ) ≤ c * N := by
    intro n hn
    refine ⟨(hcut' n hn).1, ?_⟩
    have hcast : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (hcut' n hn).1
    rw [← hcast]
    have hh : ((Fv F n).toNat : ℝ) ≤ (⌊c * N⌋₊ : ℝ) := by exact_mod_cast (hcut' n hn).2
    exact hh.trans (Nat.floor_le (by positivity))
  have hw := weighted_tail F N H (Real.log N ^ B) c K hP hc.le hN0.le hK.le
    hcutR (hpos N H hNP') (fun m hm => htail m hm _ hP)
  change |truncatedWeightedMean F N H B - _| ≤ _ at hw
  calc
    _ ≤ c * N * (K / Real.log N ^ B) * ∑ n ∈ win F N H,
        ((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
          (Fv F n).toNat.totient := hw
    _ ≤ c * N * (K / Real.log N ^ B) * (CM * H * Real.log N ^ d) := by
      exact mul_le_mul_of_nonneg_left (hm N H hNM' hH hHu) (by positivity)
    _ = (c * K * CM) * H * N * Real.log N ^ (d - B) := by
      rw [Real.rpow_sub hL]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
      positivity

end
end LeanLab.Perelli1996.Decomp533a
