/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
The major arcs of page 5 as a disjoint union: distinct reduced fractions with
denominators at most P are at least 1/P² apart, so narrow arcs are pairwise disjoint and
the integral over the major arcs is the sum of the integrals over the single arcs.
Summing display 2.5 over the arcs gives the comparison of the major arc integral with
the principal model of display 2.6, with an explicit error.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512MajorArc

namespace LeanLab.BHP1997.Route512Major
open Classical Complex MeasureTheory Set

/-- P0069 page 5: two arcs centered at distinct reduced fractions `r/q` and `r'/q'` with
`q, q' ≤ P` are disjoint as soon as every half width `h q` is below `1/(2P²)`. -/
theorem arcs_separated512j (P : ℕ) (h : ℕ → ℝ)
    (hsmall : ∀ q ∈ Finset.Icc 1 P, 2 * h q * (P : ℝ) ^ 2 < 1)
    {q q' r r' : ℕ} (hq : q ∈ Finset.Icc 1 P) (hq' : q' ∈ Finset.Icc 1 P)
    (hr : Nat.Coprime r q) (hr' : Nat.Coprime r' q') (hne : q ≠ q' ∨ r ≠ r') :
    Disjoint (Icc ((r : ℝ) / q - h q) ((r : ℝ) / q + h q))
      (Icc ((r' : ℝ) / q' - h q') ((r' : ℝ) / q' + h q')) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  have hq1 := Finset.mem_Icc.mp hq
  have hq1' := Finset.mem_Icc.mp hq'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1.1
  have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'.1
  have hqP : (q : ℝ) ≤ P := by exact_mod_cast hq1.2
  have hqP' : (q' : ℝ) ≤ P := by exact_mod_cast hq1'.2
  have hint : (r : ℤ) * q' - r' * q ≠ 0 := by
    intro h0
    have heq : r * q' = r' * q := by
      have h3 : (r : ℤ) * q' = r' * q := sub_eq_zero.mp h0
      exact_mod_cast h3
    have hd1 : q ∣ q' :=
      Nat.Coprime.dvd_of_dvd_mul_left hr.symm (Dvd.intro_left r' heq.symm)
    have hd2 : q' ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left hr'.symm (Dvd.intro_left r heq)
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst hqq
    have hrr : r = r' := Nat.eq_of_mul_eq_mul_right hq1.1 heq
    rcases hne with h | h
    · exact h rfl
    · exact h hrr
  have habs : (1 : ℝ) ≤ |(r : ℝ) * q' - r' * q| := by
    have h3 := Int.one_le_abs hint
    exact_mod_cast h3
  have h1 : |(r : ℝ) / q - (r' : ℝ) / q'| ≤ h q + h q' := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have h2 : (r : ℝ) / q - (r' : ℝ) / q' = ((r : ℝ) * q' - r' * q) / (q * q') := by
    field_simp
  rw [h2, abs_div, abs_of_pos (mul_pos hqpos hqpos'), div_le_iff₀ (mul_pos hqpos hqpos')] at h1
  have hs := hsmall q hq
  have hs' := hsmall q' hq'
  have hqq' : (q : ℝ) * q' ≤ (P : ℝ) ^ 2 := by nlinarith
  have hlt : (h q + h q') * ((q : ℝ) * q') < 1 := by
    by_cases hpos : 0 ≤ h q + h q'
    · calc _ ≤ (h q + h q') * (P : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hqq' hpos
        _ < 1 := by linarith
    · have h4 := mul_pos hqpos hqpos'
      nlinarith
  linarith

/-- P0069 page 5 and page 7 display 2.5: when the arcs are narrow and lie inside the
period `(lo, hi]`, the integral over the major arcs, written as in `major512`, is the sum
over `q ≤ P` and reduced `r` of the integrals over the single arcs. -/
theorem major_union_integral512j (P : ℕ) (h : ℕ → ℝ) (lo hi : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f)
    (hsmall : ∀ q ∈ Finset.Icc 1 P, 2 * h q * (P : ℝ) ^ 2 < 1)
    (hinside : ∀ q ∈ Finset.Icc 1 P,
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        lo < (r : ℝ) / q - h q ∧ (r : ℝ) / q + h q ≤ hi) :
    (∫ t in Ioc lo hi ∩ ⋃ q ∈ Finset.Icc 1 P,
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Icc ((r : ℝ) / q - h q) ((r : ℝ) / q + h q), f t) =
      ∑ q ∈ Finset.Icc 1 P, ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        ∫ t in Icc ((r : ℝ) / q - h q) ((r : ℝ) / q + h q), f t := by
  have hsub : (⋃ q ∈ Finset.Icc 1 P,
      ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Icc ((r : ℝ) / q - h q) ((r : ℝ) / q + h q)) ⊆ Ioc lo hi := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨q, hq, r, hr, ht⟩ := ht
    have h3 := hinside q hq r hr
    exact ⟨lt_of_lt_of_le h3.1 ht.1, ht.2.trans h3.2⟩
  rw [Set.inter_eq_right.mpr hsub, integral_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [integral_biUnion_finset]
    · intro r _
      exact measurableSet_Icc
    · intro r hr r' hr' hne
      exact arcs_separated512j P h hsmall hq hq (Finset.mem_filter.mp hr).2
        (Finset.mem_filter.mp hr').2 (Or.inr hne)
    · intro r _
      exact hf.integrableOn_Icc
  · intro q _
    exact Finset.measurableSet_biUnion _ (fun r _ => measurableSet_Icc)
  · intro q hq q' hq' hne
    rw [Function.onFun, Set.disjoint_iUnion₂_left]
    intro r hr
    rw [Set.disjoint_iUnion₂_right]
    intro r' hr'
    exact arcs_separated512j P h hsmall hq hq' (Finset.mem_filter.mp hr).2
      (Finset.mem_filter.mp hr').2 (Or.inl hne)
  · intro q _
    exact integrableOn_finset_iUnion.mpr fun r _ => hf.integrableOn_Icc

/-- P0069 page 7 displays 2.5 and 2.6, all arcs: when the arcs with denominators at most
`P` are narrow and lie inside the period `(lo, hi]`, the integral of S1 S2 e(-Nt) over
the major arcs, written as in `major512`, differs from the principal model
`w₁ w₂ ∑_{q ≤ P} μ(q)²/φ(q)² c_q(-N) ∫_{-h(q)}^{h(q)}`, the body of `principalArc512`, by
at most the sum over the arcs of the arc length times the pointwise replacement error.
The hypotheses are those of Theorem 2 at a fixed `x`: the coprimality support of `a`,
the prefix sum bounds `M₁` and `M₂` for all characters of moduli at most `P`, and a
trivial bound `V` for the sum of `‖b‖`. -/
theorem major_total512j (P : ℕ) (h : ℕ → ℝ) (lo hi : ℝ) (loI hiI loJ hiJ : ℕ)
    (a b : ℕ → ℂ) (w₁ w₂ : ℂ) (M₁ M₂ V T₁ T₂ : ℝ) (N : ℕ)
    (hT₁ : (hiI : ℝ) ≤ T₁) (hT₂ : (hiJ : ℝ) ≤ T₂)
    (hh : ∀ q ∈ Finset.Icc 1 P, 0 ≤ h q)
    (hsmall : ∀ q ∈ Finset.Icc 1 P, 2 * h q * (P : ℝ) ^ 2 < 1)
    (hinside : ∀ q ∈ Finset.Icc 1 P,
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        lo < (r : ℝ) / q - h q ∧ (r : ℝ) / q + h q ≤ hi)
    (hsupp : ∀ q ∈ Finset.Icc 1 P, ∀ k ∈ Finset.Ioc loI hiI, a k ≠ 0 → Nat.Coprime k q)
    (h1 : ∀ q ∈ Finset.Icc 1 P, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ T₁ →
      ‖∑ k ∈ (Finset.Ioc loI hiI).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - Thm2.delta χ * w₁)‖ ≤ M₁)
    (h4 : ∀ n ∈ Finset.Icc 1 P, ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T₂ →
      ‖∑ m ∈ (Finset.Ioc loJ hiJ).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b m * χ (m : ZMod n) - Thm2.delta χ * w₂)‖ ≤ M₂)
    (hV : ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖ ≤ V) :
    ‖(∫ t in Ioc lo hi ∩ ⋃ q ∈ Finset.Icc 1 P,
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Icc ((r : ℝ) / q - h q) ((r : ℝ) / q + h q),
        (∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
      w₁ * w₂ * ∑ q ∈ Finset.Icc 1 P,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          ∫ η in (-h q)..(h q),
            (∑ k ∈ Finset.Ioc loI hiI, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc loJ hiJ, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ))‖ ≤
      ∑ q ∈ Finset.Icc 1 P,
        (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) *
          (2 * h q *
            (Real.sqrt q * ((1 + 2 * Real.pi * h q * ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
              ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
                (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
                  ((1 + 2 * Real.pi * h q * ((hiJ - loJ : ℕ) : ℝ)) * M₂)))) := by
  have hpoly : ∀ (S : Finset ℕ) (c : ℕ → ℂ), Continuous (fun t : ℝ =>
      ∑ k ∈ S, c k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) := fun S c =>
    continuous_finsetSum S fun k _ => continuous_const.mul
      ((map_continuous (fourier (T := (1 : ℝ)) (k : ℤ))).comp (AddCircle.continuous_mk' 1))
  have he : Continuous (fun t : ℝ => @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    (map_continuous (fourier (T := (1 : ℝ)) (-(N : ℤ)))).comp (AddCircle.continuous_mk' 1)
  have hF : Continuous (fun t : ℝ =>
      (∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    ((hpoly _ a).mul (hpoly _ b)).mul he
  have hmodel : w₁ * w₂ * ∑ q ∈ Finset.Icc 1 P,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          ∫ η in (-h q)..(h q),
            (∑ k ∈ Finset.Ioc loI hiI, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc loJ hiJ, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ)) =
      ∑ q ∈ Finset.Icc 1 P, ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * (w₁ * w₂) *
          @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) *
          ∫ η in (-h q)..(h q),
            (∑ k ∈ Finset.Ioc loI hiI, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc loJ hiJ, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [major_union_integral512j P h lo hi _ hF hsmall hinside, hmodel, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have hq1 := Finset.mem_Icc.mp hq
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro r hr
  exact major_arc512j loI hiI loJ hiJ a b r (Finset.mem_filter.mp hr).2 w₁ w₂ M₁ M₂ V T₁ T₂
    (h q) N hT₁ hT₂ (hh q hq) (hsupp q hq) (h1 q hq)
    (fun n hn => h4 n (Finset.mem_Icc.mpr
      ⟨Nat.pos_of_ne_zero (fun h0 => hq0 (by rw [h0] at hn; exact zero_dvd_iff.mp hn)),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hn).trans hq1.2⟩)) hV

end LeanLab.BHP1997.Route512Major
