/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
Raw steps of the major arc coefficient replacement: partial summation from the
prefix sum hypothesis of Theorem 2, the character expansion of S1 at a rational
point with the Gauss sum bound, and the exact evaluation of the principal model
over one arc and over all arcs of one modulus. Every statement is written with
raw exponential sums so that Decomp512a can import this file.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Abel514
import LeanLab.BHP1997.Thm2Statement

namespace LeanLab.BHP1997.Route512Major
open Classical Complex MeasureTheory Set
open scoped ComplexConjugate

/-- P0069 page 5: every exponential e(nη) in S1 and S2 has norm one. -/
theorem fourier_norm512j (n : ℤ) (η : ℝ) :
    ‖@fourier 1 n (η : AddCircle (1 : ℝ))‖ = 1 := by
  rw [fourier_coe_apply]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (η : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * Real.pi * n * η : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma fourier_step512j (k : ℕ) (η : ℝ) :
    ‖@fourier 1 ((k + 1 : ℕ) : ℤ) (η : AddCircle (1 : ℝ)) -
      @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤ 2 * Real.pi * |η| := by
  have h1 : @fourier 1 ((k + 1 : ℕ) : ℤ) (η : AddCircle (1 : ℝ)) =
      @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) *
        @fourier 1 (1 : ℤ) (η : AddCircle (1 : ℝ)) := by
    rw [← fourier_add]
    push_cast
    rfl
  rw [h1, ← mul_sub_one, norm_mul, fourier_norm512j, one_mul, fourier_coe_apply]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (η : ℂ) / ((1 : ℝ) : ℂ)) =
      Complex.I * ((2 * Real.pi * η : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2]
  have h3 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * η)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.two_pi_pos] at h3
  exact h3

/-- P0069 page 7, the partial summation display between 2.4 and 2.5: a uniform bound `M`
for the prefix sums of the coefficients over `(lo, hi]`, in the exact shape of hypotheses
i and iv of Theorem 2 on page 3, bounds the exponential sum at `η` by
`(1 + 2π|η|(hi - lo)) M`. -/
theorem partial_summation512j (lo hi : ℕ) (c : ℕ → ℂ) (M T : ℝ) (hT : (hi : ℝ) ≤ T)
    (hc : ∀ t : ℝ, t ≤ T →
      ‖∑ k ∈ (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ t), c k‖ ≤ M) (η : ℝ) :
    ‖∑ k ∈ Finset.Ioc lo hi, c k * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
      (1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M := by
  have hs : ∀ m ∈ Finset.Ioc lo hi, lo ≤ m ∧ m ≤ hi := fun m hm =>
    ⟨(Finset.mem_Ioc.mp hm).1.le, (Finset.mem_Ioc.mp hm).2⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hc T le_rfl)
  have hall : ‖∑ m ∈ Finset.Ioc lo hi, c m‖ ≤ M := by
    have h := hc hi hT
    rwa [Finset.filter_true_of_mem] at h
    intro k hk
    exact_mod_cast (Finset.mem_Ioc.mp hk).2
  have hp : ∀ i ∈ Finset.Ico lo hi,
      ‖∑ m ∈ (Finset.Ioc lo hi).filter (fun m => m ≤ i), c m‖ ≤ M := by
    intro i hi'
    have h := hc i (le_trans (by exact_mod_cast (Finset.mem_Ico.mp hi').2.le) hT)
    have e : (Finset.Ioc lo hi).filter (fun m => m ≤ i) =
        (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ (i : ℝ)) := by
      ext m
      simp only [Finset.mem_filter, Nat.cast_le]
    rw [e]
    exact h
  have h := Decomp514Abel.weighted_sum_norm_le (Finset.Ioc lo hi) hs
    (fun k : ℕ => @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) c hall hp
  have hsum : (∑ i ∈ Finset.Ico lo hi,
      ‖@fourier 1 ((i + 1 : ℕ) : ℤ) (η : AddCircle (1 : ℝ)) -
        @fourier 1 (i : ℤ) (η : AddCircle (1 : ℝ))‖) ≤
      ((hi - lo : ℕ) : ℝ) * (2 * Real.pi * |η|) := by
    calc
      _ ≤ ∑ _i ∈ Finset.Ico lo hi, 2 * Real.pi * |η| :=
        Finset.sum_le_sum fun i _ => fourier_step512j i η
      _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  calc
    _ = ‖∑ m ∈ Finset.Ioc lo hi,
        (fun k : ℕ => @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) m * c m‖ := by
      congr 1
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ ≤ _ := h
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hM
      have h1 := fourier_norm512j (hi : ℤ) η
      simp only [h1]
      linarith

/-- P0069 page 6 display 2.1: discrete Parseval for the Gauss transforms, raw copy. -/
theorem gauss_parseval512j {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ t : ZMod q, ‖∑ r : ZMod q, f r * ZMod.stdAddChar (r * t)‖ ^ 2 =
      (q : ℝ) * ∑ r : ZMod q, ‖f r‖ ^ 2 := by
  let e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hexp (t : ZMod q) :
      (‖∑ r : ZMod q, f r * e (r * t)‖ ^ 2 : ℂ) =
        ∑ r : ZMod q, ∑ s : ZMod q, (conj (f r) * f s) * e ((s - r) * t) := by
    rw [← Complex.conj_mul']
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      ← AddChar.map_neg_eq_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    calc
      _ = (conj (f r) * f s) * (e (-(r * t)) * e (s * t)) := by ring
      _ = _ := by
        rw [← e.map_add_eq_mul]
        congr 2
        ring
  apply Complex.ofReal_injective
  push_cast
  change (∑ t : ZMod q, (‖∑ r : ZMod q, f r * e (r * t)‖ ^ 2 : ℂ)) =
    (q : ℂ) * ∑ r : ZMod q, (‖f r‖ ^ 2 : ℂ)
  have he : e.IsPrimitive := ZMod.isPrimitive_stdAddChar q
  calc
    _ = ∑ r : ZMod q, ∑ s : ZMod q,
        (conj (f r) * f s) * ∑ t : ZMod q, e (t * (s - r)) := by
      simp_rw [hexp]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [mul_comm t]
    _ = _ := by
      simp only [AddChar.sum_mulShift _ he, sub_eq_zero]
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Complex.conj_mul']
      ring

/-- P0069 page 6 display 2.1: the Gauss sum norm bound for every modulus. -/
theorem gauss_norm512j {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt (q : ℝ) := by
  let e : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun t => ∑ r : ZMod q, χ r * e (r * t)
  let S : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hS : 0 < (S.card : ℝ) := by
    have hmem : (1 : ZMod q) ∈ S := by simp [S]
    exact_mod_cast Finset.card_pos.mpr ⟨1, hmem⟩
  have hnorm (t : ZMod q) (ht : IsUnit t) : ‖G t‖ = ‖gaussSum χ e‖ := by
    have h := gaussSum_mulShift_eq χ e ht.unit
    have heq : G t = gaussSum χ (e.mulShift ht.unit) := by
      simp only [G, gaussSum, AddChar.mulShift_apply, ht.unit_spec, mul_comm]
    rw [heq, h, norm_mul, (χ⁻¹).unit_norm_eq_one ht.unit, one_mul]
  have hcoef : ∑ r : ZMod q, ‖χ r‖ ^ 2 = (S.card : ℝ) := by
    have hp (r : ZMod q) : ‖χ r‖ ^ 2 = if IsUnit r then 1 else 0 := by
      by_cases hr : IsUnit r
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hr), ← hr.unit_spec, χ.unit_norm_eq_one]
        norm_num
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hr), χ.map_nonunit hr, norm_zero, zero_pow (by decide)]
    simp_rw [hp]
    simp [S, Finset.sum_boole]
  have hlow : (S.card : ℝ) * ‖gaussSum χ e‖ ^ 2 ≤ ∑ t : ZMod q, ‖G t‖ ^ 2 := by
    calc
      _ = ∑ t ∈ S, ‖G t‖ ^ 2 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro t ht
        rw [hnorm t (Finset.mem_filter.mp ht).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun t ht hnot => sq_nonneg _)
  have hparse := gauss_parseval512j (q := q) χ
  change (∑ t : ZMod q, ‖G t‖ ^ 2) = (q : ℝ) * ∑ r : ZMod q, ‖χ r‖ ^ 2 at hparse
  rw [hcoef] at hparse
  have hsq : ‖gaussSum χ e‖ ^ 2 ≤ (q : ℝ) := by
    apply (mul_le_mul_iff_left₀ hS).mp
    nlinarith [hlow]
  exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg q)).mpr hsq

/-- P0069 page 6 display 2.4: finite character inversion for an arbitrary unit. -/
theorem gauss_inversion512j {q : ℕ} [NeZero q] (e : AddChar (ZMod q) ℂ)
    (k : ZMod q) (hk : IsUnit k) :
    (∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ e * χ k) = (q.totient : ℂ) * e k := by
  have hinv (χ : DirichletCharacter ℂ q) : χ⁻¹ k = χ k⁻¹ := by
    rw [MulChar.inv_apply_eq_inv']
    have hmul : χ k⁻¹ * χ k = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit k hk, map_one]
    exact (eq_inv_of_mul_eq_one_left hmul).symm
  have horth (r : ZMod q) :
      (∑ χ : DirichletCharacter ℂ q, χ⁻¹ r * χ k) = if r = k then (q.totient : ℂ) else 0 := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, χ r * χ⁻¹ k := by
        exact Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ q)) _ _ (fun χ => by simp)
      _ = ∑ χ : DirichletCharacter ℂ q, χ k⁻¹ * χ r := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hinv]
        ring
      _ = _ := by
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hk r]
        simp only [eq_comm]
  calc
    _ = ∑ r : ZMod q, e r * ∑ χ : DirichletCharacter ℂ q, χ⁻¹ r * χ k := by
      simp only [gaussSum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = _ := by
      simp only [horth, mul_ite, mul_zero]
      simp [mul_comm]

/-- P0069 pages 5 and 6: split a rational shift from each integer frequency. -/
theorem fourier_rational_shift512j {q : ℕ} [NeZero q] (k : ℕ) (r : ℤ) (t : ℝ) :
    @fourier 1 (k : ℤ) (((r : ℝ) / q + t : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar (((k : ℤ) * r : ℤ) : ZMod q) *
        @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, ZMod.stdAddChar_coe]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast, Complex.ofReal_one, Int.cast_mul, Int.cast_natCast, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- P0069 page 6 display 2.4, first two equalities, raw form: the exact character
expansion of S1 at `r/q + η` when the coefficients are supported on units modulo `q`. -/
theorem shifted_character_expansion512j (S : Finset ℕ) (a : ℕ → ℂ)
    {q : ℕ} [NeZero q] (r : ℤ) (hr : IsUnit (r : ZMod q)) (η : ℝ)
    (hsupp : ∀ k ∈ S, a k ≠ 0 → IsUnit (k : ZMod q)) :
    (∑ k ∈ S, a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          ∑ k ∈ S, a k * χ (k : ZMod q) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  apply (mul_left_cancel₀ hφ)
  rw [← mul_assoc, mul_inv_cancel₀ hφ, one_mul, Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ha : a k = 0
  · simp [ha]
  have hunit := (hsupp k hk ha).mul hr
  have hg := gauss_inversion512j ZMod.stdAddChar ((k : ZMod q) * (r : ZMod q)) hunit
  rw [fourier_rational_shift512j]
  calc
    _ = (a k * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
        ((q.totient : ℂ) * ZMod.stdAddChar ((k : ZMod q) * (r : ZMod q))) := by
      push_cast
      ring
    _ = _ := by
      rw [← hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [map_mul]
      ring

/-- P0069 page 6 display 2.4: for coefficients supported on units modulo `q` whose
twisted prefix sums obey the bound `M` of hypothesis i of Theorem 2 for every character,
S1 at `r/q + η` differs from the principal model, the Gauss sum of the principal
character over `φ(q)` times `w` times the unweighted exponential sum, by at most
`√q (1 + 2π|η|(hi - lo)) M`. -/
theorem major_character512j (lo hi : ℕ) (a : ℕ → ℂ) {q : ℕ} [NeZero q] (r : ℤ)
    (hr : IsUnit (r : ZMod q)) (w : ℂ) (M T : ℝ) (hT : (hi : ℝ) ≤ T)
    (hsupp : ∀ k ∈ Finset.Ioc lo hi, a k ≠ 0 → IsUnit (k : ZMod q))
    (hc : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ T →
      ‖∑ k ∈ (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - Thm2.delta χ * w)‖ ≤ M) (η : ℝ) :
    ‖(∑ k ∈ Finset.Ioc lo hi,
        a k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
      (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
        ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
      Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hmodel : (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
        ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          ∑ k ∈ Finset.Ioc lo hi,
            Thm2.delta χ * w * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
    · rw [inv_one, MulChar.one_apply hr, ← Finset.mul_sum]
      simp only [Thm2.delta, ite_true]
      ring
    · intro χ _ hχ
      simp [Thm2.delta, hχ]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [shifted_character_expansion512j (Finset.Ioc lo hi) a r hr η hsupp, hmodel, ← mul_sub,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ χ : DirichletCharacter ℂ q,
      ‖gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          (∑ k ∈ Finset.Ioc lo hi,
            a k * χ (k : ZMod q) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) -
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q) *
          ∑ k ∈ Finset.Ioc lo hi,
            Thm2.delta χ * w * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
        Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
    intro χ
    have h1 := gauss_norm512j χ⁻¹
    have h2 : ‖χ (r : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    have h3 := partial_summation512j lo hi
      (fun k => a k * χ (k : ZMod q) - Thm2.delta χ * w) M T hT (hc χ) η
    have h4 : 0 ≤ (1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M :=
      (norm_nonneg _).trans h3
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_mul]
    simp only [← sub_mul]
    calc
      _ ≤ Real.sqrt q * 1 * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
        gcongr
      _ = _ := by ring
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ q,
        Real.sqrt q * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hφ.le)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => hterm χ)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ hφ.ne', one_mul]

/-- P0069 page 7 display 2.5: an integral over the arc centered at `c` with half width
`h` is the integral over the eta interval of the shifted integrand. -/
theorem arc_translate512j (F : ℝ → ℂ) (c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in Icc (c - h) (c + h), F t) = ∫ η in (-h)..h, F (c + η) := by
  rw [intervalIntegral.integral_comp_add_left, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), sub_eq_add_neg]

private lemma fourier_shift512j (n : ℤ) (c η : ℝ) :
    @fourier 1 n ((c + η : ℝ) : AddCircle (1 : ℝ)) =
      @fourier 1 n (c : AddCircle (1 : ℝ)) * @fourier 1 n (η : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0069 page 7 displays 2.5 and 2.6: the product of the two principal models on the
arc centered at `c`, integrated against e(-Nt), is e(-Nc) times the short eta integral
of the unweighted integrand. -/
theorem model_arc512j (S T : Finset ℕ) (N : ℕ) (w : ℂ) (c h : ℝ) (hh : 0 ≤ h) :
    (∫ t in Icc (c - h) (c + h),
      w * ((∑ k ∈ S, @fourier 1 (k : ℤ) ((t - c : ℝ) : AddCircle (1 : ℝ))) *
        (∑ m ∈ T, @fourier 1 (m : ℤ) ((t - c : ℝ) : AddCircle (1 : ℝ)))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) =
      w * @fourier 1 (-(N : ℤ)) (c : AddCircle (1 : ℝ)) *
        ∫ η in (-h)..h, (∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
          (∑ m ∈ T, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ)) := by
  rw [arc_translate512j _ c h hh, ← intervalIntegral.integral_const_mul]
  congr 1
  funext η
  rw [fourier_shift512j, add_sub_cancel_left]
  simp only [one_mul]
  ring

/-- P0069 page 7 display 2.6: summing the model integrals over the reduced numerators
`r` of one modulus `q` produces the Ramanujan sum at frequency minus `N` times the
short eta integral. The numerator sum is the body of `ramanujan512`. -/
theorem model_modulus512j (S T : Finset ℕ) (N q : ℕ) (w : ℂ) (h : ℝ) (hh : 0 ≤ h) :
    (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      ∫ t in Icc ((r : ℝ) / q - h) ((r : ℝ) / q + h),
        w * ((∑ k ∈ S, @fourier 1 (k : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          (∑ m ∈ T, @fourier 1 (m : ℤ) ((t - (r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) =
      w * (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
        ∫ η in (-h)..h, (∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
          (∑ m ∈ T, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ)) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => model_arc512j S T N w ((r : ℝ) / q) h hh

end LeanLab.BHP1997.Route512Major
