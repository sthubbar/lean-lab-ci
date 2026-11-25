import LeanLab.Halupczok2012.Feed1122LargeModuli
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
S136 split of `Feed1122LargeModuli.dyadic_block` along Perelli Pintz Salerno 1984,
page 531: the character expansion of the progression error, first line of display 4,
and the character side estimate of one dyadic block, which is the rest of display 4,
the Huxley Iwaniec reduction 5, the target 6 and the Heath Brown argument of pages
531 to 538. Paper checked on the numdam page images, pages 530 and 531.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122LargeModuliS136Char

open Finset
open scoped Classical

/-- The twisted Chebyshev function `∑_{n ≤ z} Λ(n) χ(n)`, PPS1984 page 531, the sums
inside the definition of `E(z, h, χ)`. -/
noncomputable def psiChi (z : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)

/-- PPS1984 page 531, `E(z, h, χ) = ∑_{z < n ≤ z + h} Λ(n) χ(n)`, minus `h` when `χ` is
principal. -/
noncomputable def charE (z h : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  psiChi (z + h) χ - psiChi z χ - (if χ = 1 then (h : ℂ) else 0)

/-- PPS1984 page 531, the right side of the first line of display 4 for one modulus:
`(1/φ(q)) ∑_{χ mod q} |E(z, h, χ)|`, set to `0` at `q = 0`. -/
noncomputable def charBound (z h : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    haveI : NeZero q := ⟨hq⟩
    (1 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ‖

/-- PROVED piece, PPS1984 page 531, the well known relation before display 4,
`ψ(z+h;q,a) - ψ(z;q,a) - h/φ(q) = φ(q)⁻¹ ∑_χ χ̄(a) E(z,h,χ)`, in absolute value, by the
orthogonality of Dirichlet characters. -/
theorem char_expansion :
    ∀ (z h : ℝ) (q : ℕ) (a : ℤ), 1 ≤ q → Int.gcd a q = 1 →
      ppsTerm z h q a ≤ charBound z h q := by
  intro z h q a hq ha
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have hunit : IsUnit (a : ZMod q) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact ha
  have hφ : (q.totient : ℝ) ≠ 0 := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
    exact_mod_cast this.ne'
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ
  -- the orthogonality step for one truncation point
  have hpsi : ∀ w : ℝ, ((psiAP w q a : ℝ) : ℂ) * (q.totient : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * psiChi w χ := by
    intro w
    unfold psiAP psiChi
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    push_cast
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    have e : ∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q)⁻¹ * ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * χ (n : ZMod q) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun χ _ => by ring
    rw [e, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit]
    have hiff : (a : ZMod q) = (n : ZMod q) ↔ (n : ℤ) ≡ a [ZMOD q] := by
      rw [show ((n : ℕ) : ZMod q) = ((n : ℤ) : ZMod q) by push_cast; rfl,
        ZMod.intCast_eq_intCast_iff]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    by_cases hn : (n : ℤ) ≡ a [ZMOD q]
    · rw [if_pos hn, if_pos (hiff.mpr hn)]
    · rw [if_neg hn, if_neg (fun h => hn (hiff.mp h))]; simp
  have hone : (1 : DirichletCharacter ℂ q) (a : ZMod q)⁻¹ = 1 := by
    obtain ⟨u, hu⟩ := hunit
    rw [← hu, ZMod.inv_coe_unit, MulChar.one_apply_coe]
  have hkey : ((psiAP (z + h) q a - psiAP z q a - h / q.totient : ℝ) : ℂ) =
      (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * charE z h χ := by
    have e1 := hpsi (z + h)
    have e2 := hpsi z
    unfold charE
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← e1, ← e2, Finset.sum_eq_single (1 : DirichletCharacter ℂ q)
      (fun χ _ hχ => by rw [if_neg hχ, mul_zero]) (fun h1 => absurd (Finset.mem_univ _) h1),
      if_pos rfl, hone, one_mul]
    push_cast
    field_simp
  unfold ppsTerm charBound
  rw [dif_neg hq0]
  have hn : |psiAP (z + h) q a - psiAP z q a - h / q.totient| =
      ‖((psiAP (z + h) q a - psiAP z q a - h / q.totient : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn, hkey, norm_mul]
  have h1 : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  rw [norm_mul]
  have := DirichletCharacter.norm_le_one χ (a : ZMod q)⁻¹
  calc ‖χ (a : ZMod q)⁻¹‖ * ‖charE z h χ‖ ≤ 1 * ‖charE z h χ‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _

/-- PPS1984 page 531, the first line of display 4 with each character replaced by the
primitive character inducing it: `(1/φ(q)) ∑_{χ mod q} |E(z, h, χ₁)|`, `0` at `q = 0`. -/
noncomputable def primBound (z h : ℝ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    haveI : NeZero q := ⟨hq⟩
    (1 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ.primitiveCharacter‖

/-- Prime powers up to `N` sharing a factor with `q` divide `q ^ log₂ N`, so their
von Mangoldt mass is at most `log₂ N · log q`. -/
theorem noncoprime_vonMangoldt_le (q N : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ (Ioc 0 N).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n ≤
      (Nat.log 2 N : ℝ) * Real.log q := by
  set K := Nat.log 2 N
  have hqK : q ^ K ≠ 0 := pow_ne_zero _ (by omega)
  rw [← sum_filter_ne_zero]
  calc _ ≤ ∑ d ∈ (q ^ K).divisors, ArithmeticFunction.vonMangoldt d := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        intro n hn
        simp only [mem_filter, mem_Ioc] at hn
        obtain ⟨⟨⟨hn0, hnN⟩, hcop⟩, hΛ⟩ := hn
        obtain ⟨p, k, hp, hk, rfl⟩ :=
          (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
        have hpq : p ∣ q := by
          by_contra hpq
          exact hcop (((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).pow_left k)
        have hkK : k ≤ K := Nat.le_log_of_pow_le (by norm_num)
          ((Nat.pow_le_pow_left hp.two_le k).trans hnN)
        rw [Nat.mem_divisors]
        exact ⟨(pow_dvd_pow_of_dvd hpq k).trans (pow_dvd_pow q hkK), hqK⟩
    _ = (K : ℝ) * Real.log q := by
        rw [ArithmeticFunction.vonMangoldt_sum]; push_cast; rw [Real.log_pow]

/-- One truncation point: `|ψ(w, χ) - ψ(w, χ₁)| ≤ 2 ∑_{n ≤ w, (n,q) > 1} Λ(n)`. -/
theorem psiChi_sub_primitive_le (w : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖psiChi w χ - psiChi w χ.primitiveCharacter‖ ≤
      2 * ∑ n ∈ (Ioc 0 ⌊w⌋₊).filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n := by
  unfold psiChi
  rw [← sum_sub_distrib, sum_filter, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    ArithmeticFunction.vonMangoldt_nonneg]
  by_cases hc : n.Coprime q
  · rw [if_neg (not_not.mpr hc), mul_zero]
    have hic : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
    have := χ.primitiveCharacter_apply_of_isCoprime hic
    push_cast at this
    rw [this, sub_self, norm_zero, mul_zero]
  · rw [if_pos hc]
    have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
    have h2 := DirichletCharacter.norm_le_one χ.primitiveCharacter (n : ZMod χ.conductor)
    have h3 := norm_sub_le (χ (n : ZMod q)) (χ.primitiveCharacter (n : ZMod χ.conductor))
    have h4 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith

/-- A character is principal exactly when its primitive character is. -/
theorem primitiveCharacter_eq_one_iff (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h'
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    rw [DirichletCharacter.eq_one_iff_conductor_eq_one]
    have hp := χ.primitiveCharacter_isPrimitive
    rw [DirichletCharacter.isPrimitive_def, h', DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

/-- PROVED piece, PPS1984 page 531, the display after the well known relation: if `χ₁` primitive
induces `χ mod q` then `E(z, h, χ₁) - E(z, h, χ) ≪ log q log z ≪ L²`, here for moduli
`q ≤ x`, `x/2 < z ≤ x`, `0 < h ≤ x`, with the explicit constant 12. -/
theorem prim_diff :
    ∃ c : ℝ, ∀ x z h : ℝ, 2 ≤ x → x / 2 < z → z ≤ x → 0 < h → h ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ x → ∀ χ : DirichletCharacter ℂ q,
        ‖charE z h χ - charE z h χ.primitiveCharacter‖ ≤ c * Real.log x ^ 2 := by
  refine ⟨12, ?_⟩
  intro x z h hx hz1 hz2 hh1 hh2 q _ hqx χ
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxpos : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlq : Real.log q ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hqx
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  set N := ⌊2 * x⌋₊
  have hN4 : 4 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hK : (Nat.log 2 N : ℝ) * Real.log 2 ≤ 2 * Real.log x := by
    have h2K : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2K' : (2 : ℝ) ^ Nat.log 2 N ≤ 2 * x := by
      have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2K
      push_cast at this
      exact this.trans (Nat.floor_le (by linarith))
    have := Real.log_le_log (by positivity) h2K'
    rw [Real.log_pow] at this
    have hx2 : 2 * x ≤ x ^ 2 := by nlinarith
    have := this.trans (Real.log_le_log (by positivity) hx2)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hS : ∀ w : ℝ, ⌊w⌋₊ ≤ N →
      ∑ n ∈ (Ioc 0 ⌊w⌋₊).filter (fun n => ¬ n.Coprime q), ArithmeticFunction.vonMangoldt n ≤
        3 * Real.log x ^ 2 := by
    intro w hw
    refine (noncoprime_vonMangoldt_le q _ hq1).trans ?_
    have hmono : (Nat.log 2 ⌊w⌋₊ : ℝ) ≤ Nat.log 2 N := by
      exact_mod_cast Nat.log_mono_right hw
    have hK' : (Nat.log 2 N : ℝ) ≤ 3 * Real.log x := by
      have := Real.log_two_gt_d9
      have h0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
      nlinarith
    calc (Nat.log 2 ⌊w⌋₊ : ℝ) * Real.log q ≤ (3 * Real.log x) * Real.log x :=
          mul_le_mul (hmono.trans hK') hlq hlq0 (by positivity)
      _ = 3 * Real.log x ^ 2 := by ring
  have hw1 : ⌊z + h⌋₊ ≤ N := Nat.floor_mono (by linarith)
  have hw2 : ⌊z⌋₊ ≤ N := Nat.floor_mono (by linarith)
  have hd1 := psiChi_sub_primitive_le (z + h) q χ
  have hd2 := psiChi_sub_primitive_le z q χ
  have e : charE z h χ - charE z h χ.primitiveCharacter =
      (psiChi (z + h) χ - psiChi (z + h) χ.primitiveCharacter) -
        (psiChi z χ - psiChi z χ.primitiveCharacter) := by
    unfold charE
    split_ifs with h1 h2 h2
    · ring
    · exact absurd ((primitiveCharacter_eq_one_iff q χ).mpr h1) h2
    · exact absurd ((primitiveCharacter_eq_one_iff q χ).mp h2) h1
    · ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := hS (z + h) hw1
  have := hS z hw2
  linarith

/-- LEAF: PPS1984 page 531 display 4 second and third lines, display 5 from Huxley
Iwaniec, display 6, and the Heath Brown identity argument of pages 531 to 538, for the
primitive character sums of one dyadic block of moduli above x to the 1/100, uniformly
in the block index. Class HARD. -/
theorem dyadic_block_prim :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (h z : ℕ → ℝ),
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) → ∀ j : ℕ,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ) ∧
          x ^ (1 / 100 : ℝ) * 2 ^ j ≤ (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 100 : ℝ) * 2 ^ (j + 1)),
        primBound (z q) (h q) q ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- One modulus: `charBound ≤ primBound + c L²`, from `prim_diff`. -/
theorem charBound_le_primBound (c x z h : ℝ) (q : ℕ) (hq : 1 ≤ q) (hqx : (q : ℝ) ≤ x)
    (hc : ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ x → ∀ χ : DirichletCharacter ℂ q,
        ‖charE z h χ - charE z h χ.primitiveCharacter‖ ≤ c * Real.log x ^ 2) :
    charBound z h q ≤ primBound z h q + c * Real.log x ^ 2 := by
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  unfold charBound primBound
  rw [dif_neg hq0, dif_neg hq0]
  have hφpos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  have hsum : ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ‖ ≤
      ∑ χ : DirichletCharacter ℂ q, (‖charE z h χ.primitiveCharacter‖ + c * Real.log x ^ 2) := by
    refine Finset.sum_le_sum fun χ _ => ?_
    have h1 := hc q hqx χ
    have h2 := norm_sub_norm_le (charE z h χ) (charE z h χ.primitiveCharacter)
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsum
  have := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hφpos))
  rw [mul_add, ← mul_assoc, one_div_mul_cancel hφpos.ne', one_mul] at this
  exact this

/-- `dyadic_block_char` from the proved piece `prim_diff` and the leaf
`dyadic_block_prim`. The error `Q L²` is absorbed since `Q ≤ y x^{-1/2}`. -/
theorem dyadic_block_char :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (h z : ℕ → ℝ),
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) → ∀ j : ℕ,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ) ∧
          x ^ (1 / 100 : ℝ) * 2 ^ j ≤ (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 100 : ℝ) * 2 ^ (j + 1)),
        charBound (z q) (h q) q ≤ C * y * Real.log x ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, hB, C, x0, hC⟩ := dyadic_block_prim A ε hA hε
  obtain ⟨c, hc⟩ := prim_diff
  obtain ⟨x1, hx1⟩ := eventually_log_rpow_le (A + 2) (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨B, hB, C + |c|, max (max x0 x1) 3, ?_⟩
  intro x y Q hx hxy hyx hQ h z hh hz j
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hy0 : 0 ≤ y := (Real.rpow_nonneg hxpos.le _).trans hxy
  have hLB : Real.log x ^ (-B) ≤ 1 := by
    have hL1 : 1 ≤ Real.log x := by
      have := Real.exp_one_lt_d9
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hQ' : Q ≤ y * x ^ (-(1 / 2) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hLB (mul_nonneg hy0 (Real.rpow_nonneg hxpos.le (-(1 / 2) : ℝ)))
    linarith
  have hQx : Q ≤ x := by
    have : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hxone (by norm_num)
    have := mul_le_mul_of_nonneg_left this hy0
    linarith
  set S := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ) ∧
          x ^ (1 / 100 : ℝ) * 2 ^ j ≤ (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 100 : ℝ) * 2 ^ (j + 1))
  have hmem : ∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ Q := by
    intro q hq
    simp only [S, mem_filter, mem_Icc] at hq
    have hQ0 : 0 ≤ Q := by
      by_contra hneg
      have : ⌊Q⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
      omega
    exact ⟨hq.1.1, (Nat.cast_le.mpr hq.1.2).trans (Nat.floor_le hQ0)⟩
  have hstep : ∀ q ∈ S, charBound (z q) (h q) q ≤
      primBound (z q) (h q) q + |c| * Real.log x ^ 2 := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := hmem q hq
    have := charBound_le_primBound c x (z q) (h q) q hq1 (hqQ.trans hQx)
      (fun q' _ hq' χ => hc x (z q) (h q) (by linarith) (hz q).1 (hz q).2 (hh q).1
        ((hh q).2.trans hyx) q' hq' χ)
    have : c * Real.log x ^ 2 ≤ |c| * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    linarith
  have hcardS : (S.card : ℝ) ≤ y * x ^ (-(1 / 2) : ℝ) := by
    have h1 : S.card ≤ ⌊Q⌋₊ := by
      calc S.card ≤ (Icc 1 ⌊Q⌋₊).card := card_filter_le _ _
        _ = ⌊Q⌋₊ := by simp
    rcases Nat.eq_zero_or_pos ⌊Q⌋₊ with h0 | hpos
    · have : S.card = 0 := by omega
      rw [this]; simp; exact mul_nonneg hy0 (Real.rpow_nonneg hxpos.le _)
    · have hQ0 : 0 ≤ Q := by
        by_contra hneg
        have : ⌊Q⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
        omega
      calc (S.card : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast h1
        _ ≤ Q := Nat.floor_le hQ0
        _ ≤ _ := hQ'
  -- `x^{-1/2} L² ≤ L^{-A}` from `L^{A+2} ≤ x^{1/2}`
  have habs : x ^ (-(1 / 2) : ℝ) * Real.log x ^ 2 ≤ Real.log x ^ (-A) := by
    have h1 := hx1 x hx1'
    have hxh : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hLpos _
    have e2 : Real.log x ^ (A + 2) = Real.log x ^ A * Real.log x ^ 2 := by
      rw [Real.rpow_add hLpos]; norm_cast
    rw [e2] at h1
    rw [Real.rpow_neg hxpos.le, Real.rpow_neg hLpos.le, inv_mul_le_iff₀ hxh,
      le_mul_inv_iff₀ hLA]
    linarith
  have hmain := hC x y Q hx0 hxy hyx hQ h z hh hz j
  calc ∑ q ∈ S, charBound (z q) (h q) q
      ≤ ∑ q ∈ S, (primBound (z q) (h q) q + |c| * Real.log x ^ 2) := sum_le_sum hstep
    _ = ∑ q ∈ S, primBound (z q) (h q) q + (S.card : ℝ) * (|c| * Real.log x ^ 2) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ C * y * Real.log x ^ (-A) + (y * x ^ (-(1 / 2) : ℝ)) * (|c| * Real.log x ^ 2) := by
        gcongr
    _ = C * y * Real.log x ^ (-A) + |c| * y * (x ^ (-(1 / 2) : ℝ) * Real.log x ^ 2) := by ring
    _ ≤ C * y * Real.log x ^ (-A) + |c| * y * Real.log x ^ (-A) := by
        gcongr
    _ = (C + |c|) * y * Real.log x ^ (-A) := by ring

/-- `char_expansion` and `dyadic_block_char` give `Feed1122LargeModuli.dyadic_block`,
same statement; the only open input is the leaf `dyadic_block_prim`. -/
theorem dyadic_block_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) → ∀ j : ℕ,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ) ∧
          x ^ (1 / 100 : ℝ) * 2 ^ j ≤ (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 100 : ℝ) * 2 ^ (j + 1)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, hB, C, x0, hC⟩ := dyadic_block_char A ε hA hε
  refine ⟨B, hB, C, x0, ?_⟩
  intro x y Q hx hxy hyx hQ a h z ha hh hz j
  refine le_trans (sum_le_sum fun q hq => ?_) (hC x y Q hx hxy hyx hQ h z hh hz j)
  simp only [mem_filter, mem_Icc] at hq
  exact char_expansion (z q) (h q) q (a q) hq.1.1 (ha q)

end LeanLab.Halupczok2012.Feed1122LargeModuliS136Char

#print axioms LeanLab.Halupczok2012.Feed1122LargeModuliS136Char.char_expansion
#print axioms LeanLab.Halupczok2012.Feed1122LargeModuliS136Char.prim_diff
#print axioms LeanLab.Halupczok2012.Feed1122LargeModuliS136Char.dyadic_block_of_leaves
