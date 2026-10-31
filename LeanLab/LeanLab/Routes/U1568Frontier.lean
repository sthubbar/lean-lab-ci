import LeanLab.ExceptionalSet.ChenPrimes

/-!
# T2 FRONTIER: ternary Goldbach with three Chen primes outside the class 3 mod 6

Unit U-1568, idea I-0134, cloud run 20261027T0004Z-17012. AI wrote this Lean code, Claude,
checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Question. Matomäki and Shao, Compositio 153, 2017, arXiv 1512.03213 Theorem 1.2: every large
`N ≡ 3 mod 6` is a sum of three Chen primes. The classes `N ≡ 1` and `N ≡ 5 mod 6` are not
treated there, nor in Li and Pan arXiv 0812.4479, which also needs `3 ∣ N`. What is known for them?

Answer in this file.
* `et1_le`, `et5_le`, PROVED unconditional: the number of `N ≤ X`, `N ≡ 1` resp. `5 mod 6`, that
  are not sums of three Chen primes is at most `EChen X + 1`, where `EChen` counts the class
  `4 mod 6` exceptions for two Chen primes. Reason: `3` and `7` are Chen primes, `5` and
  `9 = 3 * 3` being in `P₂`, and `N - 3`, `N - 7` lie in the class `4 mod 6`.
* `ternary15_of_GT11`, CONDITIONAL ON the lab's `GT11`, P0039 Grimmelt-Teräväinen arXiv
  2508.16400 Theorem 1.1 p. 2: both classes have a power saving exceptional set `O(X^{1-δ})`.
* `mod6_structure5`, `mod6_structure1`, PROVED: a representation by Chen primes other than `2`
  and `3` uses at least one, resp. two, Chen primes `≡ 1 mod 6`, which are all of the Dickson form
  `3 r - 2`, `r` prime, by `chen_one_mod_six`. So the shift by `3` or `7` is forced in spirit:
  without the small prime `3` the class `1` route needs two Dickson primes.

Numerics, Routes/numerics/U1568/ternary_chen.py to `X = 10^7`: the only odd `N` that are not
sums of three Chen primes are `1, 3, 5`; every `N ≡ 1 mod 6` from `7` has `N - 3` a sum of two
Chen primes, every `N ≡ 5 mod 6` from `11` has `N - 7` one.
-/

open Finset
open LeanLab.AlmostPrimes LeanLab.ExceptionalSet

namespace LeanLab.Routes.U1568

attribute [local instance] Classical.propDecidable

/-- `N` is a sum of three Chen primes.
Plain math: `N = p + q + r` with `p, q, r` prime and `Ω(p+2), Ω(q+2), Ω(r+2) ≤ 2`. -/
def IsChenTernary (N : ℕ) : Prop :=
  ∃ p q r, IsChenPrime p ∧ IsChenPrime q ∧ IsChenPrime r ∧ p + q + r = N

/-- Exceptions in the class `a mod 6`.
Plain math: `E₃(a; X) = #{N ≤ X : N ≡ a mod 6, N not a sum of three Chen primes}`. -/
noncomputable def ET (a X : ℕ) : ℕ :=
  #{n ∈ Icc 1 X | n % 6 = a ∧ ¬ IsChenTernary n}

lemma chen_three : IsChenPrime 3 := by
  refine ⟨Nat.prime_three, ?_⟩
  rw [bigOmega_eq_cardFactors, show (3 + 2 : ℕ) = 5 by rfl,
    ArithmeticFunction.cardFactors_apply_prime (by norm_num)]
  norm_num

lemma chen_seven : IsChenPrime 7 := by
  refine ⟨by norm_num, ?_⟩
  rw [bigOmega_eq_cardFactors, show (7 + 2 : ℕ) = 3 * 3 by rfl,
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three]

/-- Generic shift bound: if a fixed Chen prime `d` moves the class `a` into the class `4 mod 6`,
the ternary exceptions in class `a` are at most the binary class 4 exceptions plus the `n < d + 4`. -/
lemma et_le_of_shift (a d X : ℕ) (hd : IsChenPrime d) (ha : (a + 6 - d % 6) % 6 = 4)
    (hsmall : ∀ n, n < d + 4 → n % 6 = a → 1 ≤ n → n = a) :
    ET a X ≤ EChen X + 1 := by
  classical
  set S := (Icc 1 X).filter (fun n => n % 6 = a ∧ ¬ IsChenTernary n) with hS
  have hsplit : S = S.filter (fun n => d + 4 ≤ n) ∪ S.filter (fun n => ¬ d + 4 ≤ n) :=
    (filter_union_filter_not_eq _ _).symm
  have h1 : (S.filter (fun n => d + 4 ≤ n)).card ≤ EChen X := by
    unfold EChen
    refine card_le_card_of_injOn (fun n => n - d) ?_ ?_
    · intro n hn
      simp only [hS, coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq] at hn
      simp only [coe_filter, mem_filter, mem_Icc, Set.mem_ofPred_eq]
      obtain ⟨⟨⟨hn1, hnX⟩, hna, hnt⟩, hnd⟩ := hn
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      rintro ⟨p, q, hp, hq, hpq⟩
      exact hnt ⟨d, p, q, hd, hp, hq, by omega⟩
    · intro x hx y hy hxy
      simp only [hS, coe_filter, mem_filter, Set.mem_ofPred_eq] at hx hy
      simp only at hxy
      omega
  have h2 : (S.filter (fun n => ¬ d + 4 ≤ n)).card ≤ 1 := by
    refine card_le_one.2 fun x hx y hy => ?_
    simp only [hS, mem_filter, mem_Icc] at hx hy
    rw [hsmall x (by omega) hx.1.2.1 hx.1.1.1, hsmall y (by omega) hy.1.2.1 hy.1.1.1]
  unfold ET
  rw [← hS, hsplit]
  exact (card_union_le _ _).trans (by omega)

/-- **Class 1 mod 6, PROVED unconditional.**
Plain math: `E₃(1; X) ≤ E₂(4; X) + 1`, since `N = 3 + (N - 3)` and `3` is a Chen prime. -/
theorem et1_le (X : ℕ) : ET 1 X ≤ EChen X + 1 :=
  et_le_of_shift 1 3 X chen_three (by norm_num) (fun n h1 h2 h3 => by omega)

/-- **Class 5 mod 6, PROVED unconditional.**
Plain math: `E₃(5; X) ≤ E₂(4; X) + 1`, since `N = 7 + (N - 7)` and `7 + 2 = 3 * 3`. -/
theorem et5_le (X : ℕ) : ET 5 X ≤ EChen X + 1 :=
  et_le_of_shift 5 7 X chen_seven (by norm_num) (fun n h1 h2 h3 => by omega)

/-- **Power saving for three Chen primes in the classes 1 and 5 mod 6, CONDITIONAL ON `GT11`.**
Plain math: if all but `O(X^{1-δ})` of the `m ≤ X`, `m ≡ 4 mod 6`, are sums of two Chen primes,
P0039 Theorem 1.1, then there are `δ' > 0` and `C'` with
`E₃(1; X) + E₃(5; X) ≤ C' X^{1-δ'}` for all `X ≥ 1`; stated per class. -/
theorem ternary15_of_GT11 (h : GT11) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      (ET 1 X : ℝ) ≤ C * (X : ℝ) ^ (1 - δ) ∧ (ET 5 X : ℝ) ≤ C * (X : ℝ) ^ (1 - δ) := by
  obtain ⟨δ, hδ, C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at this
    exact le_trans (Nat.cast_nonneg _) this
  refine ⟨min δ 1, lt_min hδ one_pos, C + 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (1 - δ) ≤ (X : ℝ) ^ (1 - min δ 1) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [min_le_left δ 1])
  have hone : (1 : ℝ) ≤ (X : ℝ) ^ (1 - min δ 1) :=
    Real.one_le_rpow hX1 (by linarith [min_le_right δ 1])
  have key : ∀ a, (ET a X ≤ EChen X + 1) → (ET a X : ℝ) ≤ (C + 1) * (X : ℝ) ^ (1 - min δ 1) := by
    intro a ha
    have h1 : (ET a X : ℝ) ≤ (EChen X : ℝ) + 1 := by exact_mod_cast ha
    nlinarith [hC X hX, mul_le_mul_of_nonneg_left hpow hC0]
  exact ⟨key 1 (et1_le X), key 5 (et5_le X)⟩

/-- **Structure, class 5, PROVED.**
Plain math: if `N = p + q + r ≡ 5 mod 6` with Chen primes `p, q, r ∉ {2, 3}`, then one of them is
`≡ 1 mod 6`, hence of the Dickson form `3 s - 2`, `s` prime. -/
theorem mod6_structure5 {p q r : ℕ} (hp : IsChenPrime p) (hq : IsChenPrime q) (hr : IsChenPrime r)
    (hp3 : 3 < p) (hq3 : 3 < q) (hr3 : 3 < r) (h : (p + q + r) % 6 = 5) :
    p % 6 = 1 ∨ q % 6 = 1 ∨ r % 6 = 1 := by
  have := prime_mod_six hp.1 hp3
  have := prime_mod_six hq.1 hq3
  have := prime_mod_six hr.1 hr3
  omega

/-- **Structure, class 1, PROVED.**
Plain math: if `N = p + q + r ≡ 1 mod 6` with Chen primes `p, q, r ∉ {2, 3}`, then at least two
of them are `≡ 1 mod 6`. -/
theorem mod6_structure1 {p q r : ℕ} (hp : IsChenPrime p) (hq : IsChenPrime q) (hr : IsChenPrime r)
    (hp3 : 3 < p) (hq3 : 3 < q) (hr3 : 3 < r) (h : (p + q + r) % 6 = 1) :
    (p % 6 = 1 ∧ q % 6 = 1) ∨ (p % 6 = 1 ∧ r % 6 = 1) ∨ (q % 6 = 1 ∧ r % 6 = 1) := by
  have := prime_mod_six hp.1 hp3
  have := prime_mod_six hq.1 hq3
  have := prime_mod_six hr.1 hr3
  omega

/-! ## Vacuity instances -/

lemma chen_five : IsChenPrime 5 := by
  refine ⟨by norm_num, ?_⟩
  rw [bigOmega_eq_cardFactors, show (5 + 2 : ℕ) = 7 by rfl,
    ArithmeticFunction.cardFactors_apply_prime (by norm_num)]
  norm_num

lemma chen_thirteen : IsChenPrime 13 := by
  refine ⟨by norm_num, ?_⟩
  rw [bigOmega_eq_cardFactors, show (13 + 2 : ℕ) = 3 * 5 by rfl,
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
    ArithmeticFunction.cardFactors_apply_prime (by norm_num)]

/-- Vacuity for `mod6_structure5`: `17 = 7 + 5 + 5`, Chen primes above 3, sum `≡ 5 mod 6`. -/
theorem structure5_vacuity : ∃ p q r, IsChenPrime p ∧ IsChenPrime q ∧ IsChenPrime r ∧
    3 < p ∧ 3 < q ∧ 3 < r ∧ (p + q + r) % 6 = 5 :=
  ⟨7, 5, 5, chen_seven, chen_five, chen_five, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Vacuity for `mod6_structure1`: `25 = 7 + 13 + 5`, sum `≡ 1 mod 6`. -/
theorem structure1_vacuity : ∃ p q r, IsChenPrime p ∧ IsChenPrime q ∧ IsChenPrime r ∧
    3 < p ∧ 3 < q ∧ 3 < r ∧ (p + q + r) % 6 = 1 :=
  ⟨7, 13, 5, chen_seven, chen_thirteen, chen_five, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- Vacuity for `IsChenTernary`, the predicate is not empty in either class:
`13 = 3 + 5 + 5`, `≡ 1 mod 6`, and `17 = 7 + 5 + 5`, `≡ 5 mod 6`. -/
theorem ternary_vacuity : IsChenTernary 13 ∧ IsChenTernary 17 :=
  ⟨⟨3, 5, 5, chen_three, chen_five, chen_five, rfl⟩, ⟨7, 5, 5, chen_seven, chen_five, chen_five, rfl⟩⟩

/-- Vacuity for the hypothesis shape of `GT11`: the bound with `δ = 0`, `C = 1` holds outright,
`EChen X ≤ X`. This shows the shape is consistent; `δ > 0` itself is the cited content of P0039
Theorem 1.1, carried in the lab as `grimmeltTeravainen` with `sorry`. -/
theorem gt11_shape_delta0 : ∀ X : ℕ, 1 ≤ X → (EChen X : ℝ) ≤ 1 * (X : ℝ) ^ (1 - (0 : ℝ)) := by
  intro X _
  simp only [sub_zero, Real.rpow_one, one_mul]
  have : EChen X ≤ X := by
    unfold EChen
    exact (card_filter_le _ _).trans (by simp)
  exact_mod_cast this

end LeanLab.Routes.U1568

#print axioms LeanLab.Routes.U1568.et1_le
#print axioms LeanLab.Routes.U1568.et5_le
#print axioms LeanLab.Routes.U1568.ternary15_of_GT11
#print axioms LeanLab.Routes.U1568.mod6_structure5
#print axioms LeanLab.Routes.U1568.mod6_structure1
#print axioms LeanLab.Routes.U1568.structure5_vacuity
#print axioms LeanLab.Routes.U1568.structure1_vacuity
#print axioms LeanLab.Routes.U1568.ternary_vacuity
#print axioms LeanLab.Routes.U1568.gt11_shape_delta0
