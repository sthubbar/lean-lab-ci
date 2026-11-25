/-
AI wrote this Lean code, Claude, ROUTE BURST S76, burst-20261122, unit thm3_split.
Split of the LEAF `ProgressionEPS70.thm3`, Ernvall-Hytonen and Palojarvi, arXiv 2003.01925v4,
Theorem 3 p. 3, along the paper's own proof in Section 3.3, pp. 36 to 40:
* `ortho`, PROVED: the first equality of display (8) p. 13, orthogonality of characters.
* `lemma12_omega`, LEAF MEDIUM, `lemma12_card_le_log`, LEAF EASY: the two halves of the
  proof of Lemma 12 p. 13; `lemma12`, PROVED from them; `principal_eq` and `principal_lemma12`, PROVED:
  the principal character term of (8).
* `buthe_thm10`, LEAF MEDIUM, and `sage_check`, LEAF EASY: p. 36; `psi_RH`, PROVED from them.
* `formula9`, PROVED: formula (9) p. 13. `psi0_eq_sum` and `lemma13`, PROVED: Lemma 13 p. 14.
  `reduce_primitive`, PROVED from them with Lemma 12, as used on p. 37.
* `thm29_lemma30`, LEAF HARD: Theorem 29 p. 31 and Lemma 30 p. 35, the truncated explicit
  formula (39) and the zero sum bound under GRH, for each nonprincipal character.
* `lemma17`, `lemma18`, LEAF MEDIUM: Lemmas 17 and 18 pp. 15 to 16. `card_even_le`,
  PROVED. `lemmas17_18_avg`, PROVED from them: the average over characters, p. 38.
* `lemma21`, LEAF MEDIUM: Lemma 21 p. 19 per character. `card_odd_le`, PROVED: half the
  characters are odd, p. 37. `lemma21_avg`, PROVED from them, p. 38.
* `combine`, LEAF MEDIUM: the simplification pp. 38 to 40 down to the right side with R1 q,
  a pure inequality between explicit functions of x and q. A Python mpmath check over q
  from 3 to 10^40 and x from 2 to 10^99 found slack at least 1018.
* `thm3_S76`, PROVED from the leaves: the exact statement of `ProgressionEPS70.thm3`.
The bracket of Theorem 29 was read on the rendered page 31: the terms with
`(log log qx)^2` and `log log qx` sit inside the factor `x^0.423 / log x`.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ProgressionEPS70

namespace LeanLab.BS2022GRH.ProgressionThm3S76
open Real Finset Classical Filter ChenThresholdGRH ProgressionEPS70
noncomputable section

/-- psi of x and chi, EP2022 p. 12: the sum of `χ(n) Λ(n)` over `n ≤ x`. -/
def psiChi {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- psi of x, EP2022 p. 12: the sum of `Λ(n)` over `n ≤ x`. -/
def psiR (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)

/-- psi0 of x and chi, EP2022 display (9) p. 13: the mean of the left and right limits,
so half the jump `χ(x) Λ(x)` is removed when x is an integer. -/
def psi0Chi {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) : ℂ :=
  psiChi χ x - if (⌊x⌋₊ : ℝ) = x then χ ⌊x⌋₊ * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℂ) / 2
    else 0

/-- `L'(0, χ) / L(0, χ)`, EP2022 display (10) p. 14. -/
def logDerivAt0 {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0

/-- `b(χ)`, EP2022 displays (11) and (12) p. 14: the constant term of the Laurent series of
`L'(s, χ) / L(s, χ)` at `s = 0`, written as the limit of `L'/L(s) - 1/s`. -/
def bChi {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) fun s =>
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s - 1 / s

/-- `a` of display (39) p. 37: 1 when `χ(-1) = -1`, else 0. -/
def aChi {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ := if χ (-1) = -1 then 1 else 0

/-- The trivial zero sum of (39) p. 37: `∑_{m ≥ 1} x^(a - 2m) / (2m - a)`. -/
def trivSum {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) : ℂ :=
  ∑' k : ℕ, ((x : ℂ) ^ (aChi χ - 2 * ((k : ℂ) + 1))) / (2 * ((k : ℂ) + 1) - aChi χ)

/-- `ψ0(x, χ*) + a L'/L(0, χ*) + (1 - a)(log x + b(χ*)) - ∑ x^(a-2m)/(2m-a)`, the left side
of Theorem 29 p. 31 without the zero sum; by (39) it is minus the sum over the zeros. -/
def residual {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  psi0Chi χ.primitiveCharacter x + aChi χ * logDerivAt0 χ.primitiveCharacter
    + (1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter) - trivSum χ.primitiveCharacter x

/-- The right side of Theorem 29 p. 31 plus the right side of Lemma 30 p. 35. -/
def zeroBound (q : ℕ) (x : ℝ) : ℝ :=
  1.363 * x ^ (0.423 : ℝ) * log x ^ 2 + 2.074 * √x * log x + 14.712 * x ^ (0.423 : ℝ) * log x
  + 18.610 * x ^ (0.423 : ℝ) * log (log (q * x)) + (2.382 * log q + 8.018) * x ^ (0.423 : ℝ)
  + (127.562 * log (log (q * x)) ^ 2 + (32.449 * log q - 1.720) * log (log (q * x))
    + 2.064 * log q ^ 2 + 6.570 * log q + 79.146) * x ^ (0.423 : ℝ) / log x
  + 13.962 * log x / x ^ (0.077 : ℝ) + 8.4 / x ^ (0.077 : ℝ) * log (log (q * x))
  + (1.255 * log q + 8.510) / x ^ (0.077 : ℝ)
  + (1 / (6 * π) * √x * log x ^ 2 + (0.184 * log q - 0.337) * √x * log x
    + (1.693 * log q + 11.946) * √x)

/-- The right side of Lemma 21 p. 19, three cases of q. -/
def lemma21RHS (q : ℕ) : ℝ :=
  if (q : ℝ) < 4 * 10 ^ 5 then
    0.027 * √(q : ℝ) * log q + 0.067 * √(q : ℝ) + 316.229 + log (q * π)
      + eulerMascheroniConstant + log 2
  else if (q : ℝ) < 10 ^ 29 then
    3.715 * log q ^ 2 + log (q / π) + eulerMascheroniConstant + log 2
  else (0.593 * log (log q) + 1.205) * log q ^ 2 + log (q / π) + eulerMascheroniConstant + log 2

/-- The error per character of the replacements by (9) and Lemma 13, p. 37. -/
def errPrim (q : ℕ) (x : ℝ) : ℝ := if q = 6 then 2.5 * log x else (log q + 0.5) * log x

/-- PROVED: EP2022 display (8) p. 13, first equality, orthogonality of Dirichlet characters
modulo q, from Mathlib's `DirichletCharacter.sum_char_inv_mul_char_eq`. -/
theorem ortho (q a : ℕ) (x : ℝ) (ha : Nat.Coprime a q) (hq : 3 ≤ q) :
    haveI : NeZero q := ⟨by omega⟩
    ((psiAP q a x : ℝ) : ℂ) = 1 / (q.totient : ℂ) *
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChi χ x := by
  haveI : NeZero q := ⟨by omega⟩
  have hu : IsUnit (a : ZMod q) := by
    rw [← ZMod.coe_unitOfCoprime a ha]; exact Units.isUnit _
  have key : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      1 / (q.totient : ℂ) * (χ ((a : ZMod q)⁻¹) * (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)))
      = if n % q = a % q then (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
    intro n
    have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q)
    have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (by omega)).ne'
    calc _ = 1 / (q.totient : ℂ) * (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ n)
          * (ArithmeticFunction.vonMangoldt n : ℂ) := by
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun χ _ => ?_; ring
      _ = _ := by
          rw [h]
          by_cases hn : n % q = a % q
          · have hz : (a : ZMod q) = n := (ZMod.natCast_eq_natCast_iff' a n q).2 hn.symm
            rw [if_pos hz, if_pos hn]; field_simp
          · have hz : ¬ (a : ZMod q) = n := fun h' => hn ((ZMod.natCast_eq_natCast_iff' a n q).1 h').symm
            rw [if_neg hz, if_neg hn]; simp
  simp only [psiChi, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [key]
  unfold psiAP
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

/-- LEAF: EP2022 Lemma 12 p. 13, first half of its proof: the sum of `Λ(n)` over `n ≤ x` with
`(n, q) > 1` is the sum over primes `p | q` of `log p` times the number of powers `p^v ≤ x`,
at most `log x` for each p. MEDIUM. -/
theorem lemma12_omega (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q), (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ (q.primeFactors.card : ℝ) * log x := by
  sorry

/-- LEAF: EP2022 Lemma 12 p. 13, second half of its proof: for `q ≥ 3`, `q ≠ 6`, the number
k of prime factors of q satisfies `k ≤ log q`. EASY. -/
theorem lemma12_card_le_log (q : ℕ) (hq : 3 ≤ q) (h6 : q ≠ 6) :
    (q.primeFactors.card : ℝ) ≤ log q := by
  sorry

/-- PROVED: EP2022 Lemma 12 p. 13: the sum of `Λ(n)` over `n ≤ x` with `(n, q) > 1` is at
most `2 log x` when q = 6 and `log q log x` otherwise. -/
theorem lemma12 (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q), (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ if q = 6 then 2 * log x else log q * log x := by
  have h := lemma12_omega q x hq hx
  have hlx : 0 ≤ log x := log_nonneg (by linarith)
  split_ifs with h6
  · subst h6
    have hc : (Nat.primeFactors 6).card = 2 := by decide +kernel
    rw [hc] at h; push_cast at h; exact h
  · exact le_trans h (mul_le_mul_of_nonneg_right (lemma12_card_le_log q hq h6) hlx)

/-- PROVED: EP2022 p. 13, `ψ(x, χ0) - ψ(x)` is minus the sum of `Λ(n)` over `n ≤ x` with
`(n, q) > 1`, the principal character term of (8). -/
theorem principal_eq (q : ℕ) (x : ℝ) :
    psiChi (1 : DirichletCharacter ℂ q) x - (psiR x : ℂ) =
      -(((∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q),
        (ArithmeticFunction.vonMangoldt n : ℝ)) : ℝ) : ℂ) := by
  unfold psiChi psiR
  push_cast
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : n.Coprime q
  · have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).2 hc
    rw [MulChar.one_apply hu, if_neg (not_not.2 hc)]; ring
  · have hu : ¬ IsUnit (n : ZMod q) := fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h)
    rw [MulChar.map_nonunit _ hu, if_pos hc]; ring

/-- PROVED: EP2022 display (8) p. 13 with Lemma 12, the principal character term. -/
theorem principal_lemma12 (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ‖psiChi (1 : DirichletCharacter ℂ q) x - (psiR x : ℂ)‖
      ≤ if q = 6 then 2 * log x else log q * log x := by
  rw [principal_eq, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg)]
  exact lemma12 q x hq hx

/-- LEAF: EP2022 p. 36, Buthe 2016 Theorem 10, reference [14] of the paper: under RH,
`|ψ(x) - x| < √x log² x / (8π)` for `x > 73.2`. MEDIUM. -/
theorem buthe_thm10 (hG : GRH) (x : ℝ) (hx : 73.2 < x) :
    |psiR x - x| < 1 / (8 * π) * √x * log x ^ 2 := by
  sorry

/-- LEAF: EP2022 p. 36, the Sage check: for every integer n in `[1, 74]`,
`|ψ(n) - n| < √n log² n / (8π) + 1.6`. A Python recomputation gives least slack
about 0.0072. EASY. -/
theorem sage_check (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 74) :
    |psiR n - n| < 1 / (8 * π) * √(n : ℝ) * log n ^ 2 + 1.6 := by
  sorry

/-- PROVED: EP2022 p. 36, `|ψ(x) - x| < √x log² x / (8π) + 2.6` for `x ≥ 2` under RH:
Buthe for `x > 73.2`, and the Sage check extended from integers to reals. -/
theorem psi_RH (hG : GRH) (x : ℝ) (hx : 2 ≤ x) :
    |psiR x - x| < 1 / (8 * π) * √x * log x ^ 2 + 2.6 := by
  by_cases hbig : 73.2 < x
  · have := buthe_thm10 hG x hbig; linarith
  push_neg at hbig
  set N := ⌊x⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hN74 : N ≤ 74 := by
    rw [hN]; exact Nat.floor_le_of_le (by push_cast; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hpsi : psiR x = psiR N := by
    unfold psiR; rw [Nat.floor_natCast]
  have hc := sage_check N hN1 hN74
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hmono : 1 / (8 * π) * √(N : ℝ) * log N ^ 2 ≤ 1 / (8 * π) * √x * log x ^ 2 := by
    have h1 : √(N : ℝ) ≤ √x := Real.sqrt_le_sqrt hNx
    have h2 : log N ≤ log x := log_le_log (by linarith) hNx
    have h3 : 0 ≤ log (N : ℝ) := log_nonneg hNpos
    have h4 : log (N : ℝ) ^ 2 ≤ log x ^ 2 := pow_le_pow_left₀ h3 h2 2
    have h5 : 0 ≤ 1 / (8 * π) := by positivity
    have h6 : √(N : ℝ) * log N ^ 2 ≤ √x * log x ^ 2 :=
      mul_le_mul h1 h4 (by positivity) (Real.sqrt_nonneg _)
    calc 1 / (8 * π) * √(N : ℝ) * log N ^ 2 = 1 / (8 * π) * (√(N : ℝ) * log N ^ 2) := by ring
      _ ≤ 1 / (8 * π) * (√x * log x ^ 2) := mul_le_mul_of_nonneg_left h6 h5
      _ = _ := by ring
  rw [hpsi]
  have habs : |psiR N - x| ≤ |psiR N - N| + |(N : ℝ) - x| := by
    have := abs_add_le (psiR N - N) ((N : ℝ) - x)
    simpa using this
  have hd : |(N : ℝ) - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- PROVED: EP2022 formula (9) p. 13: `ψ(x, χ)` and `ψ0(x, χ)` differ by at most `½ log x`. -/
theorem formula9 {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) (hx : 2 ≤ x) :
    ‖psiChi χ x‖ ≤ ‖psi0Chi χ x‖ + 1 / 2 * log x := by
  have h : psiChi χ x = psi0Chi χ x + (if (⌊x⌋₊ : ℝ) = x then
      χ ⌊x⌋₊ * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℂ) / 2 else 0) := by
    unfold psi0Chi; ring
  rw [h]
  refine le_trans (norm_add_le _ _) (add_le_add_right ?_ _)
  have hfl : (1 : ℝ) ≤ ⌊x⌋₊ := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast this
  have hΛ : (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ) ≤ log x :=
    le_trans ArithmeticFunction.vonMangoldt_le_log
      (log_le_log (by linarith) (Nat.floor_le (by linarith)))
  split_ifs
  · rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 := DirichletCharacter.norm_le_one χ (⌊x⌋₊ : ZMod m)
    have h0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt ⌊x⌋₊ := ArithmeticFunction.vonMangoldt_nonneg
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    have hp : ‖χ ⌊x⌋₊‖ * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ)
        ≤ (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℝ) := by nlinarith [norm_nonneg (χ ⌊x⌋₊)]
    linarith
  · simp only [norm_zero]
    have : 0 ≤ log x := log_nonneg (by linarith)
    linarith

/-- PROVED: `ψ0(x, χ)` as one weighted sum, the weight `½` at `n = x` for integer x. -/
theorem psi0_eq_sum {m : ℕ} (ψ : DirichletCharacter ℂ m) (x : ℝ) (hx : 1 ≤ x) :
    psi0Chi ψ x = ∑ n ∈ Icc 1 ⌊x⌋₊, ψ n * (ArithmeticFunction.vonMangoldt n : ℂ)
      * (if n = ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) = x then (1 / 2 : ℂ) else 1) := by
  unfold psi0Chi psiChi
  by_cases h : (⌊x⌋₊ : ℝ) = x
  · have hmem : ⌊x⌋₊ ∈ Icc 1 ⌊x⌋₊ := mem_Icc.2 ⟨Nat.le_floor (by simpa using hx), le_rfl⟩
    rw [if_pos h, ← add_sum_erase _ _ hmem, ← add_sum_erase _ _ hmem, if_pos ⟨rfl, h⟩]
    have hs : ∑ n ∈ (Icc 1 ⌊x⌋₊).erase ⌊x⌋₊, ψ n * (ArithmeticFunction.vonMangoldt n : ℂ)
        * (if n = ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) = x then (1 / 2 : ℂ) else 1)
        = ∑ n ∈ (Icc 1 ⌊x⌋₊).erase ⌊x⌋₊, ψ n * (ArithmeticFunction.vonMangoldt n : ℂ) :=
      sum_congr rfl (fun n hn => by
        rw [if_neg (fun h' => (ne_of_mem_erase hn) h'.1), mul_one])
    rw [hs]
    ring
  · simp [h]

/-- PROVED: EP2022 Lemma 13 p. 14, from its proof: for χ modulo q induced by the primitive
`χ*`, `|ψ0(x, χ) - ψ0(x, χ*)|` is at most the sum of `Λ(n)` over `n ≤ x` with `(n, q) > 1`. -/
theorem lemma13 (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) (χ : DirichletCharacter ℂ q) :
    ‖psi0Chi χ x - psi0Chi χ.primitiveCharacter x‖
      ≤ ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q),
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [psi0_eq_sum χ x (by linarith), psi0_eq_sum χ.primitiveCharacter x (by linarith),
    ← sum_sub_distrib, sum_filter]
  refine le_trans (norm_sum_le _ _) (sum_le_sum fun n _ => ?_)
  by_cases hc : n.Coprime q
  · have hp : χ.primitiveCharacter n = χ n := by
      have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
        (Nat.isCoprime_iff_coprime.2 hc)
      simpa using this
    rw [if_neg (not_not.2 hc), hp, sub_self, norm_zero]
  · rw [if_pos hc]
    have h0 : χ n = 0 :=
      MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))
    have hw : ‖(if n = ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) = x then (1 / 2 : ℂ) else 1)‖ ≤ 1 := by
      split_ifs <;> norm_num
    have h1 := DirichletCharacter.norm_le_one χ.primitiveCharacter (n : ZMod χ.conductor)
    have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    rw [h0, zero_mul, zero_mul, zero_sub, norm_neg, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΛ]
    have := mul_le_mul h1 hw (norm_nonneg _) zero_le_one
    calc ‖χ.primitiveCharacter n‖ * (ArithmeticFunction.vonMangoldt n : ℝ)
          * ‖(if n = ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) = x then (1 / 2 : ℂ) else 1)‖
        = (‖χ.primitiveCharacter n‖
          * ‖(if n = ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) = x then (1 / 2 : ℂ) else 1)‖)
          * (ArithmeticFunction.vonMangoldt n : ℝ) := by ring
      _ ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) := mul_le_mul_of_nonneg_right
          (by simpa using this) hΛ
      _ = _ := one_mul _

/-- PROVED: EP2022 formula (9) and Lemma 13 p. 14 with Lemma 12, as used on p. 37:
replacing `ψ(x, χ)` by `ψ0(x, χ*)` costs `½ log x` plus the Lemma 12 bound. -/
theorem reduce_primitive (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ q) :
    ‖psiChi χ x‖ ≤ ‖psi0Chi χ.primitiveCharacter x‖ + errPrim q x := by
  have h9 := formula9 χ x hx
  have h13 := lemma13 q x hq hx χ
  have h12 := lemma12 q x hq hx
  have ht : ‖psi0Chi χ x‖ ≤ ‖psi0Chi χ.primitiveCharacter x‖
      + ‖psi0Chi χ x - psi0Chi χ.primitiveCharacter x‖ := by
    have := norm_add_le (psi0Chi χ.primitiveCharacter x)
      (psi0Chi χ x - psi0Chi χ.primitiveCharacter x)
    simpa using this
  unfold errPrim
  split_ifs with h6
  · rw [ite_cond_eq_true _ _ (eq_true h6)] at h12; linarith
  · rw [ite_cond_eq_false _ _ (eq_false h6)] at h12; nlinarith

/-- LEAF: EP2022 Theorem 29 p. 31 and Lemma 30 p. 35, with T = x^0.577 + 8.509: under GRH
the truncated explicit formula (39) and the bound for the zeros up to height T + 1,
for each nonprincipal character modulo q; the bounds increase in the modulus, so q
replaces the conductor, p. 38. HARD. -/
theorem thm29_lemma30 (hG : GRH) (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖residual χ x‖ < zeroBound q x := by
  sorry

/-- PROVED: EP2022 p. 37, modulo q ≥ 3 there are as many odd characters as even ones,
multiplication by a fixed odd character swapping them. -/
theorem card_odd_eq_even (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ (-1) = -1)).card
      = ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => ¬ χ (-1) = -1)).card := by
  have hne : (-1 : ZMod q) ≠ 1 := by
    haveI : Fact (2 < q) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  have sq : ∀ χ : DirichletCharacter ℂ q, χ (-1) = 1 ∨ χ (-1) = -1 := fun χ =>
    mul_self_eq_one_iff.1 (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  obtain ⟨χ1, hχ1⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  have hodd : χ1 (-1) = -1 := (sq χ1).resolve_left hχ1
  have hinv : χ1⁻¹ (-1) = -1 := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ (-1)) (inv_mul_cancel χ1)
    simp only [MulChar.coeToFun_mul, Pi.mul_apply, hodd] at h
    rw [MulChar.one_apply isUnit_one.neg] at h
    linear_combination -h
  have hm1 : (-1 : ℂ) ≠ 1 := by norm_num
  refine Finset.card_bij' (fun χ _ => χ1 * χ) (fun χ _ => χ1⁻¹ * χ) ?_ ?_ ?_ ?_
  · intro χ hχ
    simp only [mem_filter, mem_univ, true_and] at hχ ⊢
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hodd, hχ]
    norm_num
  · intro χ hχ
    simp only [mem_filter, mem_univ, true_and] at hχ ⊢
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hinv]
    rcases sq χ with h | h
    · rw [h]; norm_num
    · exact absurd h hχ
  · intro χ _; exact inv_mul_cancel_left χ1 χ
  · intro χ _; exact mul_inv_cancel_left χ1 χ

/-- PROVED: the number of Dirichlet characters modulo q is `ϕ(q)`, as a real inequality. -/
theorem card_odd_add_even (q : ℕ) [NeZero q] :
    ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ (-1) = -1)).card
      + ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => ¬ χ (-1) = -1)).card
      = q.totient := by
  rw [Finset.card_filter_add_card_filter_not, card_univ, ← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- PROVED: EP2022 p. 37, half of the characters modulo q are odd, so at most half of the
nonprincipal ones. -/
theorem card_odd_le (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    2 * ((((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => χ (-1) = -1)).card : ℝ) ≤ (q.totient : ℝ) := by
  have h1 := card_odd_eq_even q hq
  have h2 := card_odd_add_even q
  have h3 : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => χ (-1) = -1)).card
      ≤ ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ (-1) = -1)).card :=
    card_le_card (filter_subset_filter _ (erase_subset _ _))
  have : 2 * (((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => χ (-1) = -1)).card ≤ q.totient := by omega
  exact_mod_cast this

/-- LEAF: EP2022 Lemma 17 p. 15 under GRH, for the primitive `χ*` inducing an even
nonprincipal χ modulo q, with q in place of the modulus of `χ*`, p. 38. MEDIUM. -/
theorem lemma17 (hG : GRH) (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (heven : χ (-1) = 1) :
    ‖bChi χ.primitiveCharacter‖ < 2.751 * log q + 23.878 := by
  sorry

/-- LEAF: EP2022 Lemma 18 p. 16: for x ≥ 2 both trivial zero sums
`∑ x^(1-2m) / (2m-1)` and `∑ x^(-2m) / (2m)` are at most 1. MEDIUM. -/
theorem lemma18 {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) (hx : 2 ≤ x) :
    ‖trivSum χ x‖ ≤ 1 := by
  sorry

/-- PROVED: EP2022 p. 37, half of the characters modulo q are even, so at most half of
the nonprincipal ones. -/
theorem card_even_le (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    2 * ((((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => ¬ χ (-1) = -1)).card : ℝ) ≤ (q.totient : ℝ) := by
  have h1 := card_odd_eq_even q hq
  have h2 := card_odd_add_even q
  have h3 : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => ¬ χ (-1) = -1)).card
      ≤ ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => ¬ χ (-1) = -1)).card :=
    card_le_card (filter_subset_filter _ (erase_subset _ _))
  have : 2 * (((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
      (fun χ => ¬ χ (-1) = -1)).card ≤ q.totient := by omega
  exact_mod_cast this

/-- PROVED: EP2022 p. 38, Lemmas 17 and 18 summed over the nonprincipal characters: the
last two terms of (39) contribute at most `½ (log x + 2.751 log q + 23.878) + 1`. -/
theorem lemmas17_18_avg (hG : GRH) (q : ℕ) [NeZero q] (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    1 / (q.totient : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
        - trivSum χ.primitiveCharacter x‖
      ≤ 1 / 2 * (log x + 2.751 * log q + 23.878) + 1 := by
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hlogx : 0 ≤ log x := log_nonneg (by linarith)
  have hlogq : 0 ≤ log q := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  set L : ℝ := log x + 2.751 * log q + 23.878 with hL
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  set s := (univ : Finset (DirichletCharacter ℂ q)).erase 1 with hs
  have hterm : ∀ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
        - trivSum χ.primitiveCharacter x‖ ≤ (if ¬ χ (-1) = -1 then L else 0) + 1 := by
    intro χ hχ
    have hT := lemma18 χ.primitiveCharacter x hx
    unfold aChi
    by_cases h : χ (-1) = -1
    · rw [if_pos h, if_neg (not_not.2 h)]; simpa using hT
    · rw [if_neg h, if_pos h]
      have heven : χ (-1) = 1 := by
        have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        rcases mul_self_eq_one_iff.1 h2 with h' | h'
        · exact h'
        · exact absurd h' h
      have hb := lemma17 hG q hq χ (ne_of_mem_erase hχ) heven
      simp only [sub_zero, one_mul]
      have e1 : ‖((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖ ≤ ‖(Real.log x : ℂ)‖ + ‖bChi χ.primitiveCharacter‖
            + ‖trivSum χ.primitiveCharacter x‖ := by
        exact le_trans (norm_sub_le _ _) (by gcongr; exact norm_add_le _ _)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogx] at e1
      rw [hL]; linarith
  have hc := card_even_le q hq
  rw [← hs] at hc
  have hcs : (s.card : ℝ) ≤ q.totient := by
    have : s.card ≤ Fintype.card (DirichletCharacter ℂ q) :=
      le_trans (card_erase_le) (by rw [card_univ])
    have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h2 ▸ this
  calc 1 / (q.totient : ℝ) * ∑ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ)
          + bChi χ.primitiveCharacter) - trivSum χ.primitiveCharacter x‖
      ≤ 1 / (q.totient : ℝ) * ∑ χ ∈ s, ((if ¬ χ (-1) = -1 then L else 0) + 1) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = 1 / (q.totient : ℝ) * (((s.filter (fun χ => ¬ χ (-1) = -1)).card : ℝ) * L
          + (s.card : ℝ)) := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
          mul_one]
    _ ≤ 1 / (q.totient : ℝ) * ((q.totient : ℝ) / 2 * L + (q.totient : ℝ)) := by
        gcongr
        · linarith
    _ = 1 / 2 * L + 1 := by field_simp

/-- LEAF: EP2022 Lemma 21 p. 19, with Corollary 20 under GRH, for the primitive `χ*` inducing
an odd nonprincipal χ modulo q; its modulus is at least 3 and at most q. MEDIUM. -/
theorem lemma21 (hG : GRH) (q : ℕ) (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hodd : χ (-1) = -1) :
    ‖logDerivAt0 χ.primitiveCharacter‖ < lemma21RHS q := by
  sorry

/-- PROVED: EP2022 p. 38, Lemma 21 summed over the odd characters, at most half of all. -/
theorem lemma21_avg (hG : GRH) (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    1 / (q.totient : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖ ≤ lemma21RHS q / 2 := by
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hne : (-1 : ZMod q) ≠ 1 := by
    haveI : Fact (2 < q) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  obtain ⟨χ1, hχ1⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  have hχ1ne : χ1 ≠ 1 := fun h => hχ1 (by rw [h]; exact MulChar.one_apply isUnit_one.neg)
  have hχ1odd : χ1 (-1) = -1 := by
    have h2 : χ1 (-1) * χ1 (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
    rcases mul_self_eq_one_iff.1 h2 with h' | h'
    · exact absurd h' hχ1
    · exact h'
  have hB : 0 ≤ lemma21RHS q :=
    le_trans (norm_nonneg _) (lemma21 hG q hq χ1 hχ1ne hχ1odd).le
  have hterm : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
        ≤ if χ (-1) = -1 then lemma21RHS q else 0 := by
    intro χ hχ
    unfold aChi
    split_ifs with h
    · rw [one_mul]; exact (lemma21 hG q hq χ (ne_of_mem_erase hχ) h).le
    · simp
  have hc := card_odd_le q hq
  calc 1 / (q.totient : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      ≤ 1 / (q.totient : ℝ) * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        (if χ (-1) = -1 then lemma21RHS q else 0) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = 1 / (q.totient : ℝ) * (((((univ : Finset (DirichletCharacter ℂ q)).erase 1).filter
          (fun χ => χ (-1) = -1)).card : ℝ) * lemma21RHS q) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 1 / (q.totient : ℝ) * ((q.totient : ℝ) / 2 * lemma21RHS q) := by
        gcongr; linarith
    _ = lemma21RHS q / 2 := by field_simp

/-- LEAF: EP2022 pp. 38 to 40, the combination and simplification of all terms, with
`ϕ(q) ≥ 2`, `x^0.423 < 0.949 √x`, `log x / x^0.077 ≤ 4.778` and Lemma 9, down to the right
side of Theorem 3 with R1 q. A pure real inequality. MEDIUM. -/
theorem combine (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    (if q = 6 then 2 * log x else log q * log x) / (q.totient : ℝ)
      + (1 / (8 * π) * √x * log x ^ 2 + 2.6) / (q.totient : ℝ)
      + errPrim q x + zeroBound q x + (1 / 2 * (log x + 2.751 * log q + 23.878) + 1)
      + lemma21RHS q / 2 ≤ thm3RHS q x := by
  sorry

/-- PROVED: `ψ0(x, χ*)` from the residual of Theorem 29, by (39). -/
theorem psi0_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ‖psi0Chi χ.primitiveCharacter x‖ ≤ ‖residual χ x‖
      + ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      + ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖ := by
  have h : psi0Chi χ.primitiveCharacter x = residual χ x
      - aChi χ * logDerivAt0 χ.primitiveCharacter
      - ((1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x) := by
    unfold residual; ring
  rw [h]
  refine le_trans (norm_sub_le _ _) ?_
  gcongr
  exact norm_sub_le _ _

/-- PROVED: for `q ≥ 3` there is a nonprincipal character modulo q. -/
theorem exists_ne_one (q : ℕ) (hq : 3 ≤ q) :
    haveI : NeZero q := ⟨by omega⟩
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 := by
  haveI : NeZero q := ⟨by omega⟩
  have hne : (-1 : ZMod q) ≠ 1 := by
    haveI : Fact (2 < q) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  exact ⟨χ, fun h => hχ (by rw [h]; exact MulChar.one_apply isUnit_one.neg)⟩

/-- PROVED: EP2022 Theorem 3 p. 3, the exact statement of `ProgressionEPS70.thm3`, from
the LEAFs above. -/
theorem thm3_S76 (hG : GRH) (q a : ℕ) (x : ℝ) (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |psiAP q a x - x / (q.totient : ℝ)| < thm3RHS q x := by
  haveI : NeZero q := ⟨by omega⟩
  set φ : ℝ := (q.totient : ℝ) with hφ
  have hφpos : 0 < φ := by rw [hφ]; exact_mod_cast Nat.totient_pos.2 (by omega)
  have hlogx : 0 ≤ log x := log_nonneg (by linarith)
  have hlogq : 0 ≤ log q := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  set s := (univ : Finset (DirichletCharacter ℂ q)).erase 1 with hs
  have hu : IsUnit ((a : ZMod q)⁻¹) := by
    rw [← ZMod.coe_unitOfCoprime a ha, ZMod.inv_coe_unit]; exact Units.isUnit _
  -- display (8): split off the principal character
  have h8 := ortho q a x ha hq
  rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)),
    MulChar.one_apply hu, one_mul] at h8
  set S : ℂ := ∑ χ ∈ s, χ ((a : ZMod q)⁻¹) * psiChi χ x with hS
  have hW : (((psiAP q a x - x / φ : ℝ)) : ℂ) =
      (psiChi (1 : DirichletCharacter ℂ q) x - (psiR x : ℂ)) / (φ : ℂ)
      + ((psiR x - x : ℝ) : ℂ) / (φ : ℂ) + S / (φ : ℂ) := by
    have hφc : (φ : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
    push_cast; rw [h8, hφ]; push_cast; field_simp; ring
  have hnorm : |psiAP q a x - x / φ| ≤
      ‖psiChi (1 : DirichletCharacter ℂ q) x - (psiR x : ℂ)‖ / φ + |psiR x - x| / φ
        + ‖S‖ / φ := by
    have h := congrArg (‖·‖) hW
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    rw [h]
    refine le_trans (norm_add₃_le) ?_
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hφpos]
    exact le_refl _
  -- the nonprincipal characters
  have hSle : ‖S‖ ≤ ∑ χ ∈ s, ‖psiChi χ x‖ := by
    refine le_trans (norm_sum_le _ _) (sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    have := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
    have h0 := norm_nonneg (psiChi χ x)
    nlinarith
  have hZpos : 0 ≤ zeroBound q x := by
    obtain ⟨χ, hχ⟩ := exists_ne_one q hq
    exact le_trans (norm_nonneg _) (thm29_lemma30 hG q x hq hx χ hχ).le
  have herr : 0 ≤ errPrim q x := by unfold errPrim; split_ifs <;> positivity
  have hcard : (s.card : ℝ) ≤ φ := by
    have : s.card ≤ Fintype.card (DirichletCharacter ℂ q) :=
      le_trans (card_erase_le) (by rw [card_univ])
    have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [hφ]; exact_mod_cast h2 ▸ this
  have hsum : ∑ χ ∈ s, ‖psiChi χ x‖ ≤ φ * (zeroBound q x + errPrim q x)
      + ∑ χ ∈ s, ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      + ∑ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖ := by
    have h1 : ∑ χ ∈ s, ‖psiChi χ x‖ ≤ ∑ χ ∈ s, ((zeroBound q x + errPrim q x)
        + ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
        + ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖) := by
      refine sum_le_sum fun χ hχ => ?_
      have hχ1 : χ ≠ 1 := ne_of_mem_erase hχ
      have := reduce_primitive q x hq hx χ
      have := psi0_norm_le χ x
      have := thm29_lemma30 hG q x hq hx χ hχ1
      linarith
    rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul] at h1
    have : (s.card : ℝ) * (zeroBound q x + errPrim q x) ≤ φ * (zeroBound q x + errPrim q x) :=
      mul_le_mul_of_nonneg_right hcard (by linarith)
    linarith
  have hL17 := lemmas17_18_avg hG q x hq hx
  have hL21 := lemma21_avg hG q hq
  have hP := principal_lemma12 q x hq hx
  have hR := psi_RH hG x hx
  have hC := combine q x hq hx
  rw [← hφ] at hL17 hL21 hC
  have hdiv1 : ‖psiChi (1 : DirichletCharacter ℂ q) x - (psiR x : ℂ)‖ / φ ≤
      (if q = 6 then 2 * log x else log q * log x) / φ :=
    div_le_div_of_nonneg_right hP hφpos.le
  have hdiv2 : |psiR x - x| / φ < (1 / (8 * π) * √x * log x ^ 2 + 2.6) / φ :=
    div_lt_div_of_pos_right hR hφpos
  have hdiv3 : ‖S‖ / φ ≤ (zeroBound q x + errPrim q x)
      + 1 / φ * ∑ χ ∈ s, ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      + 1 / φ * ∑ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖ := by
    rw [div_le_iff₀ hφpos]
    have : (zeroBound q x + errPrim q x
      + 1 / φ * ∑ χ ∈ s, ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      + 1 / φ * ∑ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖) * φ = φ * (zeroBound q x + errPrim q x)
      + ∑ χ ∈ s, ‖aChi χ * logDerivAt0 χ.primitiveCharacter‖
      + ∑ χ ∈ s, ‖(1 - aChi χ) * ((Real.log x : ℂ) + bChi χ.primitiveCharacter)
          - trivSum χ.primitiveCharacter x‖ := by
      field_simp
    rw [this]; linarith
  linarith

end

end LeanLab.BS2022GRH.ProgressionThm3S76

#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.thm3_S76
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.psi0_norm_le
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.ortho
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.formula9
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.lemma13
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.psi_RH
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.card_odd_le
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.card_even_le
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.lemma21_avg
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.lemmas17_18_avg
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.principal_eq
#print axioms LeanLab.BS2022GRH.ProgressionThm3S76.exists_ne_one
