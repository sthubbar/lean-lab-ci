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

/-- PROVED in S114, was a LEAF: EP2022 Lemma 12 p. 13, first half of its proof: the sum of `Λ(n)` over `n ≤ x` with
`(n, q) > 1` is the sum over primes `p | q` of `log p` times the number of powers `p^v ≤ x`,
at most `log x` for each p. MEDIUM. -/
theorem lemma12_omega (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q), (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ (q.primeFactors.card : ℝ) * log x := by
  set S := (Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q) with hS
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hlogN : log (⌊x⌋₊ : ℝ) ≤ log x :=
    log_le_log (by exact_mod_cast hN) (Nat.floor_le (by linarith))
  rw [← Finset.sum_filter_of_ne (p := fun n => IsPrimePow n)
    (fun n _ h => by
      by_contra hc; exact h (by simp [ArithmeticFunction.vonMangoldt_apply, hc]))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.minFac) (t := q.primeFactors)]
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfib : ∀ n ∈ (S.filter (fun n => IsPrimePow n)).filter (fun n => n.minFac = p),
        (ArithmeticFunction.vonMangoldt n : ℝ) = log p := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      simp only [ArithmeticFunction.vonMangoldt_apply, hn.1.2, hn.2, ite_true]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
    set K := Nat.log p ⌊x⌋₊
    have hsub : (S.filter (fun n => IsPrimePow n)).filter (fun n => n.minFac = p) ⊆
        (Icc 1 K).image (fun k => p ^ k) := by
      intro n hn
      simp only [Finset.mem_filter, hS, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, hpow⟩, hmin⟩ := hn
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpow
      rw [Nat.Prime.pow_minFac hr hk.ne'] at hmin
      subst hmin
      simp only [Finset.mem_image, Finset.mem_Icc]
      exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hr.one_lt h2⟩, rfl⟩
    have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hpp.one_lt.le)
    calc _ ≤ (K : ℝ) * log p := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlp
      _ = log ((p ^ K : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
      _ ≤ log (⌊x⌋₊ : ℝ) := log_le_log (by exact_mod_cast pow_pos hpp.pos _)
            (by exact_mod_cast Nat.pow_log_le_self p (by omega))
      _ ≤ log x := hlogN
  · intro n hn
    simp only [Finset.mem_filter, hS, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨_, _⟩, hcop⟩, hpow⟩ := hn
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpow
    rw [Nat.Prime.pow_minFac hr hk.ne']
    rw [Nat.mem_primeFactors]
    refine ⟨hr, ?_, by omega⟩
    by_contra hd
    exact hcop (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))

/-- PROVED in S114, was a LEAF: EP2022 Lemma 12 p. 13, second half of its proof: for `q ≥ 3`, `q ≠ 6`, the number
k of prime factors of q satisfies `k ≤ log q`. EASY. -/
theorem lemma12_card_le_log (q : ℕ) (hq : 3 ≤ q) (h6 : q ≠ 6) :
    (q.primeFactors.card : ℝ) ≤ log q := by
  have hq0 : (0:ℝ) < q := by have : 0 < q := by omega
                             exact_mod_cast this
  have he3 : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he2 : 2 < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : 0 < exp 1 := exp_pos 1
  have hP : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hT : ∀ T ⊆ q.primeFactors, 2 ∉ T → exp 1 ^ T.card ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
    intro T hTS h2
    rw [Nat.cast_prod, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => he0.le) (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hTS hp)
    have hp3 : 3 ≤ p := by
      have := hpp.two_le
      rcases Nat.lt_or_ge p 3 with h | h
      · exact absurd (show p = 2 by omega ▸ hp) h2
      · exact h
    have : (3:ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  by_cases hk : q.primeFactors.card ≤ 1
  · have : (q.primeFactors.card:ℝ) ≤ 1 := by exact_mod_cast hk
    have : 1 ≤ log q := by
      rw [Real.le_log_iff_exp_le hq0]
      have : (3:ℝ) ≤ q := by exact_mod_cast hq
      linarith
    linarith
  rw [Real.le_log_iff_exp_le hq0, ← Real.exp_one_pow]
  by_cases h2 : 2 ∈ q.primeFactors
  · have hTc : (q.primeFactors.erase 2).card + 1 = q.primeFactors.card :=
      Finset.card_erase_add_one h2
    have hSP : ∏ p ∈ q.primeFactors, p = 2 * ∏ p ∈ q.primeFactors.erase 2, p :=
      (Finset.mul_prod_erase q.primeFactors (fun p => p) h2).symm
    by_cases h5 : ∃ p ∈ q.primeFactors.erase 2, 5 ≤ p
    · obtain ⟨p, hpT, hp5⟩ := h5
      have hUc : ((q.primeFactors.erase 2).erase p).card + 1 = (q.primeFactors.erase 2).card :=
        Finset.card_erase_add_one hpT
      have hTP : ∏ p ∈ q.primeFactors.erase 2, p = p * ∏ p ∈ (q.primeFactors.erase 2).erase p, p :=
        (Finset.mul_prod_erase _ (fun p => p) hpT).symm
      have hU := hT ((q.primeFactors.erase 2).erase p)
        (fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
        (fun h => by
          have := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h)
          exact this rfl)
      have hX : (0:ℝ) ≤ ((∏ p ∈ (q.primeFactors.erase 2).erase p, p : ℕ) : ℝ) := by positivity
      have he10 : exp 1 ^ 2 ≤ 10 := by nlinarith
      have hp5' : (5:ℝ) ≤ p := by exact_mod_cast hp5
      calc exp 1 ^ q.primeFactors.card
          = exp 1 ^ 2 * exp 1 ^ ((q.primeFactors.erase 2).erase p).card := by
            rw [← pow_add]; congr 1; omega
        _ ≤ 10 * ((∏ p ∈ (q.primeFactors.erase 2).erase p, p : ℕ) : ℝ) :=
            mul_le_mul he10 hU (by positivity) (by norm_num)
        _ ≤ ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
            rw [hSP, hTP, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]; nlinarith
        _ ≤ q := hP
    · push Not at h5
      have hTsub : q.primeFactors.erase 2 ⊆ {3} := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
        have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
        have := hpp.two_le
        have := h5 p hp
        rcases (show p = 3 ∨ p = 4 by omega) with h | h
        · simp [h]
        · exact absurd (h ▸ hpp) (by decide)
      have hTcard : (q.primeFactors.erase 2).card ≤ 1 :=
        (Finset.card_le_card hTsub).trans (by simp)
      have hpos : 0 < (q.primeFactors.erase 2).card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      have hx3 : x = 3 := by simpa using hTsub hx
      subst hx3
      have h3 : 3 ∣ q := Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hx)
      have h2' : 2 ∣ q := Nat.dvd_of_mem_primeFactors h2
      have hc : q.primeFactors.card = 2 := by omega
      have h12 : 12 ≤ q := by omega
      have h12' : (12:ℝ) ≤ q := by exact_mod_cast h12
      rw [hc]; nlinarith
  · exact (hT _ subset_rfl h2).trans hP

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

/-- One prime power step of psi at integers: `ψ(m) = ψ(m - 1) + log p` when `m` is a power of `p`. -/
private lemma sageS114_pp (k m p : ℕ) {a b c d a' b' : ℝ}
    (h : a < psiR (k : ℝ) ∧ psiR (k : ℝ) < b) (hp : c < Real.log (p : ℝ) ∧ Real.log (p : ℝ) < d)
    (hkm : k + 1 = m := by norm_num) (hk : IsPrimePow m := by decide +kernel)
    (hmf : m.minFac = p := by norm_num) (ha : a' ≤ a + c := by norm_num)
    (hb : b + d ≤ b' := by norm_num) :
    a' < psiR (m : ℝ) ∧ psiR (m : ℝ) < b' := by
  have e : psiR (m : ℝ) = psiR (k : ℝ) + Real.log (p : ℝ) := by
    subst hkm hmf
    unfold psiR
    rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega),
      ArithmeticFunction.vonMangoldt_apply]
    simp only [hk, ↓reduceIte]
  rw [e]; constructor <;> linarith [h.1, h.2, hp.1, hp.2]

/-- One step of psi at an integer `m` that is not a prime power: `ψ(m) = ψ(m - 1)`. -/
private lemma sageS114_np (k m : ℕ) {a b : ℝ} (h : a < psiR (k : ℝ) ∧ psiR (k : ℝ) < b)
    (hkm : k + 1 = m := by norm_num) (hk : ¬ IsPrimePow m := by decide +kernel) :
    a < psiR (m : ℝ) ∧ psiR (m : ℝ) < b := by
  have e : psiR (m : ℝ) = psiR (k : ℝ) := by
    subst hkm
    unfold psiR
    rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (by omega),
      ArithmeticFunction.vonMangoldt_apply]
    simp only [hk, ↓reduceIte, add_zero]
  rw [e]; exact h

/-- The Sage check at one integer `N` from rational enclosures of `ψ(N)`, `√N` and `log N`. -/
private lemma sageS114_fin (N : ℕ) (s l c : ℝ) {a b : ℝ}
    (hP : a < psiR (N : ℝ) ∧ psiR (N : ℝ) < b) (hlN : l ≤ Real.log (N : ℝ))
    (hs : 0 ≤ s := by norm_num) (hsN : s ^ 2 ≤ (N : ℝ) := by norm_num) (hl : 0 ≤ l := by norm_num)
    (hc : c ≤ s * l ^ 2 / (8 * 3.1416) := by norm_num) (h1 : b - N < c + 1.6 := by norm_num)
    (h2 : (N : ℝ) - a < c + 1.6 := by norm_num) :
    |psiR (N : ℝ) - N| < 1 / (8 * π) * √(N : ℝ) * Real.log (N : ℝ) ^ 2 + 1.6 := by
  have hpi : 0 < π := Real.pi_pos
  have hsx : s ≤ √(N : ℝ) := (Real.le_sqrt hs (Nat.cast_nonneg N)).mpr hsN
  have h1' : 1 / (8 * 3.1416) ≤ 1 / (8 * π) := by
    apply one_div_le_one_div_of_le (by positivity); linarith [Real.pi_lt_d4]
  have h2' : l ^ 2 ≤ Real.log (N : ℝ) ^ 2 := pow_le_pow_left₀ hl hlN 2
  have h3 : s * l ^ 2 ≤ √(N : ℝ) * Real.log (N : ℝ) ^ 2 :=
    mul_le_mul hsx h2' (by positivity) (by positivity)
  have hf : c ≤ 1 / (8 * π) * √(N : ℝ) * Real.log (N : ℝ) ^ 2 :=
    calc c ≤ s * l ^ 2 / (8 * 3.1416) := hc
      _ = 1 / (8 * 3.1416) * (s * l ^ 2) := by ring
      _ ≤ 1 / (8 * π) * (√(N : ℝ) * Real.log (N : ℝ) ^ 2) :=
          mul_le_mul h1' h3 (by positivity) (by positivity)
      _ = _ := by ring
  rw [abs_lt]; constructor <;> linarith [hP.1, hP.2]

/-- Mathlib's enclosure of `log 2`. -/
private lemma sageS114_log2 : (0.6931471 : ℝ) < Real.log 2 ∧ Real.log 2 < (0.6931472 : ℝ) :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

/-- `log 3` from the atanh series at `1 / 5`. -/
private lemma sageS114_log3 : (1.0986122 : ℝ) < Real.log 3 ∧ Real.log 3 < (1.0986124 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 5 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (3 : ℝ) = Real.log ((3 : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2]

/-- `log 5` from the atanh series at `1 / 9`. -/
private lemma sageS114_log5 : (1.6094377 : ℝ) < Real.log 5 ∧ Real.log 5 < (1.6094380 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 9 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (5 : ℝ) = Real.log ((5 : ℝ) / 4) + Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (4:ℝ) = 2 * Real.log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2]

/-- `log 7` from the atanh series at `1 / 13`. -/
private lemma sageS114_log7 : (1.9459099 : ℝ) < Real.log 7 ∧ Real.log 7 < (1.9459103 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 13 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (7 : ℝ) = Real.log ((7 : ℝ) / 6) + Real.log 6 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2]

/-- `log 11` from the atanh series at `1 / 21`. -/
private lemma sageS114_log11 : (2.3978949 : ℝ) < Real.log 11 ∧ Real.log 11 < (2.3978954 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 21 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (11 : ℝ) = Real.log ((11 : ℝ) / 10) + Real.log 10 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by rw [show (10:ℝ) = 2 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2]

/-- `log 13` from the atanh series at `1 / 25`. -/
private lemma sageS114_log13 : (2.5649491 : ℝ) < Real.log 13 ∧ Real.log 13 < (2.5649496 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 25 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (13 : ℝ) = Real.log ((13 : ℝ) / 12) + Real.log 12 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (12:ℝ) = 2 * Real.log 2 + Real.log 3 := by rw [show (12:ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2]

/-- `log 17` from the atanh series at `1 / 33`. -/
private lemma sageS114_log17 : (2.8332130 : ℝ) < Real.log 17 ∧ Real.log 17 < (2.8332135 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 33 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (17 : ℝ) = Real.log ((17 : ℝ) / 16) + Real.log 16 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (16:ℝ) = 4 * Real.log 2 := by rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2]

/-- `log 19` from the atanh series at `1 / 37`. -/
private lemma sageS114_log19 : (2.9444387 : ℝ) < Real.log 19 ∧ Real.log 19 < (2.9444393 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 37 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (19 : ℝ) = Real.log ((19 : ℝ) / 18) + Real.log 18 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (18:ℝ) = Real.log 2 + 2 * Real.log 3 := by rw [show (18:ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2]

/-- `log 23` from the atanh series at `1 / 45`. -/
private lemma sageS114_log23 : (3.1354937 : ℝ) < Real.log 23 ∧ Real.log 23 < (3.1354944 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 45 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (23 : ℝ) = Real.log ((23 : ℝ) / 22) + Real.log 22 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (22:ℝ) = Real.log 2 + Real.log 11 := by rw [show (22:ℝ) = 2 * 11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log11.1, sageS114_log11.2]

/-- `log 29` from the atanh series at `1 / 57`. -/
private lemma sageS114_log29 : (3.3672954 : ℝ) < Real.log 29 ∧ Real.log 29 < (3.3672961 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 57 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (29 : ℝ) = Real.log ((29 : ℝ) / 28) + Real.log 28 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (28:ℝ) = 2 * Real.log 2 + Real.log 7 := by rw [show (28:ℝ) = 2^2 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log7.1, sageS114_log7.2]

/-- `log 31` from the atanh series at `1 / 61`. -/
private lemma sageS114_log31 : (3.4339868 : ℝ) < Real.log 31 ∧ Real.log 31 < (3.4339875 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 61 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (31 : ℝ) = Real.log ((31 : ℝ) / 30) + Real.log 30 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (30:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by rw [show (30:ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2]

/-- `log 37` from the atanh series at `1 / 73`. -/
private lemma sageS114_log37 : (3.6109175 : ℝ) < Real.log 37 ∧ Real.log 37 < (3.6109182 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 73 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (37 : ℝ) = Real.log ((37 : ℝ) / 36) + Real.log 36 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (36:ℝ) = 2 * Real.log 2 + 2 * Real.log 3 := by rw [show (36:ℝ) = 2^2 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2]

/-- `log 41` from the atanh series at `1 / 81`. -/
private lemma sageS114_log41 : (3.7135716 : ℝ) < Real.log 41 ∧ Real.log 41 < (3.7135723 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 81 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (41 : ℝ) = Real.log ((41 : ℝ) / 40) + Real.log 40 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (40:ℝ) = 3 * Real.log 2 + Real.log 5 := by rw [show (40:ℝ) = 2^3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2]

/-- `log 43` from the atanh series at `1 / 85`. -/
private lemma sageS114_log43 : (3.7611996 : ℝ) < Real.log 43 ∧ Real.log 43 < (3.7612004 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 85 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (43 : ℝ) = Real.log ((43 : ℝ) / 42) + Real.log 42 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (42:ℝ) = Real.log 2 + Real.log 3 + Real.log 7 := by rw [show (42:ℝ) = 2 * 3 * 7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log7.1, sageS114_log7.2]

/-- `log 47` from the atanh series at `1 / 93`. -/
private lemma sageS114_log47 : (3.8501470 : ℝ) < Real.log 47 ∧ Real.log 47 < (3.8501479 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 93 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (47 : ℝ) = Real.log ((47 : ℝ) / 46) + Real.log 46 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (46:ℝ) = Real.log 2 + Real.log 23 := by rw [show (46:ℝ) = 2 * 23 by norm_num, Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log23.1, sageS114_log23.2]

/-- `log 53` from the atanh series at `1 / 105`. -/
private lemma sageS114_log53 : (3.9702914 : ℝ) < Real.log 53 ∧ Real.log 53 < (3.9702922 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 105 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (53 : ℝ) = Real.log ((53 : ℝ) / 52) + Real.log 52 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (52:ℝ) = 2 * Real.log 2 + Real.log 13 := by rw [show (52:ℝ) = 2^2 * 13 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log13.1, sageS114_log13.2]

/-- `log 59` from the atanh series at `1 / 117`. -/
private lemma sageS114_log59 : (4.0775369 : ℝ) < Real.log 59 ∧ Real.log 59 < (4.0775378 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 117 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (59 : ℝ) = Real.log ((59 : ℝ) / 58) + Real.log 58 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (58:ℝ) = Real.log 2 + Real.log 29 := by rw [show (58:ℝ) = 2 * 29 by norm_num, Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log29.1, sageS114_log29.2]

/-- `log 61` from the atanh series at `1 / 121`. -/
private lemma sageS114_log61 : (4.1108734 : ℝ) < Real.log 61 ∧ Real.log 61 < (4.1108742 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 121 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (61 : ℝ) = Real.log ((61 : ℝ) / 60) + Real.log 60 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (60:ℝ) = 2 * Real.log 2 + Real.log 3 + Real.log 5 := by rw [show (60:ℝ) = 2^2 * 3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2]

/-- `log 67` from the atanh series at `1 / 133`. -/
private lemma sageS114_log67 : (4.2046920 : ℝ) < Real.log 67 ∧ Real.log 67 < (4.2046929 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 133 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (67 : ℝ) = Real.log ((67 : ℝ) / 66) + Real.log 66 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (66:ℝ) = Real.log 2 + Real.log 3 + Real.log 11 := by rw [show (66:ℝ) = 2 * 3 * 11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log11.1, sageS114_log11.2]

/-- `log 71` from the atanh series at `1 / 141`. -/
private lemma sageS114_log71 : (4.2626793 : ℝ) < Real.log 71 ∧ Real.log 71 < (4.2626802 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 141 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (71 : ℝ) = Real.log ((71 : ℝ) / 70) + Real.log 70 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (70:ℝ) = Real.log 2 + Real.log 5 + Real.log 7 := by rw [show (70:ℝ) = 2 * 5 * 7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2, sageS114_log7.1, sageS114_log7.2]

/-- `log 73` from the atanh series at `1 / 145`. -/
private lemma sageS114_log73 : (4.2904590 : ℝ) < Real.log 73 ∧ Real.log 73 < (4.2904598 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (x := (1 / 145 : ℝ)) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have hl : Real.log (73 : ℝ) = Real.log ((73 : ℝ) / 72) + Real.log 72 := by
    rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have hm : Real.log (72:ℝ) = 3 * Real.log 2 + 2 * Real.log 3 := by rw [show (72:ℝ) = 2^3 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]
  obtain ⟨ha, hb⟩ := abs_le.mp h
  constructor <;> linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2]

/-- psi at one. -/
private lemma sageS114_q1 : (-0.0000001 : ℝ) < psiR ((1:ℕ):ℝ) ∧ psiR ((1:ℕ):ℝ) < (0.0000001 : ℝ) := by
  unfold psiR; norm_num

/-- psi at 2. -/
private lemma sageS114_q2 : (0.6931470 : ℝ) < psiR ((2:ℕ):ℝ) ∧ psiR ((2:ℕ):ℝ) < (0.6931473 : ℝ) :=
  sageS114_pp 1 2 2 sageS114_q1 sageS114_log2

/-- psi at 3. -/
private lemma sageS114_q3 : (1.7917592 : ℝ) < psiR ((3:ℕ):ℝ) ∧ psiR ((3:ℕ):ℝ) < (1.7917597 : ℝ) :=
  sageS114_pp 2 3 3 sageS114_q2 sageS114_log3

/-- psi at 4. -/
private lemma sageS114_q4 : (2.4849063 : ℝ) < psiR ((4:ℕ):ℝ) ∧ psiR ((4:ℕ):ℝ) < (2.4849069 : ℝ) :=
  sageS114_pp 3 4 2 sageS114_q3 sageS114_log2

/-- psi at 5. -/
private lemma sageS114_q5 : (4.0943440 : ℝ) < psiR ((5:ℕ):ℝ) ∧ psiR ((5:ℕ):ℝ) < (4.0943449 : ℝ) :=
  sageS114_pp 4 5 5 sageS114_q4 sageS114_log5

/-- psi at 6. -/
private lemma sageS114_q6 : (4.0943440 : ℝ) < psiR ((6:ℕ):ℝ) ∧ psiR ((6:ℕ):ℝ) < (4.0943449 : ℝ) :=
  sageS114_np 5 6 sageS114_q5

/-- psi at 7. -/
private lemma sageS114_q7 : (6.0402539 : ℝ) < psiR ((7:ℕ):ℝ) ∧ psiR ((7:ℕ):ℝ) < (6.0402552 : ℝ) :=
  sageS114_pp 6 7 7 sageS114_q6 sageS114_log7

/-- psi at 8. -/
private lemma sageS114_q8 : (6.7334010 : ℝ) < psiR ((8:ℕ):ℝ) ∧ psiR ((8:ℕ):ℝ) < (6.7334024 : ℝ) :=
  sageS114_pp 7 8 2 sageS114_q7 sageS114_log2

/-- psi at 9. -/
private lemma sageS114_q9 : (7.8320132 : ℝ) < psiR ((9:ℕ):ℝ) ∧ psiR ((9:ℕ):ℝ) < (7.8320148 : ℝ) :=
  sageS114_pp 8 9 3 sageS114_q8 sageS114_log3

/-- psi at 10. -/
private lemma sageS114_q10 : (7.8320132 : ℝ) < psiR ((10:ℕ):ℝ) ∧ psiR ((10:ℕ):ℝ) < (7.8320148 : ℝ) :=
  sageS114_np 9 10 sageS114_q9

/-- psi at 11. -/
private lemma sageS114_q11 : (10.2299081 : ℝ) < psiR ((11:ℕ):ℝ) ∧ psiR ((11:ℕ):ℝ) < (10.2299102 : ℝ) :=
  sageS114_pp 10 11 11 sageS114_q10 sageS114_log11

/-- psi at 12. -/
private lemma sageS114_q12 : (10.2299081 : ℝ) < psiR ((12:ℕ):ℝ) ∧ psiR ((12:ℕ):ℝ) < (10.2299102 : ℝ) :=
  sageS114_np 11 12 sageS114_q11

/-- psi at 13. -/
private lemma sageS114_q13 : (12.7948572 : ℝ) < psiR ((13:ℕ):ℝ) ∧ psiR ((13:ℕ):ℝ) < (12.7948598 : ℝ) :=
  sageS114_pp 12 13 13 sageS114_q12 sageS114_log13

/-- psi at 14. -/
private lemma sageS114_q14 : (12.7948572 : ℝ) < psiR ((14:ℕ):ℝ) ∧ psiR ((14:ℕ):ℝ) < (12.7948598 : ℝ) :=
  sageS114_np 13 14 sageS114_q13

/-- psi at 15. -/
private lemma sageS114_q15 : (12.7948572 : ℝ) < psiR ((15:ℕ):ℝ) ∧ psiR ((15:ℕ):ℝ) < (12.7948598 : ℝ) :=
  sageS114_np 14 15 sageS114_q14

/-- psi at 16. -/
private lemma sageS114_q16 : (13.4880043 : ℝ) < psiR ((16:ℕ):ℝ) ∧ psiR ((16:ℕ):ℝ) < (13.4880070 : ℝ) :=
  sageS114_pp 15 16 2 sageS114_q15 sageS114_log2

/-- psi at 17. -/
private lemma sageS114_q17 : (16.3212173 : ℝ) < psiR ((17:ℕ):ℝ) ∧ psiR ((17:ℕ):ℝ) < (16.3212205 : ℝ) :=
  sageS114_pp 16 17 17 sageS114_q16 sageS114_log17

/-- psi at 18. -/
private lemma sageS114_q18 : (16.3212173 : ℝ) < psiR ((18:ℕ):ℝ) ∧ psiR ((18:ℕ):ℝ) < (16.3212205 : ℝ) :=
  sageS114_np 17 18 sageS114_q17

/-- psi at 19. -/
private lemma sageS114_q19 : (19.2656560 : ℝ) < psiR ((19:ℕ):ℝ) ∧ psiR ((19:ℕ):ℝ) < (19.2656598 : ℝ) :=
  sageS114_pp 18 19 19 sageS114_q18 sageS114_log19

/-- psi at 20. -/
private lemma sageS114_q20 : (19.2656560 : ℝ) < psiR ((20:ℕ):ℝ) ∧ psiR ((20:ℕ):ℝ) < (19.2656598 : ℝ) :=
  sageS114_np 19 20 sageS114_q19

/-- psi at 21. -/
private lemma sageS114_q21 : (19.2656560 : ℝ) < psiR ((21:ℕ):ℝ) ∧ psiR ((21:ℕ):ℝ) < (19.2656598 : ℝ) :=
  sageS114_np 20 21 sageS114_q20

/-- psi at 22. -/
private lemma sageS114_q22 : (19.2656560 : ℝ) < psiR ((22:ℕ):ℝ) ∧ psiR ((22:ℕ):ℝ) < (19.2656598 : ℝ) :=
  sageS114_np 21 22 sageS114_q21

/-- psi at 23. -/
private lemma sageS114_q23 : (22.4011497 : ℝ) < psiR ((23:ℕ):ℝ) ∧ psiR ((23:ℕ):ℝ) < (22.4011542 : ℝ) :=
  sageS114_pp 22 23 23 sageS114_q22 sageS114_log23

/-- psi at 24. -/
private lemma sageS114_q24 : (22.4011497 : ℝ) < psiR ((24:ℕ):ℝ) ∧ psiR ((24:ℕ):ℝ) < (22.4011542 : ℝ) :=
  sageS114_np 23 24 sageS114_q23

/-- psi at 25. -/
private lemma sageS114_q25 : (24.0105874 : ℝ) < psiR ((25:ℕ):ℝ) ∧ psiR ((25:ℕ):ℝ) < (24.0105922 : ℝ) :=
  sageS114_pp 24 25 5 sageS114_q24 sageS114_log5

/-- psi at 26. -/
private lemma sageS114_q26 : (24.0105874 : ℝ) < psiR ((26:ℕ):ℝ) ∧ psiR ((26:ℕ):ℝ) < (24.0105922 : ℝ) :=
  sageS114_np 25 26 sageS114_q25

/-- psi at 27. -/
private lemma sageS114_q27 : (25.1091996 : ℝ) < psiR ((27:ℕ):ℝ) ∧ psiR ((27:ℕ):ℝ) < (25.1092046 : ℝ) :=
  sageS114_pp 26 27 3 sageS114_q26 sageS114_log3

/-- psi at 28. -/
private lemma sageS114_q28 : (25.1091996 : ℝ) < psiR ((28:ℕ):ℝ) ∧ psiR ((28:ℕ):ℝ) < (25.1092046 : ℝ) :=
  sageS114_np 27 28 sageS114_q27

/-- psi at 29. -/
private lemma sageS114_q29 : (28.4764950 : ℝ) < psiR ((29:ℕ):ℝ) ∧ psiR ((29:ℕ):ℝ) < (28.4765007 : ℝ) :=
  sageS114_pp 28 29 29 sageS114_q28 sageS114_log29

/-- psi at 30. -/
private lemma sageS114_q30 : (28.4764950 : ℝ) < psiR ((30:ℕ):ℝ) ∧ psiR ((30:ℕ):ℝ) < (28.4765007 : ℝ) :=
  sageS114_np 29 30 sageS114_q29

/-- psi at 31. -/
private lemma sageS114_q31 : (31.9104818 : ℝ) < psiR ((31:ℕ):ℝ) ∧ psiR ((31:ℕ):ℝ) < (31.9104882 : ℝ) :=
  sageS114_pp 30 31 31 sageS114_q30 sageS114_log31

/-- psi at 32. -/
private lemma sageS114_q32 : (32.6036289 : ℝ) < psiR ((32:ℕ):ℝ) ∧ psiR ((32:ℕ):ℝ) < (32.6036354 : ℝ) :=
  sageS114_pp 31 32 2 sageS114_q31 sageS114_log2

/-- psi at 33. -/
private lemma sageS114_q33 : (32.6036289 : ℝ) < psiR ((33:ℕ):ℝ) ∧ psiR ((33:ℕ):ℝ) < (32.6036354 : ℝ) :=
  sageS114_np 32 33 sageS114_q32

/-- psi at 34. -/
private lemma sageS114_q34 : (32.6036289 : ℝ) < psiR ((34:ℕ):ℝ) ∧ psiR ((34:ℕ):ℝ) < (32.6036354 : ℝ) :=
  sageS114_np 33 34 sageS114_q33

/-- psi at 35. -/
private lemma sageS114_q35 : (32.6036289 : ℝ) < psiR ((35:ℕ):ℝ) ∧ psiR ((35:ℕ):ℝ) < (32.6036354 : ℝ) :=
  sageS114_np 34 35 sageS114_q34

/-- psi at 36. -/
private lemma sageS114_q36 : (32.6036289 : ℝ) < psiR ((36:ℕ):ℝ) ∧ psiR ((36:ℕ):ℝ) < (32.6036354 : ℝ) :=
  sageS114_np 35 36 sageS114_q35

/-- psi at 37. -/
private lemma sageS114_q37 : (36.2145464 : ℝ) < psiR ((37:ℕ):ℝ) ∧ psiR ((37:ℕ):ℝ) < (36.2145536 : ℝ) :=
  sageS114_pp 36 37 37 sageS114_q36 sageS114_log37

/-- psi at 38. -/
private lemma sageS114_q38 : (36.2145464 : ℝ) < psiR ((38:ℕ):ℝ) ∧ psiR ((38:ℕ):ℝ) < (36.2145536 : ℝ) :=
  sageS114_np 37 38 sageS114_q37

/-- psi at 39. -/
private lemma sageS114_q39 : (36.2145464 : ℝ) < psiR ((39:ℕ):ℝ) ∧ psiR ((39:ℕ):ℝ) < (36.2145536 : ℝ) :=
  sageS114_np 38 39 sageS114_q38

/-- psi at 40. -/
private lemma sageS114_q40 : (36.2145464 : ℝ) < psiR ((40:ℕ):ℝ) ∧ psiR ((40:ℕ):ℝ) < (36.2145536 : ℝ) :=
  sageS114_np 39 40 sageS114_q39

/-- psi at 41. -/
private lemma sageS114_q41 : (39.9281180 : ℝ) < psiR ((41:ℕ):ℝ) ∧ psiR ((41:ℕ):ℝ) < (39.9281259 : ℝ) :=
  sageS114_pp 40 41 41 sageS114_q40 sageS114_log41

/-- psi at 42. -/
private lemma sageS114_q42 : (39.9281180 : ℝ) < psiR ((42:ℕ):ℝ) ∧ psiR ((42:ℕ):ℝ) < (39.9281259 : ℝ) :=
  sageS114_np 41 42 sageS114_q41

/-- psi at 43. -/
private lemma sageS114_q43 : (43.6893176 : ℝ) < psiR ((43:ℕ):ℝ) ∧ psiR ((43:ℕ):ℝ) < (43.6893263 : ℝ) :=
  sageS114_pp 42 43 43 sageS114_q42 sageS114_log43

/-- psi at 44. -/
private lemma sageS114_q44 : (43.6893176 : ℝ) < psiR ((44:ℕ):ℝ) ∧ psiR ((44:ℕ):ℝ) < (43.6893263 : ℝ) :=
  sageS114_np 43 44 sageS114_q43

/-- psi at 45. -/
private lemma sageS114_q45 : (43.6893176 : ℝ) < psiR ((45:ℕ):ℝ) ∧ psiR ((45:ℕ):ℝ) < (43.6893263 : ℝ) :=
  sageS114_np 44 45 sageS114_q44

/-- psi at 46. -/
private lemma sageS114_q46 : (43.6893176 : ℝ) < psiR ((46:ℕ):ℝ) ∧ psiR ((46:ℕ):ℝ) < (43.6893263 : ℝ) :=
  sageS114_np 45 46 sageS114_q45

/-- psi at 47. -/
private lemma sageS114_q47 : (47.5394646 : ℝ) < psiR ((47:ℕ):ℝ) ∧ psiR ((47:ℕ):ℝ) < (47.5394742 : ℝ) :=
  sageS114_pp 46 47 47 sageS114_q46 sageS114_log47

/-- psi at 48. -/
private lemma sageS114_q48 : (47.5394646 : ℝ) < psiR ((48:ℕ):ℝ) ∧ psiR ((48:ℕ):ℝ) < (47.5394742 : ℝ) :=
  sageS114_np 47 48 sageS114_q47

/-- psi at 49. -/
private lemma sageS114_q49 : (49.4853745 : ℝ) < psiR ((49:ℕ):ℝ) ∧ psiR ((49:ℕ):ℝ) < (49.4853845 : ℝ) :=
  sageS114_pp 48 49 7 sageS114_q48 sageS114_log7

/-- psi at 50. -/
private lemma sageS114_q50 : (49.4853745 : ℝ) < psiR ((50:ℕ):ℝ) ∧ psiR ((50:ℕ):ℝ) < (49.4853845 : ℝ) :=
  sageS114_np 49 50 sageS114_q49

/-- psi at 51. -/
private lemma sageS114_q51 : (49.4853745 : ℝ) < psiR ((51:ℕ):ℝ) ∧ psiR ((51:ℕ):ℝ) < (49.4853845 : ℝ) :=
  sageS114_np 50 51 sageS114_q50

/-- psi at 52. -/
private lemma sageS114_q52 : (49.4853745 : ℝ) < psiR ((52:ℕ):ℝ) ∧ psiR ((52:ℕ):ℝ) < (49.4853845 : ℝ) :=
  sageS114_np 51 52 sageS114_q51

/-- psi at 53. -/
private lemma sageS114_q53 : (53.4556659 : ℝ) < psiR ((53:ℕ):ℝ) ∧ psiR ((53:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_pp 52 53 53 sageS114_q52 sageS114_log53

/-- psi at 54. -/
private lemma sageS114_q54 : (53.4556659 : ℝ) < psiR ((54:ℕ):ℝ) ∧ psiR ((54:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_np 53 54 sageS114_q53

/-- psi at 55. -/
private lemma sageS114_q55 : (53.4556659 : ℝ) < psiR ((55:ℕ):ℝ) ∧ psiR ((55:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_np 54 55 sageS114_q54

/-- psi at 56. -/
private lemma sageS114_q56 : (53.4556659 : ℝ) < psiR ((56:ℕ):ℝ) ∧ psiR ((56:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_np 55 56 sageS114_q55

/-- psi at 57. -/
private lemma sageS114_q57 : (53.4556659 : ℝ) < psiR ((57:ℕ):ℝ) ∧ psiR ((57:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_np 56 57 sageS114_q56

/-- psi at 58. -/
private lemma sageS114_q58 : (53.4556659 : ℝ) < psiR ((58:ℕ):ℝ) ∧ psiR ((58:ℕ):ℝ) < (53.4556767 : ℝ) :=
  sageS114_np 57 58 sageS114_q57

/-- psi at 59. -/
private lemma sageS114_q59 : (57.5332028 : ℝ) < psiR ((59:ℕ):ℝ) ∧ psiR ((59:ℕ):ℝ) < (57.5332145 : ℝ) :=
  sageS114_pp 58 59 59 sageS114_q58 sageS114_log59

/-- psi at 60. -/
private lemma sageS114_q60 : (57.5332028 : ℝ) < psiR ((60:ℕ):ℝ) ∧ psiR ((60:ℕ):ℝ) < (57.5332145 : ℝ) :=
  sageS114_np 59 60 sageS114_q59

/-- psi at 61. -/
private lemma sageS114_q61 : (61.6440762 : ℝ) < psiR ((61:ℕ):ℝ) ∧ psiR ((61:ℕ):ℝ) < (61.6440887 : ℝ) :=
  sageS114_pp 60 61 61 sageS114_q60 sageS114_log61

/-- psi at 62. -/
private lemma sageS114_q62 : (61.6440762 : ℝ) < psiR ((62:ℕ):ℝ) ∧ psiR ((62:ℕ):ℝ) < (61.6440887 : ℝ) :=
  sageS114_np 61 62 sageS114_q61

/-- psi at 63. -/
private lemma sageS114_q63 : (61.6440762 : ℝ) < psiR ((63:ℕ):ℝ) ∧ psiR ((63:ℕ):ℝ) < (61.6440887 : ℝ) :=
  sageS114_np 62 63 sageS114_q62

/-- psi at 64. -/
private lemma sageS114_q64 : (62.3372233 : ℝ) < psiR ((64:ℕ):ℝ) ∧ psiR ((64:ℕ):ℝ) < (62.3372359 : ℝ) :=
  sageS114_pp 63 64 2 sageS114_q63 sageS114_log2

/-- psi at 65. -/
private lemma sageS114_q65 : (62.3372233 : ℝ) < psiR ((65:ℕ):ℝ) ∧ psiR ((65:ℕ):ℝ) < (62.3372359 : ℝ) :=
  sageS114_np 64 65 sageS114_q64

/-- psi at 66. -/
private lemma sageS114_q66 : (62.3372233 : ℝ) < psiR ((66:ℕ):ℝ) ∧ psiR ((66:ℕ):ℝ) < (62.3372359 : ℝ) :=
  sageS114_np 65 66 sageS114_q65

/-- psi at 67. -/
private lemma sageS114_q67 : (66.5419153 : ℝ) < psiR ((67:ℕ):ℝ) ∧ psiR ((67:ℕ):ℝ) < (66.5419288 : ℝ) :=
  sageS114_pp 66 67 67 sageS114_q66 sageS114_log67

/-- psi at 68. -/
private lemma sageS114_q68 : (66.5419153 : ℝ) < psiR ((68:ℕ):ℝ) ∧ psiR ((68:ℕ):ℝ) < (66.5419288 : ℝ) :=
  sageS114_np 67 68 sageS114_q67

/-- psi at 69. -/
private lemma sageS114_q69 : (66.5419153 : ℝ) < psiR ((69:ℕ):ℝ) ∧ psiR ((69:ℕ):ℝ) < (66.5419288 : ℝ) :=
  sageS114_np 68 69 sageS114_q68

/-- psi at 70. -/
private lemma sageS114_q70 : (66.5419153 : ℝ) < psiR ((70:ℕ):ℝ) ∧ psiR ((70:ℕ):ℝ) < (66.5419288 : ℝ) :=
  sageS114_np 69 70 sageS114_q69

/-- psi at 71. -/
private lemma sageS114_q71 : (70.8045946 : ℝ) < psiR ((71:ℕ):ℝ) ∧ psiR ((71:ℕ):ℝ) < (70.8046090 : ℝ) :=
  sageS114_pp 70 71 71 sageS114_q70 sageS114_log71

/-- psi at 72. -/
private lemma sageS114_q72 : (70.8045946 : ℝ) < psiR ((72:ℕ):ℝ) ∧ psiR ((72:ℕ):ℝ) < (70.8046090 : ℝ) :=
  sageS114_np 71 72 sageS114_q71

/-- psi at 73. -/
private lemma sageS114_q73 : (75.0950536 : ℝ) < psiR ((73:ℕ):ℝ) ∧ psiR ((73:ℕ):ℝ) < (75.0950688 : ℝ) :=
  sageS114_pp 72 73 73 sageS114_q72 sageS114_log73

/-- psi at 74. -/
private lemma sageS114_q74 : (75.0950536 : ℝ) < psiR ((74:ℕ):ℝ) ∧ psiR ((74:ℕ):ℝ) < (75.0950688 : ℝ) :=
  sageS114_np 73 74 sageS114_q73

/-- PROVED in S114, was a LEAF: EP2022 p. 36, the Sage check: for every integer n in `[1, 74]`,
`|ψ(n) - n| < √n log² n / (8π) + 1.6`. A Python recomputation gives least slack
about 0.0072. EASY. -/
theorem sage_check (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 74) :
    |psiR n - n| < 1 / (8 * π) * √(n : ℝ) * log n ^ 2 + 1.6 := by
  interval_cases n
  · exact sageS114_fin 1 (1.000 : ℝ) (0.0000 : ℝ) (0.0000 : ℝ) sageS114_q1
      (by norm_num)
  · exact sageS114_fin 2 (1.414 : ℝ) (0.6931 : ℝ) (0.0270 : ℝ) sageS114_q2
      (le_trans (by norm_num) sageS114_log2.1.le)
  · exact sageS114_fin 3 (1.732 : ℝ) (1.0986 : ℝ) (0.0831 : ℝ) sageS114_q3
      (le_trans (by norm_num) sageS114_log3.1.le)
  · exact sageS114_fin 4 (2.000 : ℝ) (1.3862 : ℝ) (0.1529 : ℝ) sageS114_q4
      (by rw [show ((4:ℕ):ℝ) = 2^2 by norm_num, Real.log_pow]; linarith [sageS114_log2.1, sageS114_log2.2])
  · exact sageS114_fin 5 (2.236 : ℝ) (1.6094 : ℝ) (0.2304 : ℝ) sageS114_q5
      (le_trans (by norm_num) sageS114_log5.1.le)
  · exact sageS114_fin 6 (2.449 : ℝ) (1.7917 : ℝ) (0.3128 : ℝ) sageS114_q6
      (by rw [show ((6:ℕ):ℝ) = 2 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 7 (2.645 : ℝ) (1.9459 : ℝ) (0.3984 : ℝ) sageS114_q7
      (le_trans (by norm_num) sageS114_log7.1.le)
  · exact sageS114_fin 8 (2.828 : ℝ) (2.0794 : ℝ) (0.4865 : ℝ) sageS114_q8
      (by rw [show ((8:ℕ):ℝ) = 2^3 by norm_num, Real.log_pow]; linarith [sageS114_log2.1, sageS114_log2.2])
  · exact sageS114_fin 9 (3.000 : ℝ) (2.1972 : ℝ) (0.5762 : ℝ) sageS114_q9
      (by rw [show ((9:ℕ):ℝ) = 3^2 by norm_num, Real.log_pow]; linarith [sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 10 (3.162 : ℝ) (2.3025 : ℝ) (0.6669 : ℝ) sageS114_q10
      (by rw [show ((10:ℕ):ℝ) = 2 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 11 (3.316 : ℝ) (2.3978 : ℝ) (0.7585 : ℝ) sageS114_q11
      (le_trans (by norm_num) sageS114_log11.1.le)
  · exact sageS114_fin 12 (3.464 : ℝ) (2.4849 : ℝ) (0.8510 : ℝ) sageS114_q12
      (by rw [show ((12:ℕ):ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 13 (3.605 : ℝ) (2.5649 : ℝ) (0.9436 : ℝ) sageS114_q13
      (le_trans (by norm_num) sageS114_log13.1.le)
  · exact sageS114_fin 14 (3.741 : ℝ) (2.6390 : ℝ) (1.0366 : ℝ) sageS114_q14
      (by rw [show ((14:ℕ):ℝ) = 2 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 15 (3.872 : ℝ) (2.7080 : ℝ) (1.1297 : ℝ) sageS114_q15
      (by rw [show ((15:ℕ):ℝ) = 3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 16 (4.000 : ℝ) (2.7725 : ℝ) (1.2233 : ℝ) sageS114_q16
      (by rw [show ((16:ℕ):ℝ) = 2^4 by norm_num, Real.log_pow]; linarith [sageS114_log2.1, sageS114_log2.2])
  · exact sageS114_fin 17 (4.123 : ℝ) (2.8332 : ℝ) (1.3168 : ℝ) sageS114_q17
      (le_trans (by norm_num) sageS114_log17.1.le)
  · exact sageS114_fin 18 (4.242 : ℝ) (2.8903 : ℝ) (1.4099 : ℝ) sageS114_q18
      (by rw [show ((18:ℕ):ℝ) = 2 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 19 (4.358 : ℝ) (2.9444 : ℝ) (1.5032 : ℝ) sageS114_q19
      (le_trans (by norm_num) sageS114_log19.1.le)
  · exact sageS114_fin 20 (4.472 : ℝ) (2.9957 : ℝ) (1.5968 : ℝ) sageS114_q20
      (by rw [show ((20:ℕ):ℝ) = 2^2 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 21 (4.582 : ℝ) (3.0445 : ℝ) (1.6898 : ℝ) sageS114_q21
      (by rw [show ((21:ℕ):ℝ) = 3 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 22 (4.690 : ℝ) (3.0910 : ℝ) (1.7829 : ℝ) sageS114_q22
      (by rw [show ((22:ℕ):ℝ) = 2 * 11 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log11.1, sageS114_log11.2])
  · exact sageS114_fin 23 (4.795 : ℝ) (3.1354 : ℝ) (1.8755 : ℝ) sageS114_q23
      (le_trans (by norm_num) sageS114_log23.1.le)
  · exact sageS114_fin 24 (4.898 : ℝ) (3.1780 : ℝ) (1.9682 : ℝ) sageS114_q24
      (by rw [show ((24:ℕ):ℝ) = 2^3 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 25 (5.000 : ℝ) (3.2188 : ℝ) (2.0611 : ℝ) sageS114_q25
      (by rw [show ((25:ℕ):ℝ) = 5^2 by norm_num, Real.log_pow]; linarith [sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 26 (5.099 : ℝ) (3.2580 : ℝ) (2.1535 : ℝ) sageS114_q26
      (by rw [show ((26:ℕ):ℝ) = 2 * 13 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log13.1, sageS114_log13.2])
  · exact sageS114_fin 27 (5.196 : ℝ) (3.2958 : ℝ) (2.2456 : ℝ) sageS114_q27
      (by rw [show ((27:ℕ):ℝ) = 3^3 by norm_num, Real.log_pow]; linarith [sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 28 (5.291 : ℝ) (3.3322 : ℝ) (2.3375 : ℝ) sageS114_q28
      (by rw [show ((28:ℕ):ℝ) = 2^2 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 29 (5.385 : ℝ) (3.3672 : ℝ) (2.4293 : ℝ) sageS114_q29
      (le_trans (by norm_num) sageS114_log29.1.le)
  · exact sageS114_fin 30 (5.477 : ℝ) (3.4011 : ℝ) (2.5208 : ℝ) sageS114_q30
      (by rw [show ((30:ℕ):ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 31 (5.567 : ℝ) (3.4339 : ℝ) (2.6118 : ℝ) sageS114_q31
      (le_trans (by norm_num) sageS114_log31.1.le)
  · exact sageS114_fin 32 (5.656 : ℝ) (3.4657 : ℝ) (2.7030 : ℝ) sageS114_q32
      (by rw [show ((32:ℕ):ℝ) = 2^5 by norm_num, Real.log_pow]; linarith [sageS114_log2.1, sageS114_log2.2])
  · exact sageS114_fin 33 (5.744 : ℝ) (3.4965 : ℝ) (2.7940 : ℝ) sageS114_q33
      (by rw [show ((33:ℕ):ℝ) = 3 * 11 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log11.1, sageS114_log11.2])
  · exact sageS114_fin 34 (5.830 : ℝ) (3.5263 : ℝ) (2.8844 : ℝ) sageS114_q34
      (by rw [show ((34:ℕ):ℝ) = 2 * 17 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log17.1, sageS114_log17.2])
  · exact sageS114_fin 35 (5.916 : ℝ) (3.5553 : ℝ) (2.9753 : ℝ) sageS114_q35
      (by rw [show ((35:ℕ):ℝ) = 5 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log5.1, sageS114_log5.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 36 (6.000 : ℝ) (3.5835 : ℝ) (3.0656 : ℝ) sageS114_q36
      (by rw [show ((36:ℕ):ℝ) = 2^2 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 37 (6.082 : ℝ) (3.6109 : ℝ) (3.1552 : ℝ) sageS114_q37
      (le_trans (by norm_num) sageS114_log37.1.le)
  · exact sageS114_fin 38 (6.164 : ℝ) (3.6375 : ℝ) (3.2450 : ℝ) sageS114_q38
      (by rw [show ((38:ℕ):ℝ) = 2 * 19 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log19.1, sageS114_log19.2])
  · exact sageS114_fin 39 (6.244 : ℝ) (3.6635 : ℝ) (3.3343 : ℝ) sageS114_q39
      (by rw [show ((39:ℕ):ℝ) = 3 * 13 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log13.1, sageS114_log13.2])
  · exact sageS114_fin 40 (6.324 : ℝ) (3.6888 : ℝ) (3.4239 : ℝ) sageS114_q40
      (by rw [show ((40:ℕ):ℝ) = 2^3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 41 (6.403 : ℝ) (3.7135 : ℝ) (3.5132 : ℝ) sageS114_q41
      (le_trans (by norm_num) sageS114_log41.1.le)
  · exact sageS114_fin 42 (6.480 : ℝ) (3.7376 : ℝ) (3.6018 : ℝ) sageS114_q42
      (by rw [show ((42:ℕ):ℝ) = 2 * 3 * 7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 43 (6.557 : ℝ) (3.7611 : ℝ) (3.6905 : ℝ) sageS114_q43
      (le_trans (by norm_num) sageS114_log43.1.le)
  · exact sageS114_fin 44 (6.633 : ℝ) (3.7841 : ℝ) (3.7791 : ℝ) sageS114_q44
      (by rw [show ((44:ℕ):ℝ) = 2^2 * 11 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log11.1, sageS114_log11.2])
  · exact sageS114_fin 45 (6.708 : ℝ) (3.8066 : ℝ) (3.8674 : ℝ) sageS114_q45
      (by rw [show ((45:ℕ):ℝ) = 3^2 * 5 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 46 (6.782 : ℝ) (3.8286 : ℝ) (3.9554 : ℝ) sageS114_q46
      (by rw [show ((46:ℕ):ℝ) = 2 * 23 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log23.1, sageS114_log23.2])
  · exact sageS114_fin 47 (6.855 : ℝ) (3.8501 : ℝ) (4.0430 : ℝ) sageS114_q47
      (le_trans (by norm_num) sageS114_log47.1.le)
  · exact sageS114_fin 48 (6.928 : ℝ) (3.8712 : ℝ) (4.1310 : ℝ) sageS114_q48
      (by rw [show ((48:ℕ):ℝ) = 2^4 * 3 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 49 (7.000 : ℝ) (3.8918 : ℝ) (4.2185 : ℝ) sageS114_q49
      (by rw [show ((49:ℕ):ℝ) = 7^2 by norm_num, Real.log_pow]; linarith [sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 50 (7.071 : ℝ) (3.9120 : ℝ) (4.3056 : ℝ) sageS114_q50
      (by rw [show ((50:ℕ):ℝ) = 2 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 51 (7.141 : ℝ) (3.9318 : ℝ) (4.3923 : ℝ) sageS114_q51
      (by rw [show ((51:ℕ):ℝ) = 3 * 17 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log17.1, sageS114_log17.2])
  · exact sageS114_fin 52 (7.211 : ℝ) (3.9512 : ℝ) (4.4793 : ℝ) sageS114_q52
      (by rw [show ((52:ℕ):ℝ) = 2^2 * 13 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log13.1, sageS114_log13.2])
  · exact sageS114_fin 53 (7.280 : ℝ) (3.9702 : ℝ) (4.5657 : ℝ) sageS114_q53
      (le_trans (by norm_num) sageS114_log53.1.le)
  · exact sageS114_fin 54 (7.348 : ℝ) (3.9889 : ℝ) (4.6519 : ℝ) sageS114_q54
      (by rw [show ((54:ℕ):ℝ) = 2 * 3^3 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 55 (7.416 : ℝ) (4.0073 : ℝ) (4.7384 : ℝ) sageS114_q55
      (by rw [show ((55:ℕ):ℝ) = 5 * 11 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log5.1, sageS114_log5.2, sageS114_log11.1, sageS114_log11.2])
  · exact sageS114_fin 56 (7.483 : ℝ) (4.0253 : ℝ) (4.8242 : ℝ) sageS114_q56
      (by rw [show ((56:ℕ):ℝ) = 2^3 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 57 (7.549 : ℝ) (4.0430 : ℝ) (4.9097 : ℝ) sageS114_q57
      (by rw [show ((57:ℕ):ℝ) = 3 * 19 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log19.1, sageS114_log19.2])
  · exact sageS114_fin 58 (7.615 : ℝ) (4.0604 : ℝ) (4.9953 : ℝ) sageS114_q58
      (by rw [show ((58:ℕ):ℝ) = 2 * 29 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log29.1, sageS114_log29.2])
  · exact sageS114_fin 59 (7.681 : ℝ) (4.0775 : ℝ) (5.0811 : ℝ) sageS114_q59
      (le_trans (by norm_num) sageS114_log59.1.le)
  · exact sageS114_fin 60 (7.745 : ℝ) (4.0943 : ℝ) (5.1658 : ℝ) sageS114_q60
      (by rw [show ((60:ℕ):ℝ) = 2^2 * 3 * 5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log5.1, sageS114_log5.2])
  · exact sageS114_fin 61 (7.810 : ℝ) (4.1108 : ℝ) (5.2512 : ℝ) sageS114_q61
      (le_trans (by norm_num) sageS114_log61.1.le)
  · exact sageS114_fin 62 (7.874 : ℝ) (4.1271 : ℝ) (5.3363 : ℝ) sageS114_q62
      (by rw [show ((62:ℕ):ℝ) = 2 * 31 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log31.1, sageS114_log31.2])
  · exact sageS114_fin 63 (7.937 : ℝ) (4.1431 : ℝ) (5.4208 : ℝ) sageS114_q63
      (by rw [show ((63:ℕ):ℝ) = 3^2 * 7 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 64 (8.000 : ℝ) (4.1588 : ℝ) (5.5053 : ℝ) sageS114_q64
      (by rw [show ((64:ℕ):ℝ) = 2^6 by norm_num, Real.log_pow]; linarith [sageS114_log2.1, sageS114_log2.2])
  · exact sageS114_fin 65 (8.062 : ℝ) (4.1743 : ℝ) (5.5894 : ℝ) sageS114_q65
      (by rw [show ((65:ℕ):ℝ) = 5 * 13 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log5.1, sageS114_log5.2, sageS114_log13.1, sageS114_log13.2])
  · exact sageS114_fin 66 (8.124 : ℝ) (4.1896 : ℝ) (5.6738 : ℝ) sageS114_q66
      (by rw [show ((66:ℕ):ℝ) = 2 * 3 * 11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2, sageS114_log11.1, sageS114_log11.2])
  · exact sageS114_fin 67 (8.185 : ℝ) (4.2046 : ℝ) (5.7574 : ℝ) sageS114_q67
      (le_trans (by norm_num) sageS114_log67.1.le)
  · exact sageS114_fin 68 (8.246 : ℝ) (4.2195 : ℝ) (5.8415 : ℝ) sageS114_q68
      (by rw [show ((68:ℕ):ℝ) = 2^2 * 17 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log17.1, sageS114_log17.2])
  · exact sageS114_fin 69 (8.306 : ℝ) (4.2341 : ℝ) (5.9247 : ℝ) sageS114_q69
      (by rw [show ((69:ℕ):ℝ) = 3 * 23 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log3.1, sageS114_log3.2, sageS114_log23.1, sageS114_log23.2])
  · exact sageS114_fin 70 (8.366 : ℝ) (4.2484 : ℝ) (6.0079 : ℝ) sageS114_q70
      (by rw [show ((70:ℕ):ℝ) = 2 * 5 * 7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log5.1, sageS114_log5.2, sageS114_log7.1, sageS114_log7.2])
  · exact sageS114_fin 71 (8.426 : ℝ) (4.2626 : ℝ) (6.0915 : ℝ) sageS114_q71
      (le_trans (by norm_num) sageS114_log71.1.le)
  · exact sageS114_fin 72 (8.485 : ℝ) (4.2766 : ℝ) (6.1745 : ℝ) sageS114_q72
      (by rw [show ((72:ℕ):ℝ) = 2^3 * 3^2 by norm_num, Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_pow, Nat.cast_ofNat]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log3.1, sageS114_log3.2])
  · exact sageS114_fin 73 (8.544 : ℝ) (4.2904 : ℝ) (6.2577 : ℝ) sageS114_q73
      (le_trans (by norm_num) sageS114_log73.1.le)
  · exact sageS114_fin 74 (8.602 : ℝ) (4.3040 : ℝ) (6.3402 : ℝ) sageS114_q74
      (by rw [show ((74:ℕ):ℝ) = 2 * 37 by norm_num, Real.log_mul (by positivity) (by positivity)]; linarith [sageS114_log2.1, sageS114_log2.2, sageS114_log37.1, sageS114_log37.2])

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

/-- PROVED in S114, was a LEAF: EP2022 Lemma 18 p. 16: for x ≥ 2 both trivial zero sums
`∑ x^(1-2m) / (2m-1)` and `∑ x^(-2m) / (2m)` are at most 1. MEDIUM. -/
theorem lemma18 {m : ℕ} (χ : DirichletCharacter ℂ m) (x : ℝ) (hx : 2 ≤ x) :
    ‖trivSum χ x‖ ≤ 1 := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have key : ∀ k : ℕ, ‖((x : ℂ) ^ (aChi χ - 2 * ((k : ℂ) + 1))) / (2 * ((k : ℂ) + 1) - aChi χ)‖
      ≤ (1/2:ℝ) ^ (k+1) := by
    intro k
    have hb : ∀ (c : ℝ), 0 ≤ c → 1 ≤ 2*((k:ℝ)+1) - c → c ≤ 1 →
        ‖((x : ℂ) ^ ((c:ℂ) - 2 * ((k : ℂ) + 1))) / (2 * ((k : ℂ) + 1) - (c:ℂ))‖
          ≤ (1/2:ℝ) ^ (k+1) := by
      intro c hc0 hc1 hc2
      have e1 : (c:ℂ) - 2 * ((k : ℂ) + 1) = ((c - 2*((k:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
      have e2 : 2 * ((k : ℂ) + 1) - (c:ℂ) = ((2*((k:ℝ)+1) - c : ℝ) : ℂ) := by push_cast; ring
      rw [e1, e2, ← Complex.ofReal_cpow hx0, ← Complex.ofReal_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg (rpow_nonneg hx0 _) (by linarith))]
      have h1 : x ^ (c - 2*((k:ℝ)+1)) ≤ 2 ^ (c - 2*((k:ℝ)+1)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
      have h2 : (2:ℝ) ^ (c - 2*((k:ℝ)+1)) ≤ 2 ^ (-((k+1 : ℕ):ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      have h3 : (2:ℝ) ^ (-((k+1 : ℕ):ℝ)) = (1/2:ℝ)^(k+1) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [div_le_iff₀ (by linarith)]
      have h4 : (0:ℝ) ≤ (1/2:ℝ)^(k+1) := by positivity
      nlinarith
    unfold aChi
    split_ifs
    · have := hb 1 (by norm_num) (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]) le_rfl
      simpa using this
    · have := hb 0 le_rfl (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]) (by norm_num)
      simpa using this
  have hg : Summable (fun k : ℕ => (1/2:ℝ)^(k+1)) :=
    (summable_geometric_two).comp_injective (add_left_injective 1)
  have hs := Summable.of_nonneg_of_le (fun k => norm_nonneg _) key hg
  unfold trivSum
  calc _ ≤ _ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, (1/2:ℝ)^(k+1) := hs.tsum_le_tsum key hg
    _ = 1 := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_two]; norm_num

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

/-- PROVED: the tangent line bound of the logarithm at `exp k`. -/
private theorem log_le_tangent (u k β : ℝ) (hu : 0 < u) (hβ : 1 ≤ β * exp k) :
    log u ≤ k - 1 + u * β := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hu (exp_pos k))
  rw [log_div hu.ne' (exp_pos k).ne', log_exp] at h1
  have h2 : u / exp k ≤ u * β := by
    rw [div_le_iff₀ (exp_pos k)]
    nlinarith
  linarith

/-- PROVED: `log 3 > 1.0939`. -/
private theorem log_three_gt : (1.0939 : ℝ) ≤ log 3 := by
  have he := Real.exp_one_lt_d9
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos (by norm_num : (0:ℝ) < 3) (exp_pos 1))
  rw [log_div (by norm_num) (exp_pos 1).ne', log_exp, inv_div] at h1
  have h2 : exp 1 / 3 ≤ 2.7182818286 / 3 := by
    apply div_le_div_of_nonneg_right he.le (by norm_num)
  linarith

/-- PROVED: the lemma21RHS and R1 comparison, all three cases of q. -/
private theorem combine_R1 (q : ℕ) (hq : 3 ≤ q) :
    lemma21RHS q / 2 + 1.3755 * log q + 14.239 ≤ R1 q - 1.8 * log q - 89 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hl : (1.0939:ℝ) ≤ log q :=
    le_trans log_three_gt (log_le_log (by norm_num) (by exact_mod_cast hq))
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hl2 := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_gt_three
  have hlpi : log π ≤ π - 1 := Real.log_le_sub_one_of_pos pi_pos
  have hlpi0 : 0 ≤ log π := log_nonneg (by linarith)
  have hsq : 0 ≤ √(q:ℝ) := sqrt_nonneg _
  have hsql : 0 ≤ √(q:ℝ) * log q := mul_nonneg hsq (by linarith)
  unfold lemma21RHS R1
  split_ifs with h1 h2
  · rw [log_mul hq0.ne' pi_pos.ne']
    nlinarith
  · rw [log_div hq0.ne' pi_pos.ne']
    nlinarith [sq_nonneg (log q)]
  · rw [log_div hq0.ne' pi_pos.ne']
    have hll : 0 ≤ log (log q) := log_nonneg (by linarith)
    nlinarith [mul_nonneg hll (sq_nonneg (log q)), sq_nonneg (log q)]

/-- PROVED: the log x terms, with `ϕ(q) ≥ 2` and the case q = 6. -/
private theorem combine_A (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    (if q = 6 then 2 * log x else log q * log x) / (q.totient : ℝ) + errPrim q x
      + 1 / 2 * log x ≤ (2.015 * log q + 0.5) * log x := by
  have hL : 0 ≤ log x := log_nonneg (by linarith)
  have hl : (1.0939:ℝ) ≤ log q :=
    le_trans log_three_gt (log_le_log (by norm_num) (by exact_mod_cast hq))
  unfold errPrim
  split_ifs with h6
  · subst h6
    have ht : Nat.totient 6 = 2 := by decide
    rw [ht]
    have h62 : log ((6:ℕ):ℝ) = log 2 + log 3 := by
      rw [show ((6:ℕ):ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    rw [h62]
    have := Real.log_two_gt_d9
    have := log_three_gt
    push_cast
    nlinarith
  · have hφ : (2:ℝ) ≤ q.totient := by
      have he := Nat.totient_even (by omega : 2 < q)
      have hp := Nat.totient_pos.2 (by omega : 0 < q)
      obtain ⟨k, hk⟩ := he
      exact_mod_cast (by omega : 2 ≤ q.totient)
    have hlL : 0 ≤ log q * log x := mul_nonneg (by linarith) hL
    have : log q * log x / (q.totient : ℝ) ≤ log q * log x / 2 :=
      div_le_div_of_nonneg_left hlL (by norm_num) hφ
    nlinarith

/-- PROVED: EP2022 pp. 38 to 40, the square root part of the combination, a polynomial
inequality in `l = log q`, `L = log x`, `w = x^-0.077` and `M = log log qx`. -/
private theorem combine_core (l L w M : ℝ) (hgl : 0 ≤ l - 1.0939) (hgL : 0 ≤ L - 0.6931)
    (hw : 0 ≤ w) (hw1 : 0 ≤ 0.949 - w) (hwL : 0 ≤ 4.778 - L * w)
    (he2 : 0 ≤ 1 - w * (1 + 0.077 * L + 0.0029645 * L ^ 2)) (hM : 0 ≤ M)
    (ht1 : 0 ≤ 1 + (l + L) * 0.13534 - M) (ht2 : 0 ≤ 2 + (l + L) * 0.04979 - M)
    (ht3 : 0 ≤ 3 + (l + L) * 0.01832 - M) :
    (1.737 + 0.184 * l) * L + 1.363 * L ^ 2 * w + 14.712 * L * w + 18.61 * M * w
      + (2.382 * l + 8.018) * w + 1.693 * l + 11.946 + 5
      + (127.562 * M ^ 2 + (32.449 * l - 1.72) * M + 2.064 * l ^ 2 + 6.57 * l + 79.146) * w / L
    ≤ (0.184 * l + 8.25) * L + 5.314 * l + 124.318
      + (5.048 * l ^ 2 + 109.573 * l + 725.316) / L := by
  have hl0 : 0 ≤ l := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have key : ((1.737 + 0.184 * l) * L + 1.363 * L ^ 2 * w + 14.712 * L * w + 18.61 * M * w
      + (2.382 * l + 8.018) * w + 1.693 * l + 11.946 + 5) * L
      + (127.562 * M ^ 2 + (32.449 * l - 1.72) * M + 2.064 * l ^ 2 + 6.57 * l + 79.146) * w
    ≤ ((0.184 * l + 8.25) * L + 5.314 * l + 124.318) * L
      + (5.048 * l ^ 2 + 109.573 * l + 725.316) := by
    linarith [mul_nonneg hwL hw,
    mul_nonneg he2 hL0,
    mul_nonneg he2 hM,
    mul_nonneg he2 (mul_nonneg hM hw),
    mul_nonneg ht1 (mul_nonneg hM hw),
    mul_nonneg (mul_nonneg hgl hgL) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg hgl hw1) hl0,
    mul_nonneg (mul_nonneg hgl hw1) hL0,
    mul_nonneg (mul_nonneg hgl hw1) hM,
    mul_nonneg (mul_nonneg hgl he2) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg hgl ht1) hw,
    mul_nonneg (mul_nonneg hgl ht2) hw,
    mul_nonneg (mul_nonneg hgl ht2) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg hgl ht3) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg hgL hw1) hL0,
    mul_nonneg (mul_nonneg hgL hwL) hL0,
    mul_nonneg (mul_nonneg hgL hwL) hw,
    mul_nonneg (mul_nonneg hgL hwL) hM,
    mul_nonneg (mul_nonneg hgL hwL) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg hgL he2) (mul_nonneg hM hw),
    mul_nonneg (mul_nonneg hgL ht1) (mul_nonneg hM hw),
    mul_nonneg (mul_nonneg hw1 ht1) hL0,
    mul_nonneg (mul_nonneg hwL he2) hl0,
    mul_nonneg (mul_nonneg hwL he2) hL0,
    (mul_nonneg hwL ht1),
    mul_nonneg (mul_nonneg hwL ht1) hl0,
    mul_nonneg (mul_nonneg hwL ht1) hL0,
    (mul_nonneg hwL ht2),
    mul_nonneg (mul_nonneg hwL ht3) hL0,
    mul_nonneg (mul_nonneg he2 ht3) (mul_nonneg hL0 hw),
    mul_nonneg (mul_nonneg ht2 ht2) (mul_nonneg hL0 hw)]
  have e1 : (1.737 + 0.184 * l) * L + 1.363 * L ^ 2 * w + 14.712 * L * w + 18.61 * M * w
      + (2.382 * l + 8.018) * w + 1.693 * l + 11.946 + 5
      + (127.562 * M ^ 2 + (32.449 * l - 1.72) * M + 2.064 * l ^ 2 + 6.57 * l + 79.146) * w / L
      = (((1.737 + 0.184 * l) * L + 1.363 * L ^ 2 * w + 14.712 * L * w + 18.61 * M * w
      + (2.382 * l + 8.018) * w + 1.693 * l + 11.946 + 5) * L
      + (127.562 * M ^ 2 + (32.449 * l - 1.72) * M + 2.064 * l ^ 2 + 6.57 * l + 79.146) * w) / L := by
    field_simp
  have e2 : (0.184 * l + 8.25) * L + 5.314 * l + 124.318
      + (5.048 * l ^ 2 + 109.573 * l + 725.316) / L
      = (((0.184 * l + 8.25) * L + 5.314 * l + 124.318) * L
      + (5.048 * l ^ 2 + 109.573 * l + 725.316)) / L := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hLpos.le

/-- PROVED in S114, was a LEAF: EP2022 pp. 38 to 40, the combination and simplification of all terms, with
`ϕ(q) ≥ 2`, `x^0.423 < 0.949 √x`, `log x / x^0.077 ≤ 4.778` and Lemma 9, down to the right
side of Theorem 3 with R1 q. A pure real inequality. MEDIUM. -/
theorem combine (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    (if q = 6 then 2 * log x else log q * log x) / (q.totient : ℝ)
      + (1 / (8 * π) * √x * log x ^ 2 + 2.6) / (q.totient : ℝ)
      + errPrim q x + zeroBound q x + (1 / 2 * (log x + 2.751 * log q + 23.878) + 1)
      + lemma21RHS q / 2 ≤ thm3RHS q x := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hφpos : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ : (2:ℝ) ≤ q.totient := by
    have he := Nat.totient_even (by omega : 2 < q)
    have hp := Nat.totient_pos.2 (by omega : 0 < q)
    obtain ⟨k, hk⟩ := he
    exact_mod_cast (by omega : 2 ≤ q.totient)
  have h26 : 2.6 / (q.totient : ℝ) ≤ 1.3 := by
    rw [div_le_iff₀ hφpos]; linarith
  have E1 : (1 / (8 * π) * √x * log x ^ 2 + 2.6) / (q.totient : ℝ)
      = 1 / (8 * π * (q.totient : ℝ)) * √x * log x ^ 2 + 2.6 / (q.totient : ℝ) := by
    field_simp
  rw [E1]
  have hA := combine_A q x hq hx
  have hQ := combine_R1 q hq
  have hl : (1.0939:ℝ) ≤ log q :=
    le_trans log_three_gt (log_le_log (by norm_num) (by exact_mod_cast hq))
  have hL : (0.6931:ℝ) ≤ log x := by
    have := Real.log_two_gt_d9
    have := log_le_log (by norm_num) hx
    linarith
  have hs1 : 1 ≤ √x := by
    rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by linarith)
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  have hz : x ^ (0.077:ℝ) = exp (0.077 * log x) := by rw [rpow_def_of_pos hx0]; ring_nf
  have hzpos : 0 < x ^ (0.077:ℝ) := rpow_pos_of_pos hx0 _
  have hy : x ^ (0.423:ℝ) = √x * (x ^ (0.077:ℝ))⁻¹ := by
    have : x ^ (0.423:ℝ) * x ^ (0.077:ℝ) = √x := by
      rw [← rpow_add hx0, sqrt_eq_rpow]; norm_num
    rw [← this]; field_simp
  have hqx : log ((q:ℝ) * x) = log q + log x := log_mul hq0.ne' hx0.ne'
  have hzq : 1 + 0.077 * log x + 0.0029645 * log x ^ 2 ≤ x ^ (0.077:ℝ) := by
    rw [hz]
    have := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 0.077 * log x)
    nlinarith
  have hzL : log x ≤ 4.778 * x ^ (0.077:ℝ) := by
    rw [hz]
    have h1 := add_one_le_exp (0.077 * log x - 1)
    have h2 : exp (0.077 * log x) = exp 1 * exp (0.077 * log x - 1) := by
      rw [← exp_add]; ring_nf
    have he := Real.exp_one_gt_d9
    rw [h2]
    nlinarith [exp_pos (0.077 * log x - 1)]
  unfold zeroBound thm3RHS
  rw [hy, hqx]
  clear hy hz E1
  generalize log x = L at *
  generalize log (q:ℝ) = l at *
  generalize √x = s at *
  generalize x ^ (0.077:ℝ) = z at *
  have hpos : 0 < l + L := by linarith
  generalize hMe : log (l + L) = M
  have hw0 : 0 ≤ z⁻¹ := inv_nonneg.2 hzpos.le
  have hwz : z⁻¹ * z = 1 := inv_mul_cancel₀ hzpos.ne'
  have hw1 : 0 ≤ 0.949 - z⁻¹ := by nlinarith
  have hwL : 0 ≤ 4.778 - L * z⁻¹ := by nlinarith
  have he2 : 0 ≤ 1 - z⁻¹ * (1 + 0.077 * L + 0.0029645 * L ^ 2) := by nlinarith
  have hM0 : 0 ≤ M := by rw [← hMe]; exact log_nonneg (by linarith)
  have he1 := Real.exp_one_gt_d9
  have hexp2 : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
  have hexp3 : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
  have hexp4 : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
  have hb2 : (2.7182818283:ℝ) ^ 2 ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he1.le 2
  have hb3 : (2.7182818283:ℝ) ^ 3 ≤ exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1.le 3
  have hb4 : (2.7182818283:ℝ) ^ 4 ≤ exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1.le 4
  have ht1 : 0 ≤ 1 + (l + L) * 0.13534 - M := by
    have := log_le_tangent (l + L) 2 0.13534 hpos
      (by rw [hexp2]; linarith [hb2, (show (1:ℝ) ≤ 0.13534 * 2.7182818283 ^ 2 by norm_num)])
    linarith
  have ht2 : 0 ≤ 2 + (l + L) * 0.04979 - M := by
    have := log_le_tangent (l + L) 3 0.04979 hpos
      (by rw [hexp3]; linarith [hb3, (show (1:ℝ) ≤ 0.04979 * 2.7182818283 ^ 3 by norm_num)])
    linarith
  have ht3 : 0 ≤ 3 + (l + L) * 0.01832 - M := by
    have := log_le_tangent (l + L) 4 0.01832 hpos
      (by rw [hexp4]; linarith [hb4, (show (1:ℝ) ≤ 0.01832 * 2.7182818283 ^ 4 by norm_num)])
    linarith
  have hcore := combine_core l L z⁻¹ M (by linarith) (by linarith) hw0 hw1 hwL he2 hM0
    ht1 ht2 ht3
  have hcs := mul_le_mul_of_nonneg_left hcore hs0
  have hl0 : 0 ≤ l := by linarith
  have hnonS : 13.962 * L / z + 8.4 / z * M + (1.255 * l + 8.510) / z
      ≤ 92.75 + 1.59 * l := by
    have e : 13.962 * L / z + 8.4 / z * M + (1.255 * l + 8.510) / z
        = 13.962 * (L * z⁻¹) + 8.4 * (z⁻¹ * M) + (1.255 * l + 8.510) * z⁻¹ := by ring
    rw [e]
    have p1 := mul_nonneg hw0 ht2
    have p2 := mul_nonneg hw1 hl0
    linarith
  have EZ : 1.363 * (s * z⁻¹) * L ^ 2 + 2.074 * s * L + 14.712 * (s * z⁻¹) * L
      + 18.610 * (s * z⁻¹) * M + (2.382 * l + 8.018) * (s * z⁻¹)
      + (127.562 * M ^ 2 + (32.449 * l - 1.720) * M + 2.064 * l ^ 2 + 6.570 * l + 79.146)
        * (s * z⁻¹) / L
      + 13.962 * L / z + 8.4 / z * M + (1.255 * l + 8.510) / z
      + (1 / (6 * π) * s * L ^ 2 + (0.184 * l - 0.337) * s * L + (1.693 * l + 11.946) * s)
    = s * ((1.737 + 0.184 * l) * L + 1.363 * L ^ 2 * z⁻¹
      + 14.712 * L * z⁻¹ + 18.61 * M * z⁻¹ + (2.382 * l + 8.018) * z⁻¹ + 1.693 * l + 11.946 + 5
      + (127.562 * M ^ 2 + (32.449 * l - 1.72) * M + 2.064 * l ^ 2 + 6.57 * l + 79.146)
        * z⁻¹ / L) - 5 * s + 1 / (6 * π) * s * L ^ 2
      + (13.962 * L / z + 8.4 / z * M + (1.255 * l + 8.510) / z) := by
    ring
  have ER : (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * s * L ^ 2
      + (0.184 * l + 8.250) * s * L + (5.314 * l + 124.318) * s
      + (5.048 * l ^ 2 + 109.573 * l + 725.316) * s / L + (2.015 * l + 0.5) * L + R1 q
    = 1 / (8 * π * (q.totient : ℝ)) * s * L ^ 2 + 1 / (6 * π) * s * L ^ 2
      + s * ((0.184 * l + 8.25) * L + 5.314 * l + 124.318
      + (5.048 * l ^ 2 + 109.573 * l + 725.316) / L) + (2.015 * l + 0.5) * L + R1 q := by
    ring
  rw [EZ, ER]
  linarith

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
