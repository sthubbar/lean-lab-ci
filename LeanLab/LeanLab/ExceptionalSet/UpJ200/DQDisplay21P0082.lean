import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions

/-!
REPAIR for unit P1122-0126, burst-20261122 session S31. P0082, Bruedern and Perelli 1998,
Ann. Inst. Fourier 48, https://doi.org/10.5802/aif.1621.

The named wall `DQLeafPrimeProductSelected.PrimeProductSelectedP0082` bundled Lemma 3 of
page 358 with the elementary display 21 of page 363, case ii b, which the paper takes from
Montgomery and Vaughan 1975, formula 8.5:

  `|𝔖~(m)| ≤ 𝔖(m) ∏_{p ∣ r, p ∤ m, p > 3} 1 / (p - 2)`.

This file carves display 21 out of the wall and proves it, with the twisted singular series
`𝔖~` of page 359 display 12 and the sum `I~` of display 13 as definitions. It also proves the
two consequences the paper draws on page 363: `|𝔖~(m)| ≤ 𝔖(m) / 3` when the product is not
empty, and the trivial bound `|I~(m)| ≤ m`.

Display 21 holds for every modulus `r ≥ 1`, every Dirichlet character and every even
`m ≠ 0`; the paper's use is for the exceptional real primitive character. Evenness matters:
for odd `m` the factor of `𝔖(m)` at `p = 2` is zero while that of `𝔖~(m)` is not.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082

open Real Finset ArithmeticFunction
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)

/-- The local factor at the prime `p` of the singular series, P0082 page 358 display 11:
`1 + 1/(p-1)` if `p ∣ m`, and `1 - 1/(p-1)^2` if `p ∤ m`. -/
noncomputable def singFactor (m : ℤ) (p : ℕ) : ℝ :=
  if (p : ℤ) ∣ m then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- P0082 page 359 display 12, the twisted singular series of the exceptional character
`χ~` of modulus `r~`:
`𝔖~(m) = χ~(-1) μ(r/(r,m)) r / (φ(r) φ(r/(r,m))) ∏_{p ∤ r m} (1 - 1/(p-1)^2) ∏_{p ∤ r, p ∣ m} (1 + 1/(p-1))`.
The two Euler products are written as one product over the primes `p ∤ r` of the local
factor of display 11. `χ~` is real, so `χ~(-1)` is real and the real part loses nothing. -/
noncomputable def twistedSing {r : ℕ} (χ : DirichletCharacter ℂ r) (m : ℤ) : ℝ :=
  (χ (-1)).re * (ArithmeticFunction.moebius (r / Int.gcd m r) : ℝ) *
    ((r : ℝ) / ((r.totient : ℝ) * ((r / Int.gcd m r).totient : ℝ))) *
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else singFactor m p)

/-- P0082 page 359 display 13, `I~(m) = Σ_{P < k < m - P} (k (m - k))^(β~ - 1)` over integers
`k`. The range is cut to `0 < k < m`, which loses nothing when `P ≥ 0`, as always in the paper
where `P = X^(6δ)`. -/
noncomputable def Itilde (β P : ℝ) (m : ℤ) : ℝ :=
  ∑ k ∈ (Finset.Ioo (0 : ℤ) m).filter (fun k : ℤ => P < (k : ℝ) ∧ (k : ℝ) < (m : ℝ) - P),
    ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1)

/-- The singular series is the product of the local factors. Definitional. -/
theorem singSeries_eq (m : ℤ) : singSeries m = ∏' p : Nat.Primes, singFactor m p := rfl

/-- Every local factor of display 11 is nonnegative. -/
theorem singFactor_nonneg (m : ℤ) {p : ℕ} (hp : p.Prime) : 0 ≤ singFactor m p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  unfold singFactor
  split_ifs
  · have : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    linarith
  · have hsq : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hsq
    linarith

/-- The singular series is nonnegative. -/
theorem singSeries_nonneg (m : ℤ) : 0 ≤ singSeries m := by
  rw [singSeries_eq]
  exact tprod_nonneg fun p => singFactor_nonneg m p.2

/-- The local weight of display 21 at a prime `p` of the modulus. -/
private theorem weight_nonneg (m : ℤ) {p : ℕ} (hp : p.Prime) :
    0 ≤ singFactor m p * (if ¬ (p : ℤ) ∣ m ∧ 3 < p then 1 / ((p : ℝ) - 2) else 1) := by
  apply mul_nonneg (singFactor_nonneg m hp)
  split_ifs with h
  · have : (3 : ℝ) < p := by exact_mod_cast h.2
    have : 0 < (p : ℝ) - 2 := by linarith
    positivity
  · norm_num

/-- `Int.gcd m r` is the natural gcd of `|m|` and `r`. -/
private theorem int_gcd_eq (m : ℤ) (r : ℕ) : Int.gcd m r = Nat.gcd m.natAbs r := rfl

/-- The local comparison behind display 21, Montgomery and Vaughan 1975 formula 8.5:
for an even `m ≠ 0` and every `r ≥ 1`,
`|μ(r/(r,m))| r / (φ(r) φ(r/(r,m))) ≤ ∏_{p ∣ r} w(p)`, where `w(p)` is the local factor of
display 11, times `1/(p-2)` when `p ∤ m` and `p > 3`. Proved by multiplicativity in `r` and a
computation at prime powers. -/
theorem local_bound (m : ℤ) (he : Even m) (r : ℕ) (hr : r ≠ 0) :
    |(ArithmeticFunction.moebius (r / Nat.gcd m.natAbs r) : ℝ)| *
        ((r : ℝ) / ((r.totient : ℝ) * ((r / Nat.gcd m.natAbs r).totient : ℝ))) ≤
      ∏ p ∈ r.primeFactors,
        singFactor m p * (if ¬ (p : ℤ) ∣ m ∧ 3 < p then 1 / ((p : ℝ) - 2) else 1) := by
  set n := m.natAbs with hn
  induction r using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hr
  | one => simp
  | prime_pow p k hp hk =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero j) hp, Finset.prod_singleton]
    have hgd : Nat.gcd n (p ^ (j + 1)) ∣ p ^ (j + 1) := Nat.gcd_dvd_right _ _
    have hdd : p ^ (j + 1) / Nat.gcd n (p ^ (j + 1)) ∣ p ^ (j + 1) := Nat.div_dvd_of_dvd hgd
    obtain ⟨i, hi, hd⟩ := (Nat.dvd_prime_pow hp).1 hdd
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hφ : (((p ^ (j + 1)).totient : ℕ) : ℝ) = (p : ℝ) ^ j * ((p : ℝ) - 1) := by
      rw [Nat.totient_prime_pow_succ hp]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    have hpj : (0 : ℝ) < (p : ℝ) ^ j := by positivity
    rw [hd]
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · -- `p^(j+1)` divides `m`
        have hg : Nat.gcd n (p ^ (j + 1)) = p ^ (j + 1) := by
          have h1 : p ^ (j + 1) / Nat.gcd n (p ^ (j + 1)) = 1 := by simpa using hd
          have hpos : 0 < Nat.gcd n (p ^ (j + 1)) :=
            Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos _)
          have := Nat.div_mul_cancel hgd
          rw [h1, one_mul] at this
          exact this
        have hpm : (p : ℤ) ∣ m := by
          rw [Int.natCast_dvd]
          have : p ^ (j + 1) ∣ n := hg ▸ Nat.gcd_dvd_left n (p ^ (j + 1))
          exact (dvd_pow_self p (Nat.succ_ne_zero j)).trans this
        have hnot : ¬ (¬ (p : ℤ) ∣ m ∧ 3 < p) := fun h => h.1 hpm
        simp only [pow_zero, ArithmeticFunction.moebius_apply_one, Int.cast_one, abs_one,
          one_mul, Nat.totient_one, Nat.cast_one, mul_one, singFactor, hpm, not_true_eq_false, false_and, ↓reduceIte]
        rw [hφ]
        push_cast
        field_simp
        apply le_of_eq
        rw [Nat.succ_eq_add_one, pow_succ]; ring
      · -- `r/(r,m) = p`
        simp only [pow_one, ArithmeticFunction.moebius_apply_prime hp, Int.reduceNeg,
          Int.cast_neg, Int.cast_one, abs_neg, abs_one, one_mul, Nat.totient_prime hp]
        rw [hφ]
        push_cast [Nat.cast_sub hp.one_le]
        have hQ : (p : ℝ) ^ (j + 1) / ((p : ℝ) ^ j * ((p : ℝ) - 1) * ((p : ℝ) - 1)) =
            (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
          field_simp
          ring
        rw [hQ]
        by_cases hpm : (p : ℤ) ∣ m
        · have hnot : ¬ (¬ (p : ℤ) ∣ m ∧ 3 < p) := fun h => h.1 hpm
          simp only [singFactor, hpm, not_true_eq_false, false_and, ↓reduceIte, mul_one]
          have he1 : 1 + 1 / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) := by
            field_simp; ring
          rw [he1, div_le_div_iff_of_pos_left (by positivity) (by positivity) hp1]
          nlinarith
        · have hp2' : p ≠ 2 := by
            rintro rfl
            exact hpm (by exact_mod_cast even_iff_two_dvd.mp he)
          have hp3 : 3 ≤ p := by
            have := hp.two_le; omega
          simp only [singFactor, hpm, ite_false]
          by_cases h3 : 3 < p
          · simp only [not_false_eq_true, h3, and_self, ite_true]
            have h3' : (3 : ℝ) < p := by exact_mod_cast h3
            have hp2r : (0 : ℝ) < (p : ℝ) - 2 := by linarith
            apply le_of_eq
            field_simp
            ring
          · have : p = 3 := by omega
            subst this
            norm_num
    · have hμ : ArithmeticFunction.moebius (p ^ i) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp; omega
      rw [hμ]
      simp only [Int.cast_zero, abs_zero, zero_mul]
      exact weight_nonneg m hp
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hg : Nat.gcd n (a * b) = Nat.gcd n a * Nat.gcd n b := Nat.Coprime.gcd_mul n hab
    have hga : Nat.gcd n a ∣ a := Nat.gcd_dvd_right _ _
    have hgb : Nat.gcd n b ∣ b := Nat.gcd_dvd_right _ _
    have hdiv : a * b / Nat.gcd n (a * b) = (a / Nat.gcd n a) * (b / Nat.gcd n b) := by
      rw [hg, Nat.div_mul_div_comm hga hgb]
    have hcop : Nat.Coprime (a / Nat.gcd n a) (b / Nat.gcd n b) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hgb)
        (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hga) hab)
    rw [hdiv, Nat.Coprime.primeFactors_mul hab,
      Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab),
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hcop, Nat.totient_mul hab]
    have hA := iha ha0
    have hB := ihb hb0
    have hA0 : 0 ≤ |(ArithmeticFunction.moebius (a / Nat.gcd n a) : ℝ)| *
        ((a : ℝ) / ((a.totient : ℝ) * ((a / Nat.gcd n a).totient : ℝ))) := by positivity
    have hB0 : 0 ≤ ∏ p ∈ b.primeFactors,
        singFactor m p * (if ¬ (p : ℤ) ∣ m ∧ 3 < p then 1 / ((p : ℝ) - 2) else 1) :=
      Finset.prod_nonneg fun p hp => weight_nonneg m (Nat.prime_of_mem_primeFactors hp)
    have hQ0 : 0 ≤ |(ArithmeticFunction.moebius (b / Nat.gcd n b) : ℝ)| *
        ((b : ℝ) / ((b.totient : ℝ) * ((b / Nat.gcd n b).totient : ℝ))) := by positivity
    calc |((ArithmeticFunction.moebius (a / Nat.gcd n a) * ArithmeticFunction.moebius (b / Nat.gcd n b) : ℤ) : ℝ)| *
          (((a * b : ℕ) : ℝ) / ((((a.totient * b.totient : ℕ)) : ℝ) *
            (((a / Nat.gcd n a).totient * (b / Nat.gcd n b).totient : ℕ) : ℝ)))
        = (|(ArithmeticFunction.moebius (a / Nat.gcd n a) : ℝ)| *
            ((a : ℝ) / ((a.totient : ℝ) * ((a / Nat.gcd n a).totient : ℝ)))) *
          (|(ArithmeticFunction.moebius (b / Nat.gcd n b) : ℝ)| *
            ((b : ℝ) / ((b.totient : ℝ) * ((b / Nat.gcd n b).totient : ℝ)))) := by
          push_cast
          rw [abs_mul]
          ring
      _ ≤ _ := mul_le_mul hA hB hQ0 (hA0.trans hA)

/-- The local factors split along the primes dividing `r`:
`𝔖(m) = ∏_{p ∣ r} (local factor) × ∏_{p ∤ r} (local factor)`, for `m ≠ 0`, `r ≥ 1`.
The product over `p ∤ r` converges since `Σ 1/(p-1)^2` does. -/
theorem singSeries_split (m : ℤ) (hm : m ≠ 0) (r : ℕ) (hr : r ≠ 0) :
    singSeries m = (∏ p ∈ r.primeFactors, singFactor m p) *
      ∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else singFactor m p) := by
  classical
  set s : Finset Nat.Primes := r.primeFactors.subtype Nat.Prime with hs
  have hout : ∀ p : Nat.Primes, p ∉ s → ¬ (p : ℕ) ∣ r := by
    intro p hp hdvd
    apply hp
    exact (Finset.mem_subtype (p := Nat.Prime) (a := (p : {x // Nat.Prime x}))).mpr
      (Nat.mem_primeFactors.mpr ⟨p.2, hdvd, hr⟩)
  have hh : Multipliable fun p : Nat.Primes => if (p : ℕ) ∣ r then singFactor m p else 1 :=
    multipliable_of_ne_finset_one (s := s) fun p hp => by simp [hout p hp]
  have hprod : (∏' p : Nat.Primes, if (p : ℕ) ∣ r then singFactor m p else 1) =
      ∏ p ∈ r.primeFactors, singFactor m p := by
    rw [tprod_eq_prod (s := s) fun p hp => by simp [hout p hp]]
    refine (Finset.prod_subtype_eq_prod_filter (s := r.primeFactors) (p := Nat.Prime)
      (fun p => if p ∣ r then singFactor m p else 1)).trans ?_
    rw [Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp]
    exact Finset.prod_congr rfl fun p hp => by simp [Nat.dvd_of_mem_primeFactors hp]
  -- the product over `p ∤ r` converges
  set u : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ r then 0 else
    (if ((p : ℕ) : ℤ) ∣ m then 1 / (((p : ℕ) : ℝ) - 1) else -(1 / (((p : ℕ) : ℝ) - 1) ^ 2))
    with hu
  have hsq : Summable fun p : Nat.Primes => 1 / (((p : ℕ) : ℝ)) ^ 2 :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective
  set t : Finset Nat.Primes := m.natAbs.primeFactors.subtype Nat.Prime with ht
  have hind : Summable fun p : Nat.Primes => if ((p : ℕ) : ℤ) ∣ m then (1 : ℝ) else 0 := by
    apply summable_of_ne_finset_zero (s := t)
    intro p hp
    have : ¬ ((p : ℕ) : ℤ) ∣ m := by
      intro hdvd
      apply hp
      exact (Finset.mem_subtype (p := Nat.Prime) (a := (p : {x // Nat.Prime x}))).mpr
        (Nat.mem_primeFactors.mpr ⟨p.2, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hm⟩)
    simp [this]
  have hus : Summable u := by
    refine (hind.add (hsq.mul_left 4)).of_norm_bounded fun p => ?_
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) - 1 := by linarith
    have hpos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hb1 : 1 / (((p : ℕ) : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    have hb2 : 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 4 * (1 / ((p : ℕ) : ℝ) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hq : 0 ≤ 4 * (1 / ((p : ℕ) : ℝ) ^ 2) := by positivity
    simp only [hu, Real.norm_eq_abs]
    split_ifs with h1 h2 h2
    · simp only [abs_zero]; positivity
    · simp only [abs_zero]; linarith
    · rw [abs_of_nonneg (by positivity)]; linarith
    · rw [abs_neg, abs_of_nonneg (by positivity)]; simp only [zero_add]; exact hb2
  have hg : Multipliable fun p : Nat.Primes => if (p : ℕ) ∣ r then 1 else singFactor m p := by
    have := Real.multipliable_one_add_of_summable hus
    refine this.congr fun p => ?_
    simp only [hu, singFactor]
    split_ifs <;> ring
  rw [singSeries_eq, ← hprod, ← hh.tprod_mul hg]
  congr 1
  funext p
  split_ifs <;> simp

/-- P0082 page 363 display 21, from Montgomery and Vaughan 1975 formula 8.5: for an even
`m ≠ 0` and any Dirichlet character `χ` of modulus `r ≥ 1`,
`|𝔖~(m)| ≤ 𝔖(m) ∏_{p ∣ r, p ∤ m, p > 3} 1 / (p - 2)`. PROVED. -/
theorem display21 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (m : ℤ) (hm : m ≠ 0)
    (he : Even m) :
    |twistedSing χ m| ≤ singSeries m *
      ∏ p ∈ r.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ m ∧ 3 < p), 1 / ((p : ℝ) - 2) := by
  have hr : r ≠ 0 := NeZero.ne r
  set T := ∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else singFactor m p) with hT
  have hT0 : 0 ≤ T := tprod_nonneg fun p => by
    split_ifs
    · norm_num
    · exact singFactor_nonneg m p.2
  have hχ : |(χ (-1)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  have hloc := local_bound m he r hr
  rw [← int_gcd_eq] at hloc
  have hA0 : 0 ≤ (r : ℝ) / ((r.totient : ℝ) * ((r / Int.gcd m r).totient : ℝ)) := by
    positivity
  have hW : (∏ p ∈ r.primeFactors,
        singFactor m p * (if ¬ (p : ℤ) ∣ m ∧ 3 < p then 1 / ((p : ℝ) - 2) else 1)) =
      (∏ p ∈ r.primeFactors, singFactor m p) *
        ∏ p ∈ r.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ m ∧ 3 < p), 1 / ((p : ℝ) - 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_filter]
  rw [singSeries_split m hm r hr, ← hT]
  unfold twistedSing
  rw [← hT, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hT0]
  calc |(χ (-1)).re| * |(ArithmeticFunction.moebius (r / Int.gcd m r) : ℝ)| *
        ((r : ℝ) / ((r.totient : ℝ) * ((r / Int.gcd m r).totient : ℝ))) * T
      ≤ 1 * (|(ArithmeticFunction.moebius (r / Int.gcd m r) : ℝ)| *
        ((r : ℝ) / ((r.totient : ℝ) * ((r / Int.gcd m r).totient : ℝ)))) * T := by
        rw [← mul_assoc]
        gcongr
    _ ≤ (∏ p ∈ r.primeFactors,
        singFactor m p * (if ¬ (p : ℤ) ∣ m ∧ 3 < p then 1 / ((p : ℝ) - 2) else 1)) * T := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hloc hT0
    _ = _ := by rw [hW]; ring

/-- P0082 page 363 case ii b, the sentence after display 21: if the product in display 21 is
not empty, that is some prime `p > 3` divides `r` but not `m`, then
`|𝔖~(m)| ≤ 𝔖(m) / 3`. PROVED. -/
theorem display21_third {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (m : ℤ) (hm : m ≠ 0)
    (he : Even m) (hex : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) :
    |twistedSing χ m| ≤ singSeries m / 3 := by
  obtain ⟨p, hp, hpr, hp3, hpm⟩ := hex
  set s := r.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ m ∧ 3 < p) with hs
  have hps : p ∈ s := by
    rw [hs, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, hpr, NeZero.ne r⟩, hpm, hp3⟩
  have hfac : ∀ q ∈ s, 0 ≤ 1 / ((q : ℝ) - 2) ∧ 1 / ((q : ℝ) - 2) ≤ 1 / 3 := by
    intro q hq
    rw [hs, Finset.mem_filter] at hq
    have : (3 : ℝ) < q := by exact_mod_cast hq.2.2
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    have h4 : (5 : ℝ) ≤ q := by
      have h5 : 5 ≤ q := by
        have h3 : 3 < q := hq.2.2
        rcases Nat.lt_or_ge q 5 with h | h
        · interval_cases q
          exact absurd hqp (by decide)
        · exact h
      exact_mod_cast h5
    refine ⟨by apply div_nonneg <;> linarith, ?_⟩
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hprod : ∏ q ∈ s, 1 / ((q : ℝ) - 2) ≤ 1 / 3 := by
    rw [← Finset.mul_prod_erase s _ hps]
    have hrest : ∏ q ∈ s.erase p, 1 / ((q : ℝ) - 2) ≤ 1 :=
      Finset.prod_le_one₀ (fun q hq => (hfac q (Finset.mem_of_mem_erase hq)).1)
        (fun q hq => (hfac q (Finset.mem_of_mem_erase hq)).2.trans (by norm_num))
    have hrest0 : 0 ≤ ∏ q ∈ s.erase p, 1 / ((q : ℝ) - 2) :=
      Finset.prod_nonneg fun q hq => (hfac q (Finset.mem_of_mem_erase hq)).1
    calc 1 / ((p : ℝ) - 2) * ∏ q ∈ s.erase p, 1 / ((q : ℝ) - 2) ≤ 1 / 3 * 1 :=
          mul_le_mul (hfac p hps).2 hrest hrest0 (by norm_num)
      _ = 1 / 3 := by ring
  calc |twistedSing χ m| ≤ singSeries m * ∏ q ∈ s, 1 / ((q : ℝ) - 2) := display21 χ m hm he
    _ ≤ singSeries m * (1 / 3) := mul_le_mul_of_nonneg_left hprod (singSeries_nonneg m)
    _ = singSeries m / 3 := by ring

/-- P0082 page 363 case ii b, the trivial bound `|I~(m)| ≤ m` for display 13: each term
`(k (m - k))^(β - 1)` is at most one since `k (m - k) ≥ 1` and `β ≤ 1`, and there are fewer
than `m` terms. PROVED. -/
theorem Itilde_abs_le (β P : ℝ) (hβ : β ≤ 1) (m : ℤ) (hm : 0 ≤ m) :
    |Itilde β P m| ≤ m := by
  unfold Itilde
  set s := (Finset.Ioo (0 : ℤ) m).filter
    (fun k : ℤ => P < (k : ℝ) ∧ (k : ℝ) < (m : ℝ) - P) with hs
  have hterm : ∀ k ∈ s, 0 ≤ ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1) ∧
      ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1) ≤ 1 := by
    intro k hk
    rw [hs, Finset.mem_filter, Finset.mem_Ioo] at hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1.1
    have hk2 : (1 : ℝ) ≤ (m : ℝ) - k := by
      have : k + 1 ≤ m := hk.1.2
      have : ((k + 1 : ℤ) : ℝ) ≤ m := by exact_mod_cast this
      push_cast at this; linarith
    have hb : (1 : ℝ) ≤ (k : ℝ) * ((m : ℝ) - k) := by nlinarith
    exact ⟨Real.rpow_nonneg (by linarith) _,
      Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)⟩
  have h0 : 0 ≤ ∑ k ∈ s, ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1) :=
    Finset.sum_nonneg fun k hk => (hterm k hk).1
  rw [abs_of_nonneg h0]
  have hle : ∑ k ∈ s, ((k : ℝ) * ((m : ℝ) - (k : ℝ))) ^ (β - 1) ≤ (s.card : ℝ) := by
    have := Finset.sum_le_card_nsmul s _ 1 fun k hk => (hterm k hk).2
    simpa using this
  have hcard : (s.card : ℤ) ≤ m := by
    have h1 : s.card ≤ (Finset.Ioo (0 : ℤ) m).card := Finset.card_filter_le _ _
    rw [Int.card_Ioo] at h1
    omega
  have hcardR : (s.card : ℝ) ≤ m := by exact_mod_cast hcard
  linarith

end LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082

#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.singFactor_nonneg
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.singSeries_nonneg
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.local_bound
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.singSeries_split
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.display21
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.display21_third
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082.Itilde_abs_le
