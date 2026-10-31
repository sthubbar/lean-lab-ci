/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Lemma 8.2 with (8.1), (7.1), (7.6).
`Lemma82` of MajorArcs.lean PROVED unconditionally, as `lemma82`.

Plain math. Let `q = q_0 = ∏_{p < Z} p`, `φ = φ(q)`, `R_0 ⊆ [1, q]` the reduced residues of (4.8).
1. `ramanujan_muphi`: for every `n`, `μ(d)/φ(d) = φ⁻¹ Σ_{x ∈ U q} e(xn/q)`, `d = q/(q, n)`.
   Both sides are `∏_{p<Z} (1 if p | n, -1/(p-1) otherwise)`, the left by multiplicativity of
   `μ`, `φ` and `gcd`, the right by `ram_mul` and `ram_prime` of LocalFactors.lean.
2. `inner_eq`: for `w | q`, `Σ_{ℓ<q} μ(q_ℓ)/φ(q_ℓ) Σ_{r∈R_0} e(-ℓr/q) = (q/φ) Σ_{r∈R_0} e(ra/w)`,
   by 1, `q_ℓ = q/(q, aq/w + ℓ)` and orthogonality `Σ_{ℓ<q} e(ℓj/q) = q [q | j]`.
3. `sum_divisors_U`: `Σ_{w | q} Σ_{a ∈ U w} e(aj/w) = q [q | j]`, the fractions `a/w` with
   `w | q`, `(a,w) = 1` being exactly the `b/q`, `1 ≤ b ≤ q`.
4. `Gq0_eq_count`: `G(q_0) = q φ⁻³ #{(r₁,r₂,r₃) ∈ R_0³ : r₁+r₂+r₃ ≡ m mod q}`.
5. `count_eq_prod`: by CRT that count is `∏_{p<Z} N_p(m)`.
6. `lemma82`: hence `G(q_0) = ∏_{p<Z} p N_p(m)/(p-1)³`, which is Lemma 8.2 with the local
   factor `G(p) = p N_p(m)/(p-1)³`. The hypothesis `m` odd is not needed.

AI-written Lean code, Claude, run 20261021T0303Z-27628, unit U-1338. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.LocalFactors

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Lemma82

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
  LeanLab.SparseTernary.LocalFactors

/-! ### Orthogonality -/

theorem ee_eq_one_iff (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ee ((j : ℝ) / q) = 1 ↔ (q : ℤ) ∣ j := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h1 : ((((j : ℝ) / q : ℝ)) : ℂ) = n := by
      apply mul_left_cancel₀ hpi; rw [hn]; ring
    push_cast at h1
    have h2 : (j : ℂ) = n * q := by rw [← h1]; field_simp
    have h3 : j = n * q := by exact_mod_cast h2
    exact ⟨n, by rw [h3]; ring⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    rw [mul_div_cancel_left₀ _ hq']; ring

theorem sum_range_ee (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ∑ ℓ ∈ range q, ee ((ℓ : ℝ) * (j : ℝ) / q) = if (q : ℤ) ∣ j then (q : ℂ) else 0 := by
  have hz : ∀ ℓ : ℕ, ee ((ℓ : ℝ) * (j : ℝ) / q) = ee ((j : ℝ) / q) ^ ℓ := by
    intro ℓ; rw [← ee_nat_mul]; congr 1; ring
  simp_rw [hz]
  split_ifs with h
  · rw [(ee_eq_one_iff q hq j).mpr h]; simp
  · have hne : ee ((j : ℝ) / q) ≠ 1 := fun h' => h ((ee_eq_one_iff q hq j).mp h')
    rw [geom_sum_eq hne, ← ee_nat_mul]
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have : (q : ℝ) * ((j : ℝ) / q) = (j : ℝ) := by field_simp
    rw [this, ee_int]; simp

theorem conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat]
  push_cast; ring

/-! ### Products over a finite set of primes -/

theorem coprime_prod_of_not_mem {s : Finset ℕ} {p : ℕ} (hs : ∀ q ∈ s, q.Prime) (hpp : p.Prime)
    (hp : p ∉ s) : p.Coprime (∏ q ∈ s, q) :=
  Nat.Coprime.prod_right fun q hq =>
    (Nat.coprime_primes hpp (hs q hq)).mpr (fun h => hp (h ▸ hq))

theorem ram_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    ram (∏ p ∈ s, p) n = ∏ p ∈ s, ram p n := by
  induction s using Finset.induction_on with
  | empty => simp [ram_one]
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp,
      ram_mul p _ n hpp.one_lt.le (prod_pos fun q hq => (hs' q hq).pos)
        (coprime_prod_of_not_mem hs' hpp hp), ih hs']

theorem totient_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (((∏ p ∈ s, p).totient : ℕ) : ℝ) = ∏ p ∈ s, ((p : ℝ) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp, Nat.totient_mul (coprime_prod_of_not_mem hs' hpp hp),
      Nat.totient_prime hpp, Nat.cast_mul, ih hs', Nat.cast_sub hpp.one_le]
    simp

theorem muphi_mul {a b : ℕ} (h : a.Coprime b) : muphi (a * b) = muphi a * muphi b := by
  unfold muphi
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  rw [div_mul_div_comm]

theorem muphi_one : muphi 1 = 1 := by simp [muphi]

theorem muphi_prime {p : ℕ} (hp : p.Prime) : muphi p = -1 / ((p : ℝ) - 1) := by
  unfold muphi
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  simp

theorem muphi_step {p P n : ℕ} (hpp : p.Prime) (hcop : p.Coprime P) :
    muphi ((p * P) / Nat.gcd (p * P) n) =
      (if p ∣ n then 1 else -1 / ((p : ℝ) - 1)) * muphi (P / Nat.gcd P n) := by
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul n hcop, Nat.gcd_comm n p, Nat.gcd_comm n P,
    ← Nat.div_mul_div_comm (Nat.gcd_dvd_left p n) (Nat.gcd_dvd_left P n)]
  have hc2 : (p / Nat.gcd p n).Coprime (P / Nat.gcd P n) :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left p n))
      (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left P n)) hcop)
  rw [muphi_mul hc2]
  congr 1
  split_ifs with hd
  · rw [Nat.gcd_eq_left hd, Nat.div_self hpp.pos, muphi_one]
  · have : Nat.gcd p n = 1 := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hd
    rw [this, Nat.div_one, muphi_prime hpp]

theorem muphi_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    muphi ((∏ p ∈ s, p) / Nat.gcd (∏ p ∈ s, p) n) =
      ∏ p ∈ s, (if p ∣ n then 1 else -1 / ((p : ℝ) - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp [muphi_one]
  | @insert p s hp ih =>
    have hpp := hs p (mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
    rw [prod_insert hp, prod_insert hp, muphi_step hpp (coprime_prod_of_not_mem hs' hpp hp),
      ih hs']

/-! ### Step 1: the Ramanujan sum evaluation of `μ(d)/φ(d)` at `q_0` -/

theorem ram_q0 (Z n : ℕ) : ram (q0 Z) n =
    ((∏ p ∈ Nat.primesBelow Z, (if p ∣ n then (p : ℝ) - 1 else -1) : ℝ) : ℂ) := by
  unfold q0
  rw [ram_prod _ (fun p hp => Nat.prime_of_mem_primesBelow hp)]
  push_cast
  refine prod_congr rfl fun p hp => ?_
  rw [ram_prime p n (Nat.prime_of_mem_primesBelow hp)]
  try (split_ifs <;> simp)

theorem sum_U_ee (q n : ℕ) : ∑ x ∈ U q, ee ((x : ℝ) * n / q) = (starRingEnd ℂ) (ram q n) := by
  unfold ram
  rw [map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [conj_ee, neg_neg]

theorem ramanujan_muphi (Z n : ℕ) :
    (muphi (q0 Z / Nat.gcd (q0 Z) n) : ℂ) =
      1 / ((q0 Z).totient : ℂ) * ∑ x ∈ U (q0 Z), ee ((x : ℝ) * n / q0 Z) := by
  have hs : ∀ p ∈ Nat.primesBelow Z, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  rw [sum_U_ee, ram_q0, Complex.conj_ofReal]
  have htot : (((q0 Z).totient : ℕ) : ℂ) = (((∏ p ∈ Nat.primesBelow Z, ((p : ℝ) - 1)) : ℝ) : ℂ) := by
    rw [← totient_prod _ hs, Complex.ofReal_natCast]; rfl
  rw [htot]
  have hmu : muphi (q0 Z / Nat.gcd (q0 Z) n) =
      ∏ p ∈ Nat.primesBelow Z, (if p ∣ n then 1 else -1 / ((p : ℝ) - 1)) := muphi_prod _ hs n
  rw [hmu]
  have key : ∏ p ∈ Nat.primesBelow Z, (if p ∣ n then 1 else -1 / ((p : ℝ) - 1)) =
      1 / (∏ p ∈ Nat.primesBelow Z, ((p : ℝ) - 1)) *
        ∏ p ∈ Nat.primesBelow Z, (if p ∣ n then (p : ℝ) - 1 else -1) := by
    rw [one_div, ← prod_inv_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have h1 : (p : ℝ) - 1 ≠ 0 := by
      have := (hs p hp).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith
    split_ifs
    · rw [inv_mul_cancel₀ h1]
    · rw [neg_div, one_div, mul_neg_one]
  rw [key, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]

/-! ### Step 2: the inner sum -/

theorem R0_sub_U (Z : ℕ) : R0 Z ⊆ U (q0 Z) := by
  intro r hr
  simp only [R0, mem_filter] at hr
  simp only [U, mem_filter]
  exact ⟨hr.1, hr.2.1⟩

theorem dvd_sub_iff_eq {q x r : ℕ} (hx : x ∈ Icc 1 q) (hr : r ∈ Icc 1 q) :
    (q : ℤ) ∣ ((x : ℤ) - r) ↔ x = r := by
  simp only [mem_Icc] at hx hr
  constructor
  · intro h
    have : (x : ℤ) - r = 0 :=
      Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · rintro rfl; simp

theorem inner_eq (Z w a : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) :
    inner Z w a = (q0 Z : ℂ) / ((q0 Z).totient : ℂ) * ∑ r ∈ R0 Z, ee ((r : ℝ) * a / w) := by
  have hq : 0 < q0 Z := q0_pos Z
  obtain ⟨k, hk⟩ := hw
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  have hkq : q0 Z / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hqR : ((q0 Z : ℕ) : ℝ) = (w : ℝ) * k := by rw [hk]; push_cast; ring
  have key : ∀ ℓ ∈ range (q0 Z), (muphi (qell Z w a ℓ) : ℂ) *
      ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) =
      1 / ((q0 Z).totient : ℂ) * ∑ x ∈ U (q0 Z), ∑ r ∈ R0 Z,
        ee ((x : ℝ) * a / w) * ee ((ℓ : ℝ) * ((((x : ℤ) - r : ℤ)) : ℝ) / q0 Z) := by
    intro ℓ _
    rw [qell_of_dvd a ℓ ⟨k, hk⟩ hw0, ramanujan_muphi, mul_assoc, sum_mul_sum]
    congr 1
    refine sum_congr rfl fun x _ => sum_congr rfl fun r _ => ?_
    rw [← ee_add, ← ee_add]
    congr 1
    rw [hkq, hqR]
    push_cast
    field_simp
    ring
  unfold MajorArcs.inner
  rw [sum_congr rfl key, ← mul_sum, sum_comm]
  have step : ∀ x ∈ U (q0 Z), ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee ((x : ℝ) * a / w) * ee ((ℓ : ℝ) * ((((x : ℤ) - r : ℤ)) : ℝ) / q0 Z) =
      if x ∈ R0 Z then ee ((x : ℝ) * a / w) * (q0 Z : ℂ) else 0 := by
    intro x hx
    rw [sum_comm]
    simp_rw [← mul_sum]
    have hxI : x ∈ Icc 1 (q0 Z) := by simp only [U, mem_filter] at hx; exact hx.1
    have h2 : ∀ r ∈ R0 Z, ∑ ℓ ∈ range (q0 Z), ee ((ℓ : ℝ) * ((((x : ℤ) - r : ℤ)) : ℝ) / q0 Z) =
        if x = r then (q0 Z : ℂ) else 0 := by
      intro r hr
      have hrI : r ∈ Icc 1 (q0 Z) := by simp only [R0, mem_filter] at hr; exact hr.1
      rw [sum_range_ee (q0 Z) hq]
      exact if_congr (dvd_sub_iff_eq hxI hrI) rfl rfl
    rw [sum_congr rfl h2, sum_ite_eq]
    split_ifs <;> simp
  rw [sum_congr rfl step, ← sum_filter]
  have hf : (U (q0 Z)).filter (fun x => x ∈ R0 Z) = R0 Z := by
    ext x; simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨R0_sub_U Z h, h⟩⟩
  rw [hf, ← sum_mul]
  ring

/-! ### Step 3: the fractions `a/w`, `w ∣ q`, are the fractions `b/q` -/

theorem sum_Icc_ee (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ∑ b ∈ Icc 1 q, ee ((b : ℝ) * (j : ℝ) / q) = if (q : ℤ) ∣ j then (q : ℂ) else 0 := by
  rw [← sum_range_ee q hq j]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hI : Icc 1 q = Ico 1 (q + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  have e1 : ∑ ℓ ∈ range (q + 1), ee ((ℓ : ℝ) * (j : ℝ) / q) =
      ∑ ℓ ∈ range q, ee ((ℓ : ℝ) * (j : ℝ) / q) + ee ((q : ℝ) * (j : ℝ) / q) :=
    sum_range_succ _ _
  have e2 : ∑ ℓ ∈ range (q + 1), ee ((ℓ : ℝ) * (j : ℝ) / q) =
      ee (((0 : ℕ) : ℝ) * (j : ℝ) / q) + ∑ ℓ ∈ Ico 1 (q + 1), ee ((ℓ : ℝ) * (j : ℝ) / q) := by
    rw [range_eq_Ico]; exact sum_eq_sum_Ico_succ_bot (by omega) _
  have hq1 : ee ((q : ℝ) * (j : ℝ) / q) = 1 := by
    rw [mul_div_cancel_left₀ _ hq0, ee_int]
  have h0 : ee (((0 : ℕ) : ℝ) * (j : ℝ) / q) = 1 := by simp [ee]
  rw [hq1] at e1; rw [h0] at e2
  rw [hI]
  linear_combination e2.symm.trans e1

theorem sum_divisors_U (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ∑ w ∈ q.divisors, ∑ a ∈ U w, ee ((a : ℝ) * (j : ℝ) / w) =
      if (q : ℤ) ∣ j then (q : ℂ) else 0 := by
  rw [← sum_Icc_ee q hq j, sum_sigma']
  refine sum_bij (fun t _ => t.2 * (q / t.1)) ?_ ?_ ?_ ?_
  · rintro ⟨w, a⟩ ht
    simp only [mem_sigma, Nat.mem_divisors, U, mem_filter, mem_Icc] at ht
    obtain ⟨⟨hwq, -⟩, ⟨ha1, ha2⟩, -⟩ := ht
    have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hwq hq
    have hk : 0 < q / w := Nat.div_pos (Nat.le_of_dvd hq hwq) hw0
    simp only [mem_Icc]
    constructor
    · exact Nat.mul_pos (by omega) hk
    · calc a * (q / w) ≤ w * (q / w) := Nat.mul_le_mul_right _ ha2
        _ = q := Nat.mul_div_cancel' hwq
  · rintro ⟨w, a⟩ ht ⟨w', a'⟩ ht' he
    simp only [mem_sigma, Nat.mem_divisors, U, mem_filter, mem_Icc] at ht ht'
    change a * (q / w) = a' * (q / w') at he
    have hg : ∀ w a : ℕ, w ∣ q → a.Coprime w → Nat.gcd (a * (q / w)) q = q / w := by
      intro w a hwq hc
      obtain ⟨k, hk⟩ := hwq
      have hw0 : 0 < w := Nat.pos_of_dvd_of_pos ⟨k, hk⟩ hq
      have hkq : q / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
      rw [hkq, hk, Nat.gcd_mul_right, hc.gcd_eq_one, one_mul]
    have hk : q / w = q / w' := by
      rw [← hg w a ht.1.1 ht.2.2, ← hg w' a' ht'.1.1 ht'.2.2, he]
    have hww : w = w' := by
      rw [← Nat.div_div_self ht.1.1 (by omega), hk, Nat.div_div_self ht'.1.1 (by omega)]
    subst hww
    have hk0 : 0 < q / w := Nat.div_pos (Nat.le_of_dvd hq ht.1.1)
      (Nat.pos_of_dvd_of_pos ht.1.1 hq)
    have haa : a = a' := Nat.eq_of_mul_eq_mul_right hk0 he
    subst haa; rfl
  · intro b hb
    simp only [mem_Icc] at hb
    have hg0 : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_left _ (by omega)
    refine ⟨⟨q / Nat.gcd b q, b / Nat.gcd b q⟩, ?_, ?_⟩
    · simp only [mem_sigma, Nat.mem_divisors, U, mem_filter, mem_Icc]
      refine ⟨⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right b q), by omega⟩, ⟨?_, ?_⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left b q)) hg0
      · exact Nat.div_le_div_right hb.2
      · exact Nat.coprime_div_gcd_div_gcd hg0
    · simp only
      rw [Nat.div_div_self (Nat.gcd_dvd_right b q) (by omega),
        Nat.div_mul_cancel (Nat.gcd_dvd_left b q)]
  · rintro ⟨w, a⟩ ht
    simp only [mem_sigma, Nat.mem_divisors] at ht
    obtain ⟨⟨hwq, -⟩, -⟩ := ht
    have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hwq hq
    obtain ⟨k, hk⟩ := hwq
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hkq : q / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
    simp only
    congr 1
    rw [hkq, hk]
    have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast
    field_simp

/-! ### Step 4: `G(q_0)` is a count -/

theorem cube_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ r ∈ s, f r) ^ 3 = ∑ t ∈ s ×ˢ s ×ˢ s, f t.1 * f t.2.1 * f t.2.2 := by
  rw [pow_three, sum_mul, sum_product]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_mul, mul_sum, sum_product]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  show f a * (f b * f c) = f a * f b * f c
  ring

/-- The triples of `R_0` summing to `m mod q_0`. -/
def Tset (Z m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD q0 Z])

theorem fq_eq (Z m w : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) :
    fq Z m w = 1 / ((q0 Z).totient : ℂ) ^ 3 * ∑ t ∈ R0 Z ×ˢ R0 Z ×ˢ R0 Z, ∑ a ∈ U w,
      ee ((a : ℝ) * ((((t.1 + t.2.1 + t.2.2 : ℕ) : ℤ) - m : ℤ) : ℝ) / w) := by
  have hq : (q0 Z : ℂ) ≠ 0 := by exact_mod_cast (q0_pos Z).ne'
  have htot : ((q0 Z).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (q0_pos Z)).ne'
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
  have hin := fun a => inner_eq Z w a hw hw0
  unfold fq
  have hU : (Icc 1 w).filter (fun a => a.Coprime w) = U w := rfl
  rw [hU, sum_comm]
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [hin a, mul_pow, cube_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  have e : (-((a : ℝ) * m / w) + ((t.1 : ℝ) * a / w + (t.2.1 : ℝ) * a / w +
      (t.2.2 : ℝ) * a / w)) =
      (a : ℝ) * ((((t.1 + t.2.1 + t.2.2 : ℕ) : ℤ) - m : ℤ) : ℝ) / w := by
    push_cast; field_simp; ring
  rw [← e, ee_add, ee_add, ee_add]
  field_simp

theorem Gq0_eq_count (Z m : ℕ) :
    Gq0 Z m = (q0 Z : ℂ) / ((q0 Z).totient : ℂ) ^ 3 * (#(Tset Z m) : ℂ) := by
  have hq := q0_pos Z
  unfold Gq0
  have h1 : ∀ w ∈ (q0 Z).divisors, fq Z m w = 1 / ((q0 Z).totient : ℂ) ^ 3 *
      ∑ t ∈ R0 Z ×ˢ R0 Z ×ˢ R0 Z, ∑ a ∈ U w,
        ee ((a : ℝ) * ((((t.1 + t.2.1 + t.2.2 : ℕ) : ℤ) - m : ℤ) : ℝ) / w) := by
    intro w hw
    rw [Nat.mem_divisors] at hw
    exact fq_eq Z m w hw.1 (Nat.pos_of_dvd_of_pos hw.1 hq)
  rw [sum_congr rfl h1, ← mul_sum, sum_comm]
  simp_rw [sum_divisors_U (q0 Z) hq]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hf : (R0 Z ×ˢ R0 Z ×ˢ R0 Z).filter (fun t => (q0 Z : ℤ) ∣
      (((t.1 + t.2.1 + t.2.2 : ℕ) : ℤ) - m : ℤ)) = Tset Z m := by
    unfold Tset
    refine filter_congr fun t _ => ?_
    rw [← Nat.modEq_iff_dvd]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hf]
  ring

/-! ### Step 5: CRT, the count is a product of local counts -/

theorem mod_mem_Lset_of_R0 {Z r p : ℕ} (hr : r ∈ R0 Z) (hp : p ∈ Nat.primesBelow Z) :
    r % p ∈ Lset p := by
  simp only [R0, mem_filter] at hr
  obtain ⟨s, hs, hrs⟩ := hr.2.2 p hp
  have h0 := mod_ne_zero_of_coprime (Nat.prime_of_mem_primesBelow hp) (dvd_q0 hp) hr.2.1
  unfold Lset; simp only [mem_filter, mem_image]
  exact ⟨⟨s, hs, hrs.symm⟩, h0⟩

theorem eq_of_R0 {Z r r' : ℕ} (hr : r ∈ R0 Z) (hr' : r' ∈ R0 Z)
    (h : ∀ p ∈ Nat.primesBelow Z, r % p = r' % p) : r = r' := by
  simp only [R0, mem_filter, mem_Icc] at hr hr'
  have hq := modEq_q0 (Z := Z) (a := r) (b := r') h
  rcases le_total r r' with h' | h'
  · have hd := (Nat.modEq_iff_dvd' h').mp hq
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := (Nat.modEq_iff_dvd' h').mp hq.symm
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

/-- The local triple set whose size is `N_p(m)`. -/
def Nset (p m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Lset p ×ˢ Lset p ×ˢ Lset p).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD p])

theorem count_eq_prod (Z m : ℕ) : #(Tset Z m) = ∏ p ∈ Nat.primesBelow Z, Np p m := by
  have hN : ∀ p, Np p m = #(Nset p m) := fun p => rfl
  simp_rw [hN]
  rw [← card_pi]
  refine card_bij (fun t _ => fun p _ => (t.1 % p, t.2.1 % p, t.2.2 % p)) ?_ ?_ ?_
  · intro t ht
    simp only [Tset, mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, hs⟩ := ht
    rw [mem_pi]
    intro p hp
    simp only [Nset, mem_filter, mem_product]
    refine ⟨⟨mod_mem_Lset_of_R0 h1 hp, mod_mem_Lset_of_R0 h2 hp, mod_mem_Lset_of_R0 h3 hp⟩, ?_⟩
    exact (((Nat.mod_modEq _ _).add (Nat.mod_modEq _ _)).add (Nat.mod_modEq _ _)).trans
      (hs.of_dvd (dvd_q0 hp))
  · intro t ht t' ht' he
    simp only [Tset, mem_filter, mem_product] at ht ht'
    have hc : ∀ p ∈ Nat.primesBelow Z,
        t.1 % p = t'.1 % p ∧ t.2.1 % p = t'.2.1 % p ∧ t.2.2 % p = t'.2.2 % p := by
      intro p hp
      have := congrFun (congrFun he p) hp
      simp only [Prod.mk.injEq] at this
      exact this
    have e1 := eq_of_R0 ht.1.1 ht'.1.1 (fun p hp => (hc p hp).1)
    have e2 := eq_of_R0 ht.1.2.1 ht'.1.2.1 (fun p hp => (hc p hp).2.1)
    have e3 := eq_of_R0 ht.1.2.2 ht'.1.2.2 (fun p hp => (hc p hp).2.2)
    exact Prod.ext e1 (Prod.ext e2 e3)
  · intro f hf
    rw [mem_pi] at hf
    have hT : ∀ p (hp : p ∈ Nat.primesBelow Z), (f p hp).1 ∈ Lset p ∧ (f p hp).2.1 ∈ Lset p ∧
        (f p hp).2.2 ∈ Lset p ∧ (f p hp).1 + (f p hp).2.1 + (f p hp).2.2 ≡ m [MOD p] := by
      intro p hp
      have := hf p hp
      simp only [Nset, mem_filter, mem_product] at this
      exact ⟨this.1.1, this.1.2.1, this.1.2.2, this.2⟩
    let x : ℕ → ℕ × ℕ × ℕ := fun p => if hp : p ∈ Nat.primesBelow Z then f p hp else (0, 0, 0)
    have hx : ∀ p (hp : p ∈ Nat.primesBelow Z), x p = f p hp := by
      intro p hp; show (if h : p ∈ Nat.primesBelow Z then f p h else (0, 0, 0)) = f p hp
      rw [dif_pos hp]
    have hs : ∀ p ∈ Nat.primesBelow Z, id p ≠ 0 := fun p hp =>
      (Nat.prime_of_mem_primesBelow hp).ne_zero
    have pp : Set.Pairwise (↑(Nat.primesBelow Z) : Set ℕ) (Function.onFun Nat.Coprime id) :=
      fun p hp q hq hne => (Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
        (Nat.prime_of_mem_primesBelow hq)).mpr hne
    let k₁ := Nat.chineseRemainderOfFinset (fun p => (x p).1) id (Nat.primesBelow Z) hs pp
    let k₂ := Nat.chineseRemainderOfFinset (fun p => (x p).2.1) id (Nat.primesBelow Z) hs pp
    let k₃ := Nat.chineseRemainderOfFinset (fun p => (x p).2.2) id (Nat.primesBelow Z) hs pp
    have m1 : rep Z k₁ ∈ R0 Z := rep_mem_R0 Z k₁ (fun p => (x p).1)
      (fun p hp => by show (x p).1 ∈ Lset p; rw [hx p hp]; exact (hT p hp).1) k₁.2
    have m2 : rep Z k₂ ∈ R0 Z := rep_mem_R0 Z k₂ (fun p => (x p).2.1)
      (fun p hp => by show (x p).2.1 ∈ Lset p; rw [hx p hp]; exact (hT p hp).2.1) k₂.2
    have m3 : rep Z k₃ ∈ R0 Z := rep_mem_R0 Z k₃ (fun p => (x p).2.2)
      (fun p hp => by show (x p).2.2 ∈ Lset p; rw [hx p hp]; exact (hT p hp).2.2.1) k₃.2
    have l1 : ∀ p ∈ Nat.primesBelow Z, rep Z k₁ ≡ (x p).1 [MOD p] := fun p hp =>
      ((rep_modEq Z k₁).of_dvd (dvd_q0 hp)).trans (k₁.2 p hp)
    have l2 : ∀ p ∈ Nat.primesBelow Z, rep Z k₂ ≡ (x p).2.1 [MOD p] := fun p hp =>
      ((rep_modEq Z k₂).of_dvd (dvd_q0 hp)).trans (k₂.2 p hp)
    have l3 : ∀ p ∈ Nat.primesBelow Z, rep Z k₃ ≡ (x p).2.2 [MOD p] := fun p hp =>
      ((rep_modEq Z k₃).of_dvd (dvd_q0 hp)).trans (k₃.2 p hp)
    have hlt : ∀ p (hp : p ∈ Nat.primesBelow Z) (y : ℕ), y ∈ Lset p → y % p = y := by
      intro p hp y hy
      have := Lset_sub p (Nat.prime_of_mem_primesBelow hp).pos hy
      simp only [mem_Ico] at this
      exact Nat.mod_eq_of_lt this.2
    refine ⟨(rep Z k₁, rep Z k₂, rep Z k₃), ?_, ?_⟩
    · simp only [Tset, mem_filter, mem_product]
      refine ⟨⟨m1, m2, m3⟩, ?_⟩
      apply modEq_q0
      intro p hp
      have := (hT p hp).2.2.2
      rw [← hx p hp] at this
      exact (((l1 p hp).add (l2 p hp)).add (l3 p hp)).trans this
    · funext p hp
      have a1 : rep Z k₁ % p = (f p hp).1 := by
        have := l1 p hp; unfold Nat.ModEq at this; rw [this, hx p hp, hlt p hp _ (hT p hp).1]
      have a2 : rep Z k₂ % p = (f p hp).2.1 := by
        have := l2 p hp; unfold Nat.ModEq at this; rw [this, hx p hp, hlt p hp _ (hT p hp).2.1]
      have a3 : rep Z k₃ % p = (f p hp).2.2 := by
        have := l3 p hp; unfold Nat.ModEq at this
        rw [this, hx p hp, hlt p hp _ (hT p hp).2.2.1]
      rw [a1, a2, a3]

/-! ### Step 6: Lemma 8.2 -/

/-- **Lemma 8.2 with the local factor `G(p) = p N_p(m)/(p-1)³`, PROVED unconditionally.** -/
theorem lemma82 : Lemma82 := by
  intro Z m _
  have hs : ∀ p ∈ Nat.primesBelow Z, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  rw [Gq0_eq_count, count_eq_prod]
  have hq : ((q0 Z : ℕ) : ℝ) = ∏ p ∈ Nat.primesBelow Z, (p : ℝ) := by
    unfold q0; exact Nat.cast_prod _ _
  have htot : (((q0 Z).totient : ℕ) : ℝ) = ∏ p ∈ Nat.primesBelow Z, ((p : ℝ) - 1) := by
    unfold q0; exact totient_prod _ hs
  have hreal : ((q0 Z : ℕ) : ℝ) / (((q0 Z).totient : ℕ) : ℝ) ^ 3 *
      (((∏ p ∈ Nat.primesBelow Z, Np p m : ℕ)) : ℝ) = Gprod Z m := by
    rw [hq, htot, Gprod]
    push_cast
    rw [← prod_pow, ← prod_div_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    ring
  rw [← hreal]
  push_cast
  try ring

/-- **MajorLower, CONDITIONAL ON `Major618 A B`, `Tail72 A B`** only. -/
theorem majorLower_of_analytic (A B : ℕ) (hA : 1 ≤ A) (hB : 36 * A + 3 ≤ B)
    (h618 : Major618 A B) (h72 : Tail72 A B) :
    MajorLower A B (9 * (A : ℝ) + 1) :=
  majorLower_of_three A B hA hB h618 h72 lemma82

/-- **RepProp A, CONDITIONAL ON `Minor516W A B`, `Major618 A B`, `Tail72 A B`** only. -/
theorem repProp_of_analytic (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B)
    (hB2 : 28 * A + 13 ≤ B) (hmin : RepAssembly.Minor516W A B) (h618 : Major618 A B)
    (h72 : Tail72 A B) : RepProp A :=
  repProp_of_inputs A B hA hB1 hB2 hmin h618 h72 lemma82 euler716

/-! ### Vacuity tests -/

/-- `lemma82` at `Z = 4`, `q_0 = 6`, `m = 7`: a genuine instance with two primes. -/
example : Gq0 4 7 = (Gprod 4 7 : ℂ) := lemma82 4 7 ⟨3, by norm_num⟩

/-- The count `#T` at `Z = 4` is a product of two local counts. -/
example : #(Tset 4 7) = ∏ p ∈ Nat.primesBelow 4, Np p 7 := count_eq_prod 4 7

end LeanLab.SparseTernary.Lemma82
