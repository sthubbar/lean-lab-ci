import Mathlib

/-!
# Wu 2004 Lemma 4.1, the pointwise weighted inequality, exact form

P0036 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114, 2004, arXiv 0705.1652, Section 4, Lemma 4.1.
Unit U-5400, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.

For a finite set `A` of naturals, `d, N : ℕ` and reals `w ≤ z`, with
`S(A_e; P(D), y) = #{a ∈ A : e ∣ a, no prime q < y with q ∤ D divides a}`, and with Wu's
`Ω₁ = 2 S(A_d; P(dN), w)`,
`Ω₂ = Σ_{w ≤ p < z, (p, N) = 1} S(A_{dp}; P(dN), w)`,
`Ω₃ = Σ_{w ≤ p₁ < p₂ < p₃ < z, (p₁p₂p₃, N) = 1} S(A_{dp₁p₂p₃}; P(dp₁N), p₂)`,
`lemma41_exact` proves
`2 S(A_d; P(dN), z) ≤ Ω₁ - Ω₂ + Ω₃ + E`, `E = Σ_{w ≤ p < z, (p, N) = 1, p ∣ d} S(A_{dp}; P(dN), w)`,
for EVERY `A`, `d`, `N`, `w ≤ z`, with no `O(N^{1-η})` term. Wu takes `w = d̲^{1/s'}`,
`z = d̲^{1/s}`, `A = {N - p}`, sums against `σ(d) ≥ 0` and absorbs his `p₁ = p₂` terms in
`O(N^{1-η})`; here those terms are not needed at all, and the only error is `E`, the terms with
`p ∣ d`, which count `a` with `p² ∣ a` and which Wu's sum over `(p, N) = 1` includes silently.
The proof is pointwise in `a`: if `r` primes of `[w, z)` coprime to `dN` divide `a`, the
right side minus the left is `2 - r + max(r - 2, 0) - 2·[r = 0] ≥ 0`.
Binary Goldbach is OPEN; this is one combinatorial step of an upper bound sieve.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu41

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`. -/
def Sifted (D : ℕ) (y : ℝ) (a : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < y → ¬ q ∣ D → ¬ q ∣ a

/-- `S(A_e; P(D), y)`. -/
def S (A : Finset ℕ) (e D : ℕ) (y : ℝ) : ℕ :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def PS (N : ℕ) (w z : ℝ) : Finset ℕ :=
  {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N}

/-- Triples `p₁ < p₂ < p₃` from `PS N w z`. -/
def triples (N : ℕ) (w z : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  {t ∈ (PS N w z ×ˢ PS N w z) ×ˢ PS N w z | t.1.1 < t.1.2 ∧ t.1.2 < t.2}

/-- Wu's `Ω₁`. -/
def Ω₁ (A : Finset ℕ) (d N : ℕ) (w : ℝ) : ℕ := 2 * S A d (d * N) w

/-- Wu's `Ω₂`. -/
def Ω₂ (A : Finset ℕ) (d N : ℕ) (w z : ℝ) : ℕ := ∑ p ∈ PS N w z, S A (d * p) (d * N) w

/-- Wu's `Ω₃`. -/
def Ω₃ (A : Finset ℕ) (d N : ℕ) (w z : ℝ) : ℕ :=
  ∑ t ∈ triples N w z, S A (d * t.1.1 * t.1.2 * t.2) (d * t.1.1 * N) t.1.2

/-- The terms of `Ω₂` with `p ∣ d`. -/
def Err (A : Finset ℕ) (d N : ℕ) (w z : ℝ) : ℕ :=
  ∑ p ∈ {p ∈ PS N w z | p ∣ d}, S A (d * p) (d * N) w

lemma S_eq_sum (A : Finset ℕ) (e D : ℕ) (y : ℝ) :
    S A e D y = ∑ a ∈ A, if e ∣ a ∧ Sifted D y a then 1 else 0 := by
  unfold S; rw [card_filter]

lemma sifted_mono {D : ℕ} {y y' : ℝ} (h : y ≤ y') {a : ℕ} (ha : Sifted D y' a) :
    Sifted D y a := fun q hq hqy hqD => ha q hq (lt_of_lt_of_le hqy h) hqD

lemma mem_PS {N : ℕ} {w z : ℝ} {p : ℕ} :
    p ∈ PS N w z ↔ p.Prime ∧ w ≤ p ∧ (p : ℝ) < z ∧ p.Coprime N := by
  unfold PS
  simp only [mem_filter, mem_range, and_iff_right_iff_imp]
  rintro ⟨-, -, hz, -⟩
  exact Nat.lt_ceil.mpr hz

lemma coprime_of_prime_not_dvd {p m : ℕ} (hp : p.Prime) (h : ¬ p ∣ m) : m.Coprime p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm

/-- The pointwise inequality behind Lemma 4.1, for one `a`. -/
lemma pointwise (d N : ℕ) {w z : ℝ} (hwz : w ≤ z) (a : ℕ) :
    2 * (if d ∣ a ∧ Sifted (d * N) z a then 1 else 0)
      + #{p ∈ PS N w z | d * p ∣ a ∧ Sifted (d * N) w a}
    ≤ 2 * (if d ∣ a ∧ Sifted (d * N) w a then 1 else 0)
      + #{t ∈ triples N w z | d * t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (d * t.1.1 * N) t.1.2 a}
      + #{p ∈ {p ∈ PS N w z | p ∣ d} | d * p ∣ a ∧ Sifted (d * N) w a} := by
  set P := PS N w z
  -- split the `Ω₂` count by `p ∣ d`
  have hsplit := card_filter_add_card_filter_not (s := {p ∈ P | d * p ∣ a ∧
    Sifted (d * N) w a}) (fun p => p ∣ d)
  rw [filter_filter, filter_filter] at hsplit
  have hE : #{p ∈ {p ∈ P | p ∣ d} | d * p ∣ a ∧ Sifted (d * N) w a}
      = #{p ∈ P | (d * p ∣ a ∧ Sifted (d * N) w a) ∧ p ∣ d} := by
    rw [filter_filter]; congr 1; apply filter_congr; intro p _; tauto
  rw [hE, ← hsplit]
  by_cases hda : d ∣ a ∧ Sifted (d * N) w a
  swap
  · -- nothing survives
    have h1 : ¬ (d ∣ a ∧ Sifted (d * N) z a) := fun h => hda ⟨h.1, sifted_mono hwz h.2⟩
    have h2 : #{p ∈ P | (d * p ∣ a ∧ Sifted (d * N) w a) ∧ ¬ p ∣ d} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro p - ⟨⟨hp, hs⟩, -⟩
      exact hda ⟨dvd_trans (dvd_mul_right d p) hp, hs⟩
    rw [if_neg h1, if_neg hda, h2]; omega
  obtain ⟨hd, hw⟩ := hda
  rw [if_pos (show d ∣ a ∧ Sifted (d * N) w a from ⟨hd, hw⟩)]
  set R := {p ∈ P | p.Prime ∧ ¬ p ∣ d ∧ p ∣ a} with hRdef
  have hRmem : ∀ p, p ∈ R ↔ p ∈ P ∧ ¬ p ∣ d ∧ p ∣ a := by
    intro p; rw [hRdef, mem_filter]
    constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (mem_PS.1 h1).1, h2⟩
  have hR : #{p ∈ P | (d * p ∣ a ∧ Sifted (d * N) w a) ∧ ¬ p ∣ d} = #R := by
    congr 1; ext p; rw [mem_filter, hRmem]
    constructor
    · rintro ⟨hp, ⟨hdp, -⟩, hnd⟩
      exact ⟨hp, hnd, dvd_trans (dvd_mul_left p d) hdp⟩
    · rintro ⟨hp, hnd, hpa⟩
      exact ⟨hp, ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (coprime_of_prime_not_dvd (mem_PS.1 hp).1 hnd) hd hpa, hw⟩, hnd⟩
  rw [hR]
  -- a prime of `R` kills sifting up to `z`
  have hz : R.Nonempty → ¬ Sifted (d * N) z a := by
    rintro ⟨p, hp⟩ hs
    obtain ⟨hpP, hnd, hpa⟩ := (hRmem p).1 hp
    obtain ⟨hpr, -, hpz, hpN⟩ := mem_PS.1 hpP
    refine hs p hpr hpz ?_ hpa
    intro hdiv
    rcases (Nat.Prime.dvd_mul hpr).1 hdiv with h | h
    · exact hnd h
    · exact (Nat.Prime.coprime_iff_not_dvd hpr).1 hpN h
  rcases Nat.lt_or_ge (#R) 3 with h3 | h3
  · by_cases hRe : R.Nonempty
    · rw [if_neg (show ¬ (d ∣ a ∧ Sifted (d * N) z a) from fun h => hz hRe h.2)]; omega
    · rw [not_nonempty_iff_eq_empty] at hRe
      rw [hRe, card_empty]; split_ifs <;> omega
  -- `#R ≥ 3`: the two smallest elements of `R` and any third give a triple of `Ω₃`
  have hRne : R.Nonempty := card_pos.1 (by omega)
  rw [if_neg (show ¬ (d ∣ a ∧ Sifted (d * N) z a) from fun h => hz hRne h.2)]
  set p₁ := R.min' hRne with hp₁
  set R₁ := R.erase p₁ with hR₁
  have hR₁c : #R₁ = #R - 1 := card_erase_of_mem (min'_mem R hRne)
  have hR₁ne : R₁.Nonempty := card_pos.1 (by omega)
  set p₂ := R₁.min' hR₁ne with hp₂
  set R₂ := R₁.erase p₂ with hR₂
  have hR₂c : #R₂ = #R₁ - 1 := card_erase_of_mem (min'_mem R₁ hR₁ne)
  have hp₁R : p₁ ∈ R := min'_mem R hRne
  have hp₂R₁ : p₂ ∈ R₁ := min'_mem R₁ hR₁ne
  have hp₂R : p₂ ∈ R := mem_of_mem_erase hp₂R₁
  have hp₂ne : p₂ ≠ p₁ := ne_of_mem_erase hp₂R₁
  have h12 : p₁ < p₂ := lt_of_le_of_ne (min'_le R p₂ hp₂R) hp₂ne.symm
  -- the injection `p₃ ↦ ((p₁, p₂), p₃)` from `R₂`
  have hsub : R₂.image (fun p₃ => ((p₁, p₂), p₃)) ⊆
      {t ∈ triples N w z | d * t.1.1 * t.1.2 * t.2 ∣ a ∧ Sifted (d * t.1.1 * N) t.1.2 a} := by
    intro t ht
    obtain ⟨p₃, hp₃, rfl⟩ := mem_image.1 ht
    have hp₃R₁ : p₃ ∈ R₁ := mem_of_mem_erase hp₃
    have hp₃R : p₃ ∈ R := mem_of_mem_erase hp₃R₁
    have hp₃ne : p₃ ≠ p₂ := ne_of_mem_erase hp₃
    have hp₃ne1 : p₃ ≠ p₁ := ne_of_mem_erase hp₃R₁
    have h23 : p₂ < p₃ := lt_of_le_of_ne (min'_le R₁ p₃ hp₃R₁) hp₃ne.symm
    obtain ⟨hP1, hnd1, ha1⟩ := (hRmem p₁).1 hp₁R
    obtain ⟨hP2, hnd2, ha2⟩ := (hRmem p₂).1 hp₂R
    obtain ⟨hP3, hnd3, ha3⟩ := (hRmem p₃).1 hp₃R
    have pr1 := (mem_PS.1 hP1).1
    have pr2 := (mem_PS.1 hP2).1
    have pr3 := (mem_PS.1 hP3).1
    simp only [mem_filter, triples, mem_product]
    refine ⟨⟨⟨⟨hP1, hP2⟩, hP3⟩, h12, h23⟩, ?_, ?_⟩
    · -- `d p₁ p₂ p₃ ∣ a`
      have c1 : (d).Coprime p₁ := coprime_of_prime_not_dvd pr1 hnd1
      have c2 : (d * p₁).Coprime p₂ :=
        Nat.Coprime.mul_left (coprime_of_prime_not_dvd pr2 hnd2)
          ((Nat.coprime_primes pr1 pr2).2 hp₂ne.symm)
      have c3 : (d * p₁ * p₂).Coprime p₃ :=
        Nat.Coprime.mul_left (Nat.Coprime.mul_left (coprime_of_prime_not_dvd pr3 hnd3)
          ((Nat.coprime_primes pr1 pr3).2 hp₃ne1.symm))
          ((Nat.coprime_primes pr2 pr3).2 hp₃ne.symm)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd c3
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd c2 (Nat.Coprime.mul_dvd_of_dvd_of_dvd c1 hd ha1) ha2)
        ha3
    · -- sifted by `P(d p₁ N)` up to `p₂`
      intro q hq hqp₂ hqD hqa
      have hqdN : ¬ q ∣ d * N := fun h =>
        hqD (dvd_trans h (mul_dvd_mul_right (dvd_mul_right d p₁) N))
      by_cases hqw : (q : ℝ) < w
      · exact hw q hq hqw hqdN hqa
      · push_neg at hqw
        have hqz : (q : ℝ) < z :=
          lt_trans hqp₂ (mem_PS.1 hP2).2.2.1
        have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2
          (fun h => hqdN (dvd_mul_of_dvd_right h d))
        have hqd : ¬ q ∣ d := fun h => hqdN (dvd_mul_of_dvd_left h N)
        have hqR : q ∈ R := (hRmem q).2 ⟨mem_PS.2 ⟨hq, hqw, hqz, hqN⟩, hqd, hqa⟩
        have hq1 : q ≠ p₁ := by
          intro hqe
          rw [hqe] at hqD
          exact hqD (dvd_mul_of_dvd_left (dvd_mul_left p₁ d) N)
        have hqR₁ : q ∈ R₁ := mem_erase.2 ⟨hq1, hqR⟩
        have := min'_le R₁ q hqR₁
        rw [← hp₂] at this
        exact absurd hqp₂ (not_lt.2 (by exact_mod_cast this))
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun x y h => by simpa using h)] at hcard
  have hR₂c' : #R₂ = #R - 2 := by rw [hR₂c, hR₁c]; omega
  rw [hR₂c'] at hcard
  omega

/-- **Wu 2004 Lemma 4.1, exact form, in `ℕ`**: `2 S(A_d; P(dN), z) + Ω₂ ≤ Ω₁ + Ω₃ + E`. -/
theorem lemma41_nat (A : Finset ℕ) (d N : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    2 * S A d (d * N) z + Ω₂ A d N w z ≤ Ω₁ A d N w + Ω₃ A d N w z + Err A d N w z := by
  unfold Ω₁ Ω₂ Ω₃ Err
  simp only [S_eq_sum]
  rw [sum_comm (s := PS N w z), sum_comm (s := triples N w z),
    sum_comm (s := {p ∈ PS N w z | p ∣ d}), mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum fun a _ => ?_
  have := pointwise d N hwz a
  simp only [card_filter] at this
  exact this

/-- **Wu 2004 Lemma 4.1, exact form**: `2 S(A_d; P(dN), z) ≤ Ω₁ - Ω₂ + Ω₃ + E` in `ℤ`. -/
theorem lemma41_exact (A : Finset ℕ) (d N : ℕ) {w z : ℝ} (hwz : w ≤ z) :
    (2 * S A d (d * N) z : ℤ) ≤
      (Ω₁ A d N w : ℤ) - Ω₂ A d N w z + Ω₃ A d N w z + Err A d N w z := by
  have := lemma41_nat A d N hwz
  omega

/-- Summed against any weights `σ(d) ≥ 0` over a finite support, the form Wu uses with
`Φ(N, σ, s) = Σ_d σ(d) S(A_d; P(dN), d̲^{1/s})`, with `w d`, `z d` any reals `w d ≤ z d`. -/
theorem lemma41_weighted (A : Finset ℕ) (N : ℕ) (D : Finset ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ d ∈ D, 0 ≤ σ d) (w z : ℕ → ℝ) (hwz : ∀ d ∈ D, w d ≤ z d) :
    2 * ∑ d ∈ D, σ d * S A d (d * N) (z d) ≤
      ∑ d ∈ D, σ d * ((Ω₁ A d N (w d) : ℝ) - Ω₂ A d N (w d) (z d) + Ω₃ A d N (w d) (z d)
        + Err A d N (w d) (z d)) := by
  rw [mul_sum]
  refine sum_le_sum fun d hd => ?_
  have h := lemma41_exact A d N (hwz d hd)
  have h' : ((2 * S A d (d * N) (z d) : ℤ) : ℝ) ≤
      (((Ω₁ A d N (w d) : ℤ) - Ω₂ A d N (w d) (z d) + Ω₃ A d N (w d) (z d)
        + Err A d N (w d) (z d) : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  nlinarith [hσ d hd]

/-! ## Vacuity test and the need for `E`

`A = {9}`, `d = 3`, `N = 1`, `w = 2`, `z = 4`, so `PS = {2, 3}`: `2 S(A_d; P(dN), z) = 2`,
`Ω₁ = 2`, `Ω₂ = 1` from `p = 3`, `Ω₃ = 0`, `E = 1`. The hypotheses hold, the inequality is tight,
and without `E` it fails: `2 > 2 - 1 + 0`. -/

lemma PS_ex : PS 1 2 4 = {2, 3} := by
  ext p
  rw [mem_PS]
  simp only [mem_insert, mem_singleton, Nat.coprime_one_right_eq_true, and_true]
  constructor
  · rintro ⟨hp, h2, h4⟩
    have h2' : 2 ≤ p := by exact_mod_cast h2
    have h4' : p < 4 := by exact_mod_cast h4
    interval_cases p <;> simp_all
  · rintro (rfl | rfl) <;> refine ⟨by norm_num, by norm_num, by norm_num⟩

lemma sifted_ex_w (D a : ℕ) : Sifted D 2 a := by
  intro q hq hq2
  have : q < 2 := by exact_mod_cast hq2
  exact absurd hq.two_le (by omega)

lemma sifted_ex_z : Sifted 3 4 9 := by
  intro q hq hq4 h3 h9
  have : q < 4 := by exact_mod_cast hq4
  interval_cases q <;> simp_all

theorem example_tight :
    2 * S {9} 3 (3 * 1) 4 = 2 ∧ Ω₁ {9} 3 1 2 = 2 ∧ Ω₂ {9} 3 1 2 4 = 1 ∧
      Ω₃ {9} 3 1 2 4 = 0 ∧ Err {9} 3 1 2 4 = 1 := by
  have hS : ∀ (e D : ℕ) (y : ℝ), S {9} e D y = if e ∣ 9 ∧ Sifted D y 9 then 1 else 0 := by
    intro e D y; rw [S_eq_sum, sum_singleton]
  have hT : triples 1 2 4 = ∅ := by
    unfold triples; rw [PS_ex]
    ext t; simp only [mem_filter, mem_product, mem_insert, mem_singleton, notMem_empty,
      iff_false, not_and]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hS, if_pos ⟨by norm_num, sifted_ex_z⟩]
  · unfold Ω₁; rw [hS, if_pos ⟨by norm_num, sifted_ex_w _ _⟩]
  · unfold Ω₂; rw [PS_ex, sum_pair (by norm_num), hS, hS,
      if_neg (by norm_num), if_pos ⟨by norm_num, sifted_ex_w _ _⟩]
  · unfold Ω₃; rw [hT, sum_empty]
  · unfold Err; rw [PS_ex]
    have : ({p ∈ ({2, 3} : Finset ℕ) | p ∣ 3}) = {3} := by decide
    rw [this, sum_singleton, hS, if_pos ⟨by norm_num, sifted_ex_w _ _⟩]

/-- Without `E` the printed pointwise form fails at this instance; Wu's `O(N^{1-η})` absorbs it. -/
theorem err_needed :
    ¬ ((2 * S {9} 3 (3 * 1) 4 : ℤ) ≤ (Ω₁ {9} 3 1 2 : ℤ) - Ω₂ {9} 3 1 2 4 + Ω₃ {9} 3 1 2 4) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := example_tight
  rw [h2, h3, h4]; omega

end LeanLab.ChenDoubleSieve.Wu41
