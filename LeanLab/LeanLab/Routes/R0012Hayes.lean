/-
R-0012, T3 MOONSHOT: binary Goldbach in ℤ[X], Hayes 1965, as a model case.
Every integer polynomial of degree n ≥ 1 is the sum of two polynomials of degree n, each
irreducible over ℚ. The proof uses two different Eisenstein primes, one for each summand, glued
by the Chinese remainder theorem. Eisenstein's criterion is a congruence certificate of
irreducibility; `no_congruence_certificate` records that primality in ℕ has none, which is
where the analogy with binary Goldbach breaks.
KNOWN mathematics: D. R. Hayes, Amer. Math. Monthly 72 (1965); F. Saidak, Monthly 113 (2006);
P. Pollack, "On polynomial rings with a Goldbach property", Monthly 118 (2011).
Run 20261019T1902Z-2936, unit U-1098. AI-written Lean code, Claude. Checked only by the Lean
kernel. Nothing here is progress on Goldbach; Goldbach is open.
-/
import Mathlib

open Polynomial

namespace LeanLab.Routes.R0012

/-- Eisenstein at an integer prime `p`, without primitivity, gives irreducibility over ℚ.
The content is prime to `p` because it divides the leading coefficient. -/
theorem irreducible_map_of_eisenstein {g : ℤ[X]} {p : ℤ} (hp : Prime p)
    (hdeg : 0 < g.natDegree) (hlead : ¬ p ∣ g.leadingCoeff)
    (hmem : ∀ i, i < g.natDegree → p ∣ g.coeff i) (h0 : ¬ p ^ 2 ∣ g.coeff 0) :
    Irreducible (g.map (Int.castRingHom ℚ)) := by
  set c := g.content with hc
  set q := g.primPart with hq
  have hg : g = C c * q := eq_C_content_mul_primPart g
  have hg0 : g ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  have hc0 : c ≠ 0 := by
    rw [hc]; exact fun h => hg0 (content_eq_zero_iff.mp h)
  have hcoeff : ∀ i, g.coeff i = c * q.coeff i := by
    intro i; conv_lhs => rw [hg]
    rw [coeff_C_mul]
  have hqdeg : q.natDegree = g.natDegree := natDegree_primPart g
  have hpc : ¬ p ∣ c := by
    intro h; exact hlead (dvd_trans h (content_dvd_coeff _))
  have hleadq : g.leadingCoeff = c * q.leadingCoeff := by
    rw [leadingCoeff, leadingCoeff, hqdeg, hcoeff]
  have hspan : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hE : q.IsEisensteinAt (Ideal.span {p}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton]
      intro h; exact hlead (by rw [hleadq]; exact dvd_mul_of_dvd_right h c)
    · intro n hn
      rw [Ideal.mem_span_singleton]
      have := hmem n (by rw [← hqdeg]; exact hn)
      rw [hcoeff] at this
      rcases hp.dvd_or_dvd this with h | h
      · exact absurd h hpc
      · exact h
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h; exact h0 (by rw [hcoeff]; exact dvd_mul_of_dvd_right h c)
  have hqirr : Irreducible q :=
    hE.irreducible hspan (isPrimitive_primPart g) (by rw [hqdeg]; exact hdeg)
  have hqirrQ : Irreducible (q.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_primPart g)).mp hqirr
  have hmap : g.map (Int.castRingHom ℚ) = C ((c : ℚ)) * q.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [hg]
    rw [Polynomial.map_mul, map_C]; rfl
  rw [hmap, irreducible_isUnit_mul]
  · exact hqirrQ
  · exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc0))

/-- An integer of absolute value 1 or 2 is not divisible by a prime `p` with `|p| ≥ 3`. -/
theorem not_dvd_small {p d : ℤ} (hp : 3 ≤ p.natAbs) (hd0 : d ≠ 0) (hd : d.natAbs ≤ 2) :
    ¬ p ∣ d := by
  intro h
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd0) (Int.natAbs_dvd_natAbs.mpr h)
  omega

/-- The choice of the free constant: some `w ∈ {0, 1, 2}` avoids one bad class modulo `p` and
one bad class modulo `q`. -/
theorem exists_good_w {p q : ℤ} (hp : Prime p) (hq : Prime q) (hp3 : 3 ≤ p.natAbs)
    (hq3 : 3 ≤ q.natAbs) (hpq : ¬ p ∣ q) (hqp : ¬ q ∣ p) (x y : ℤ) :
    ∃ w : ℤ, ¬ p ∣ x + q * w ∧ ¬ q ∣ y - p * w := by
  by_contra hcon
  push Not at hcon
  have key1 : ∀ w1 w2 : ℤ, w1 ≠ w2 → (w1 - w2).natAbs ≤ 2 →
      p ∣ x + q * w1 → p ∣ x + q * w2 → False := by
    intro w1 w2 hne hle h1 h2
    have h3 : p ∣ q * (w1 - w2) := by
      have := dvd_sub h1 h2; rw [show x + q * w1 - (x + q * w2) = q * (w1 - w2) by ring] at this
      exact this
    rcases hp.dvd_or_dvd h3 with h | h
    · exact hpq h
    · exact not_dvd_small hp3 (sub_ne_zero.mpr hne) hle h
  have key2 : ∀ w1 w2 : ℤ, w1 ≠ w2 → (w1 - w2).natAbs ≤ 2 →
      q ∣ y - p * w1 → q ∣ y - p * w2 → False := by
    intro w1 w2 hne hle h1 h2
    have h3 : q ∣ p * (w2 - w1) := by
      have := dvd_sub h1 h2; rw [show y - p * w1 - (y - p * w2) = p * (w2 - w1) by ring] at this
      exact this
    rcases hq.dvd_or_dvd h3 with h | h
    · exact hqp h
    · exact not_dvd_small hq3 (sub_ne_zero.mpr (Ne.symm hne))
        (by rw [show w2 - w1 = -(w1 - w2) by ring, Int.natAbs_neg]; exact hle) h
  have c0 : ¬ p ∣ x + q * 0 → q ∣ y - p * 0 := hcon 0
  have c1 : ¬ p ∣ x + q * 1 → q ∣ y - p * 1 := hcon 1
  have c2 : ¬ p ∣ x + q * 2 → q ∣ y - p * 2 := hcon 2
  by_cases a0 : p ∣ x + q * 0 <;> by_cases a1 : p ∣ x + q * 1 <;> by_cases a2 : p ∣ x + q * 2
  · exact key1 0 1 (by norm_num) (by norm_num) a0 a1
  · exact key1 0 1 (by norm_num) (by norm_num) a0 a1
  · exact key1 0 2 (by norm_num) (by norm_num) a0 a2
  · exact key2 1 2 (by norm_num) (by norm_num) (c1 a1) (c2 a2)
  · exact key1 1 2 (by norm_num) (by norm_num) a1 a2
  · exact key2 0 2 (by norm_num) (by norm_num) (c0 a0) (c2 a2)
  · exact key2 0 1 (by norm_num) (by norm_num) (c0 a0) (c1 a1)
  · exact key2 0 1 (by norm_num) (by norm_num) (c0 a0) (c1 a1)

/-- **Hayes 1965, over ℚ.** Every `f ∈ ℤ[X]` of degree `n ≥ 1` is `g + h` with `g, h ∈ ℤ[X]`
of degree `n`, both irreducible in `ℚ[X]`. -/
theorem hayes_goldbach (f : ℤ[X]) (hf : 1 ≤ f.natDegree) :
    ∃ g h : ℤ[X], f = g + h ∧ g.natDegree = f.natDegree ∧ h.natDegree = f.natDegree ∧
      Irreducible (g.map (Int.castRingHom ℚ)) ∧ Irreducible (h.map (Int.castRingHom ℚ)) := by
  set n := f.natDegree with hn
  set a := f.leadingCoeff with ha
  have ha0 : a ≠ 0 := by
    intro h; rw [ha, leadingCoeff_eq_zero] at h; rw [h] at hn; simp at hn; omega
  -- two primes P < Q, both beyond 2|a| + 2
  obtain ⟨P, hPge, hP⟩ := Nat.exists_infinite_primes (2 * a.natAbs + 3)
  obtain ⟨Q, hQge, hQ⟩ := Nat.exists_infinite_primes (P + 1)
  set p : ℤ := (P : ℤ) with hpdef
  set q : ℤ := (Q : ℤ) with hqdef
  have hpP : Prime p := Nat.prime_iff_prime_int.mp hP
  have hqP : Prime q := Nat.prime_iff_prime_int.mp hQ
  have hp3 : 3 ≤ p.natAbs := by rw [hpdef, Int.natAbs_natCast]; omega
  have hq3 : 3 ≤ q.natAbs := by rw [hqdef, Int.natAbs_natCast]; omega
  have hpq : ¬ p ∣ q := by
    intro h
    have h' : P ∣ Q := Int.natCast_dvd_natCast.mp h
    rcases (Nat.dvd_prime hQ).mp h' with h1 | h1
    · exact hP.one_lt.ne' h1
    · omega
  have hqp : ¬ q ∣ p := by
    intro h
    have h' : Q ∣ P := Int.natCast_dvd_natCast.mp h
    have := Nat.le_of_dvd hP.pos h'
    omega
  have hcop : IsCoprime p q := by
    rw [Prime.coprime_iff_not_dvd hpP]; exact hpq
  obtain ⟨s, t, hst⟩ := hcop
  obtain ⟨w, hw1, hw2⟩ :=
    exists_good_w hpP hqP hp3 hq3 hpq hqp (s * f.coeff 0) (t * f.coeff 0)
  set E := f.eraseLead with hE
  set g : ℤ[X] := C (2 * a) * X ^ n + C (s * p) * E + C (p * q * w) with hg
  set h : ℤ[X] := C (-a) * X ^ n + C (t * q) * E - C (p * q * w) with hh
  have hfE : f = E + C a * X ^ n := (eraseLead_add_C_mul_X_pow f).symm
  have hsum : f = g + h := by
    have hC : C (s * p) + C (t * q) = (1 : ℤ[X]) := by rw [← C_add, hst, C_1]
    rw [hg, hh]
    conv_lhs => rw [hfE]
    have h2 : C (2 * a) = 2 * C a := by rw [C_mul]; rfl
    rw [h2, C_neg]
    linear_combination (-E) * hC
  -- coefficient formulas
  have hEn : E.coeff n = 0 := eraseLead_coeff_natDegree
  have hEi : ∀ i, i ≠ n → E.coeff i = f.coeff i := fun i hi => eraseLead_coeff_of_ne i hi
  have hEhi : ∀ i, n < i → E.coeff i = 0 := by
    intro i hi; rw [hEi i (by omega)]; exact coeff_eq_zero_of_natDegree_lt hi
  have gcoeff : ∀ i, g.coeff i =
      (if i = n then 2 * a else 0) + s * p * E.coeff i + (if i = 0 then p * q * w else 0) := by
    intro i; rw [hg, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_C]
  have hcoeff : ∀ i, h.coeff i =
      (if i = n then -a else 0) + t * q * E.coeff i - (if i = 0 then p * q * w else 0) := by
    intro i; rw [hh, coeff_sub, coeff_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_C]
  have hn0 : (0 : ℕ) ≠ n := by omega
  -- degrees
  have gdeg : g.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      have hi' : n < i := by exact_mod_cast hi
      rw [gcoeff, if_neg (by omega), if_neg (by omega), hEhi i hi']; ring
    · rw [gcoeff, if_pos rfl, if_neg (Ne.symm hn0), hEn]; simpa using ha0
  have hdeg : h.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      have hi' : n < i := by exact_mod_cast hi
      rw [hcoeff, if_neg (by omega), if_neg (by omega), hEhi i hi']; ring
    · rw [hcoeff, if_pos rfl, if_neg (Ne.symm hn0), hEn]; simpa using ha0
  have hpa : ¬ p ∣ 2 * a := by
    intro hd
    have h1 := Int.natAbs_dvd_natAbs.mpr hd
    have h2 : 0 < (2 * a).natAbs := Int.natAbs_pos.mpr (by positivity)
    have := Nat.le_of_dvd h2 h1
    rw [hpdef, Int.natAbs_natCast, Int.natAbs_mul] at this
    simp at this; omega
  have hqa : ¬ q ∣ -a := by
    intro hd
    have h1 := Int.natAbs_dvd_natAbs.mpr hd
    have h2 : 0 < (-a).natAbs := Int.natAbs_pos.mpr (neg_ne_zero.mpr ha0)
    have := Nat.le_of_dvd h2 h1
    rw [hqdef, Int.natAbs_natCast, Int.natAbs_neg] at this
    omega
  refine ⟨g, h, hsum, gdeg, hdeg, ?_, ?_⟩
  · apply irreducible_map_of_eisenstein hpP (by rw [gdeg]; omega)
    · rw [leadingCoeff, gdeg, gcoeff, if_pos rfl, if_neg (Ne.symm hn0), hEn]; simpa using hpa
    · intro i hi
      rw [gdeg] at hi
      rw [gcoeff, if_neg (by omega)]
      split_ifs
      · rw [zero_add]; exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left p s) _)
          (dvd_mul_of_dvd_left (dvd_mul_right p q) w)
      · simpa using dvd_mul_of_dvd_left (dvd_mul_left p s) (E.coeff i)
    · rw [gcoeff, if_neg hn0, if_pos rfl, hEi 0 hn0]
      rintro ⟨k, hk⟩
      apply hw1
      refine ⟨k, ?_⟩
      have : p * (s * f.coeff 0 + q * w) = p * (p * k) := by linear_combination hk
      exact mul_left_cancel₀ hpP.ne_zero this
  · apply irreducible_map_of_eisenstein hqP (by rw [hdeg]; omega)
    · rw [leadingCoeff, hdeg, hcoeff, if_pos rfl, if_neg (Ne.symm hn0), hEn]; simpa using hqa
    · intro i hi
      rw [hdeg] at hi
      rw [hcoeff, if_neg (by omega)]
      split_ifs
      · rw [zero_add]; exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_left q t) _)
          (dvd_mul_of_dvd_left (dvd_mul_left q p) w)
      · simpa using dvd_mul_of_dvd_left (dvd_mul_left q t) (E.coeff i)
    · rw [hcoeff, if_neg hn0, if_pos rfl, hEi 0 hn0]
      rintro ⟨k, hk⟩
      apply hw2
      refine ⟨k, ?_⟩
      have : q * (t * f.coeff 0 - p * w) = q * (q * k) := by linear_combination hk
      exact mul_left_cancel₀ hqP.ne_zero this

/-- **No congruence certificate for primality.** Every residue class modulo every `m ≥ 1`
contains composite numbers beyond any bound. So no finite set of congruence conditions forces
an integer to be prime, while Eisenstein's congruence conditions force irreducibility. -/
theorem no_congruence_certificate (m : ℕ) (hm : 1 ≤ m) (r N : ℕ) :
    ∃ n, N < n ∧ n % m = r % m ∧ ¬ n.Prime := by
  set A := r + m * (N + 2) with hA
  refine ⟨A * (1 + m), ?_, ?_, ?_⟩
  · have : N + 2 ≤ A := by rw [hA]; nlinarith
    nlinarith
  · rw [show A * (1 + m) = A + m * A by ring, Nat.add_mul_mod_self_left, hA,
      Nat.add_mul_mod_self_left]
  · apply Nat.not_prime_mul
    · rw [hA]; nlinarith
    · omega

/-- Vacuity: the hypotheses of `hayes_goldbach` hold, for example for `f = X`. -/
theorem hayes_vacuity : 1 ≤ (X : ℤ[X]).natDegree := by simp

/-- Instance: `X` itself splits as a sum of two linear polynomials irreducible over ℚ. -/
theorem hayes_X : ∃ g h : ℤ[X], (X : ℤ[X]) = g + h ∧ g.natDegree = 1 ∧ h.natDegree = 1 ∧
    Irreducible (g.map (Int.castRingHom ℚ)) ∧ Irreducible (h.map (Int.castRingHom ℚ)) := by
  simpa using hayes_goldbach X hayes_vacuity

end LeanLab.Routes.R0012
