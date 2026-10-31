/-
P0072 A. Togashi and S. Uchiyama 1964, On the representation of large even integers as sums
of two almost primes I, J. Fac. Sci. Hokkaido Univ. Ser. I 18, pp. 60 to 68. Lab copy
papers/P0072.pdf and papers/P0072.txt. Unit U-1544, run 20261026T0808Z-17522, type DECOMPOSE,
track T1, file a of three.

Target of the three files: the Section 3 summed upper sieve bound, the hypothesis
`TogashiUchiyamaScale.UpperSieveInput`, Σ_{z<q≤z₁} S(q) ≤ I(ε) M + 3εM, which is one of the two
remaining inputs of `TogashiUchiyamaScale.section5_of_two_sieve_inputs`.

This file a: Lemma 1, p. 61, and the Selberg step, pp. 63 to 64,
S(q) ≤ 2φ(N)/(q W_q) + R_q. The sieve problem for S(q) is a `SelbergSieve` whose support is
the set of values a_n = n(N - n), n in `Aq N q`, with multiplicity weights, density
ν(p) = 2/p and sifting range the odd primes p ∤ N with p⁶ ≤ N. The Λ² bound itself is the
lab's PROVED `LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple`, so the step reduces to
bookkeeping leaves.

Original decomposition leaves, all PROVED by CODEX task178: `card_rootsMod`, `dvd_iff_mod_mem_rootsMod`, `card_progression_moebius`,
`card_mul_mod_eq`, `sum_moebius_div_eq_totient`, `sum_abs_moebius_divisors`,
`siftedSum_sieveQ`, `multSum_sieveQ`, `nuT_of_squarefree`, `sqfree_coprime_mul_q`,
`selbergTerms_sieveQ`, `sum_six_pow_omega_le`.
Assemblies, now unconditional with clean axiom checks:
`card_progression_coprime`; `lemma1`, Lemma 1 with B_N = 2^{ν(N)}; `rem_sieveQ_le`;
`Sq_le_selberg`, the first display of Section 3 with an explicit R_q.

Original decomposition by Claude on 2026-10-26. Proofs and extensions by CODEX task178.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PNTSieve.SelbergBounds
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp1544a
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

/-! ### Lemma 1, p. 61 -/

/-- The residues r mod d with d ∣ r(N - r), computed in ℤ. -/
def rootsMod (N d : ℕ) : Finset ℕ :=
  (range d).filter (fun r => (d : ℤ) ∣ (r : ℤ) * ((N : ℤ) - r))

/-- Lemma 1, p. 61 also permits nonsquarefree moduli. For any positive d coprime to N,
there are two roots at each prime power. CRT gives 2 to omega d roots in total. -/
theorem card_rootsMod_coprime {N d : ℕ} (hd : 0 < d) (hdN : d.Coprime N) :
    (rootsMod N d).card = 2 ^ ω d := by
  have rc (d : ℕ) [NeZero d] :
      (rootsMod N d).card = Fintype.card {x : ZMod d // x * ((N : ZMod d) - x) = 0} := by
    rw [← Fintype.card_coe (rootsMod N d)]
    apply Fintype.card_congr
    refine { toFun := fun r => ⟨(r.val : ZMod d), ?_⟩
             invFun := fun x => ⟨x.val.val, ?_⟩
             left_inv := ?_
             right_inv := ?_ }
    · have hr := (mem_filter.mp r.property).2
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hr
      simpa using hr
    · rw [rootsMod, mem_filter, mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using x.property
    · intro r
      apply Subtype.ext
      exact ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp r.property).1)
    · intro x
      apply Subtype.ext
      exact ZMod.natCast_zmod_val _
  have cm {a b : ℕ} [NeZero a] [NeZero b] (hab : a.Coprime b) :
      Fintype.card {x : ZMod (a*b) // x * ((N : ZMod (a*b)) - x) = 0} =
        Fintype.card {x : ZMod a // x * ((N : ZMod a) - x) = 0} *
        Fintype.card {x : ZMod b // x * ((N : ZMod b) - x) = 0} := by
    rw [← Fintype.card_prod]
    apply Fintype.card_congr
    let E := ZMod.chineseRemainder hab
    refine (Equiv.subtypeEquiv E.toEquiv (p := fun x => x * ((N : ZMod (a*b)) - x) = 0)
      (q := fun x : ZMod a × ZMod b =>
        x.1 * ((N : ZMod a) - x.1) = 0 ∧ x.2 * ((N : ZMod b) - x.2) = 0) ?_).trans
        (Equiv.subtypeProdEquivProd (p := fun x : ZMod a => x * ((N : ZMod a) - x) = 0)
          (q := fun x : ZMod b => x * ((N : ZMod b) - x) = 0))
    intro x
    change x * ((N : ZMod (a*b)) - x) = 0 ↔
      (E x).1 * ((N : ZMod a) - (E x).1) = 0 ∧
      (E x).2 * ((N : ZMod b) - (E x).2) = 0
    have h := E.injective.eq_iff (a := x * ((N : ZMod (a*b)) - x)) (b := 0)
    simpa only [map_mul, map_sub, map_natCast, map_zero, Prod.ext_iff,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_natCast, Prod.snd_natCast, Prod.fst_zero, Prod.snd_zero] using h.symm
  have pc {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hc : (p^k).Coprime N) :
      (rootsMod N (p^k)).card = 2 := by
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero k := ⟨hk⟩
    let : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hunit : IsUnit (N : ZMod (p^k)) := (ZMod.isUnit_iff_coprime N (p^k)).mpr hc.symm
    have hchar : ∀ x : ZMod (p^k), x * ((N : ZMod (p^k)) - x) = 0 ↔ x = 0 ∨ x = N := by
      intro x
      constructor
      · intro hx
        have hu : IsUnit x ∨ IsUnit ((N : ZMod (p^k)) - x) :=
          IsLocalRing.isUnit_or_isUnit_of_isUnit_add (by simpa using hunit)
        rcases hu with hu | hu
        · right
          exact (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hx)).symm
        · left
          exact hu.mul_left_eq_zero.mp hx
      · rintro (rfl | rfl) <;> simp
    rw [rc]
    have hs : (univ.filter (fun x : ZMod (p^k) => x * ((N : ZMod (p^k)) - x) = 0)) =
        {0, (N : ZMod (p^k))} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, hchar, mem_insert, mem_singleton]
    rw [Fintype.card_subtype, hs, card_pair (Ne.symm hunit.ne_zero)]
  induction d using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp =>
    cases k with
    | zero => simp [rootsMod]
    | succ k =>
      rw [pc hp (by omega) hdN, ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp (by omega)]
      norm_num
  | coprime a b ha hb hab ia ib =>
    have hNs := Nat.coprime_mul_iff_left.mp hdN
    let : NeZero a := ⟨by omega⟩
    let : NeZero b := ⟨by omega⟩
    rw [rc (a*b), cm hab, ← rc a, ← rc b,
      ia (by omega) hNs.1, ib (by omega) hNs.2,
      ArithmeticFunction.cardDistinctFactors_mul hab, pow_add]

/-- LEAF. Unit U-1544. For squarefree d coprime to N the congruence r(N - r) ≡ 0 mod d has
exactly 2^{ν(d)} solutions mod d: by the Chinese remainder theorem, r ≡ 0 or r ≡ N mod each
p ∣ d, and these differ since p ∤ N. This is the count ω(d) = 2^{ν(d)} of Lemma 1, p. 61. -/
theorem card_rootsMod {N d : ℕ} (hd : Squarefree d) (hdN : d.Coprime N) :
    (rootsMod N d).card = 2 ^ ω d := by
  exact card_rootsMod_coprime (Nat.pos_of_ne_zero hd.ne_zero) hdN

/-- LEAF. Unit U-1544. For 0 < d and n ≤ N, d ∣ n(N - n) iff n mod d is a root, since
n ≡ n mod d and the natural subtraction N - n is the integer one. Lemma 1, p. 61. -/
theorem dvd_iff_mod_mem_rootsMod {N d n : ℕ} (hd : 0 < d) (hn : n ≤ N) :
    d ∣ n * (N - n) ↔ n % d ∈ rootsMod N d := by
  simp only [rootsMod, mem_filter, mem_range]
  rw [and_iff_right (Nat.mod_lt n hd)]
  have he : (n : ℤ) ≡ (n % d : ℕ) [ZMOD (d : ℤ)] := by
    exact_mod_cast (Nat.mod_modEq n d).symm
  have hh := he.mul (Int.ModEq.refl (N : ℤ) |>.sub he)
  simpa only [← Int.natCast_sub hn, ← Int.natCast_mul, Int.natCast_dvd_natCast] using hh.dvd_iff

/-- LEAF. Unit U-1544. Möbius inclusion and exclusion over e ∣ N for the condition (n, N) = 1:
#{1 ≤ n ≤ N : (n, N) = 1, n mod d = r} = Σ_{e ∣ N} μ(e) #{1 ≤ m ≤ N/e : em mod d = r}.
Lemma 1, p. 61, the step behind R(d). -/
theorem card_progression_moebius (N d r : ℕ) :
    (((Aset N).filter (fun n => n % d = r)).card : ℝ) =
      ∑ e ∈ N.divisors, (μ e : ℝ) *
        (((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) := by
  by_cases hN : N = 0
  · subst N; simp [Aset]
  have hc (e : ℕ) (he : e ∈ N.divisors) :
      ((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card =
        ((Icc 1 N).filter (fun n => e ∣ n ∧ n % d = r)).card := by
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    apply card_bij (fun m _ => e * m)
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm ⊢
      exact ⟨⟨by nlinarith [hm.1.1], by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le he0).mp hm.1.2⟩,
        dvd_mul_right e m, hm.2⟩
    · intro a ha b hb h
      exact Nat.eq_of_mul_eq_mul_left he0 h
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn
      refine ⟨n / e, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn.1.2⟩, ?_⟩, ?_⟩
      · have hmul := Nat.mul_div_cancel' hn.2.1
        nlinarith [hn.1.1]
      · simpa [Nat.mul_div_cancel' hn.2.1] using hn.2.2
      · exact Nat.mul_div_cancel' hn.2.1
  have hmu (n : ℕ) (hn : n ∈ Icc 1 N) :
      ∑ e ∈ N.divisors with e ∣ n, (μ e : ℝ) = if n.Coprime N then 1 else 0 := by
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hset : N.divisors.filter (fun e => e ∣ n) = (n.gcd N).divisors := by
      ext e
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      have hg0 : n.gcd N ≠ 0 := Nat.gcd_ne_zero_left hn0
      tauto
    rw [hset]
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f (n.gcd N))
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hh
    simpa only [ArithmeticFunction.intCoe_apply, Nat.Coprime] using hh
  have hc2 : (∑ e ∈ N.divisors, (μ e : ℝ) *
      (((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ)) =
      ∑ e ∈ N.divisors, (μ e : ℝ) *
      (((Icc 1 N).filter (fun n => e ∣ n ∧ n % d = r)).card : ℝ) := by
    exact sum_congr rfl (fun e he => by rw [hc e he])
  rw [hc2]
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, mul_sum]
  rw [sum_comm]
  change (∑ x ∈ Aset N, if x % d = r then (1 : ℝ) else 0) = _
  rw [Aset, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hr : n % d = r
  · simp only [hr, and_true, mul_ite, mul_one, mul_zero, ← sum_filter]
    exact (hmu n hn).symm
  · simp [hr]

/-- LEAF. Unit U-1544. If e is coprime to d > 0 and r < d, then m ↦ em mod d permutes the
residues, so #{1 ≤ m ≤ M : em mod d = r} is ⌊M/d⌋ or ⌈M/d⌉ and differs from M/d by at most 1.
Lemma 1, p. 61. -/
theorem card_mul_mod_eq {d e r : ℕ} (M : ℕ) (hd : 0 < d) (hed : e.Coprime d) (hr : r < d) :
    |(((Icc 1 M).filter (fun m => (e * m) % d = r)).card : ℝ) - (M : ℝ) / d| ≤ 1 := by
  let : NeZero d := ⟨hd.ne'⟩
  let u : ℕ := (((e : ZMod d)⁻¹ * r) - 1).val
  have hinv : (e : ZMod d) * (e : ZMod d)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one e hed
  have heq (n : ℕ) : (e * (n + 1)) % d = r ↔ n ≡ u [MOD d] := by
    rw [← Nat.mod_eq_of_lt hr, ← ZMod.natCast_eq_natCast_iff']
    rw [← ZMod.natCast_eq_natCast_iff, show (u : ZMod d) = (e : ZMod d)⁻¹ * r - 1 by
      exact ZMod.natCast_zmod_val _]
    push_cast
    constructor
    · intro h
      have hi := congrArg (fun x : ZMod d => (e : ZMod d)⁻¹ * x) h
      have hinv' : (e : ZMod d)⁻¹ * e = 1 := by simpa [mul_comm] using hinv
      rw [← mul_assoc, hinv', one_mul] at hi
      linear_combination hi
    · intro h
      rw [h]
      ring_nf
      rw [hinv]
      ring
  have hcard : ((Icc 1 M).filter (fun m => (e * m) % d = r)).card =
      Nat.count (fun n => n ≡ u [MOD d]) M := by
    rw [Nat.count_eq_card_filter_range]
    apply card_bij (fun n _ => n - 1)
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn
      simp only [mem_filter, mem_range]
      exact ⟨by omega, (heq (n - 1)).mp (by simpa [Nat.sub_add_cancel hn.1.1] using hn.2)⟩
    · intro a ha b hb hab
      have ha := (mem_Icc.mp (mem_filter.mp ha).1).1
      have hb := (mem_Icc.mp (mem_filter.mp hb).1).1
      omega
    · intro n hn
      simp only [mem_filter, mem_range] at hn
      refine ⟨n + 1, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (heq n).mpr hn.2⟩, by omega⟩
  rw [hcard, Nat.count_modEq_card M hd u]
  have hrem := Nat.mod_lt M hd
  have hdiv := Nat.mod_add_div M d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hremR : ((M % d : ℕ) : ℝ) < d := by exact_mod_cast hrem
  have heR : ((M % d : ℕ) : ℝ) + d * (M / d : ℕ) = M := by exact_mod_cast hdiv
  have hb0 : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    have := Nat.cast_nonneg (α := ℝ) (M % d)
    nlinarith
  have hb1 : (M : ℝ) / d < ((M / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).mpr
    nlinarith
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- LEAF. Unit U-1544. φ(N) = Σ_{e ∣ N} μ(e) N/e, Möbius inversion of Σ_{e ∣ N} φ(e) = N,
Mathlib `Nat.sum_totient`. Used in Lemma 1, p. 61. -/
theorem sum_moebius_div_eq_totient (N : ℕ) :
    ∑ e ∈ N.divisors, (μ e : ℝ) * ((N / e : ℕ) : ℝ) = N.totient := by
  by_cases hN : N = 0
  · subst N; simp
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun n => (n.totient : ℝ)) (g := fun n => (n : ℝ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n) N (Nat.pos_of_ne_zero hN)
  convert hi using 1
  exact (Nat.sum_divisorsAntidiagonal (fun i j => (μ i : ℝ) * (j : ℝ))).symm

/-- LEAF. Unit U-1544. Σ_{e ∣ N} |μ(e)| = 2^{ν(N)} for N ≥ 1: the squarefree divisors of N are
the subsets of its prime factors. This is the constant B_N = c 2^{ν(N)} of Lemma 1, p. 61. -/
theorem sum_abs_moebius_divisors {N : ℕ} (hN : N ≠ 0) :
    ∑ e ∈ N.divisors, |(μ e : ℝ)| = 2 ^ ω N := by
  simp_rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ← sum_filter]
  rw [Nat.sum_divisors_filter_squarefree hN]
  simp only [sum_const, nsmul_eq_mul, mul_one, card_powerset]
  push_cast
  congr 1
  simp [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.factors_eq]

/-- Assembly from `card_progression_moebius`, `card_mul_mod_eq`,
`sum_moebius_div_eq_totient`, `sum_abs_moebius_divisors`: for 0 < d coprime to N ≥ 1 and r < d,
|#{1 ≤ n ≤ N : (n, N) = 1, n mod d = r} - φ(N)/d| ≤ 2^{ν(N)}. Lemma 1, p. 61. -/
theorem card_progression_coprime {N d r : ℕ} (hN : 1 ≤ N) (hd : 0 < d) (hdN : d.Coprime N)
    (hr : r < d) :
    |(((Aset N).filter (fun n => n % d = r)).card : ℝ) - (N.totient : ℝ) / d| ≤ 2 ^ ω N := by
  rw [card_progression_moebius, ← sum_moebius_div_eq_totient, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← sum_abs_moebius_divisors (by omega)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  have heN : e ∣ N := Nat.dvd_of_mem_divisors he
  have hed : e.Coprime d := (Nat.Coprime.coprime_dvd_left heN hdN.symm)
  have h1 := card_mul_mod_eq (N / e) hd hed hr
  rw [show (μ e : ℝ) * (((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) -
      (μ e : ℝ) * ((N / e : ℕ) : ℝ) / d = (μ e : ℝ) *
      ((((Icc 1 (N / e)).filter (fun m => (e * m) % d = r)).card : ℝ) - ((N / e : ℕ) : ℝ) / d)
      by ring, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- Lemma 1, p. 61 for every positive modulus coprime to N. This extends the original
squarefree assembly to the full coprime modulus range of the paper. -/
theorem lemma1_coprime {N d : ℕ} (hN : 1 ≤ N) (hd : 0 < d) (hdN : d.Coprime N) :
    |(((Aset N).filter (fun n => d ∣ n * (N - n))).card : ℝ) -
        2 ^ ω d * (N.totient : ℝ) / d| ≤ 2 ^ ω d * 2 ^ ω N := by
  have hd0 : 0 < d := hd
  have hle : ∀ n ∈ Aset N, n ≤ N := fun n hn => (mem_Aset.mp hn).2.1
  set A' := (Aset N).filter (fun n => d ∣ n * (N - n)) with hA'
  have hmaps : ∀ n ∈ A', n % d ∈ rootsMod N d := by
    intro n hn
    rw [hA', mem_filter] at hn
    exact (dvd_iff_mod_mem_rootsMod hd0 (hle n hn.1)).1 hn.2
  have hcard : A'.card = ∑ r ∈ rootsMod N d, (A'.filter (fun n => n % d = r)).card :=
    card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ rootsMod N d,
      A'.filter (fun n => n % d = r) = (Aset N).filter (fun n => n % d = r) := by
    intro r hr
    ext n
    simp only [hA', mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, (dvd_iff_mod_mem_rootsMod hd0 (hle n h1)).2 (h3 ▸ hr)⟩, h3⟩
  have hroots : ((rootsMod N d).card : ℝ) = 2 ^ ω d := by
    rw [card_rootsMod_coprime hd hdN]; push_cast; ring
  rw [hcard, Nat.cast_sum, ← hroots,
    show ((rootsMod N d).card : ℝ) * (N.totient : ℝ) / d =
      ∑ r ∈ rootsMod N d, (N.totient : ℝ) / d by rw [sum_const, nsmul_eq_mul]; ring,
    ← Finset.sum_sub_distrib,
    show ((rootsMod N d).card : ℝ) * 2 ^ ω N = ∑ r ∈ rootsMod N d, (2 : ℝ) ^ ω N by
      rw [sum_const, nsmul_eq_mul]]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  rw [hfib r hr]
  have hrd : r < d := by
    have := (mem_filter.mp hr).1
    exact mem_range.mp this
  exact card_progression_coprime hN hd0 hdN hrd

/-- **Lemma 1**, p. 61, with B_N = 2^{ν(N)}: for squarefree d coprime to N ≥ 1,
S_d = #{1 ≤ n ≤ N : (n, N) = 1, d ∣ n(N - n)} satisfies
|S_d - 2^{ν(d)} φ(N)/d| ≤ 2^{ν(d)} 2^{ν(N)}.
Assembly from `card_rootsMod`, `dvd_iff_mod_mem_rootsMod` and the leaves of
`card_progression_coprime`. -/
theorem lemma1 {N d : ℕ} (hN : 1 ≤ N) (hd : Squarefree d) (hdN : d.Coprime N) :
    |(((Aset N).filter (fun n => d ∣ n * (N - n))).card : ℝ) -
        2 ^ ω d * (N.totient : ℝ) / d| ≤ 2 ^ ω d * 2 ^ ω N := by
  exact lemma1_coprime hN (Nat.pos_of_ne_zero hd.ne_zero) hdN

/-! ### The sieve problem for S(q), p. 63 -/

/-- The sifting primes: odd primes p ∤ N with p⁶ ≤ N, that is p ≤ z = N^{1/6}. For even N the
primes p ∣ N, 2 among them, never divide a_n with (n, N) = 1, so this is the paper's range. -/
def siftPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ 2 < p ∧ p ^ 6 ≤ N ∧ ¬ p ∣ N)

lemma mem_siftPrimes {N p : ℕ} :
    p ∈ siftPrimes N ↔ p ≤ N ∧ p.Prime ∧ 2 < p ∧ p ^ 6 ≤ N ∧ ¬ p ∣ N := by
  simp [siftPrimes, Nat.lt_succ_iff]

/-- P(z), the product of the sifting primes. -/
def Pz (N : ℕ) : ℕ := ∏ p ∈ siftPrimes N, p

lemma Pz_ne_zero (N : ℕ) : Pz N ≠ 0 :=
  prod_ne_zero_iff.mpr (fun p hp => (mem_siftPrimes.1 hp).2.1.ne_zero)

lemma Pz_squarefree (N : ℕ) : Squarefree (Pz N) :=
  LeanLab.PNTSieve.Sieve.prodDistinctPrimes_squarefree _ (fun p hp => (mem_siftPrimes.1 hp).2.1)

lemma prime_dvd_Pz {N p : ℕ} (hp : p.Prime) (h : p ∣ Pz N) : p ∈ siftPrimes N := by
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hrp := (mem_siftPrimes.1 hr).2.1
  rwa [(Nat.prime_dvd_prime_iff_eq hp hrp).1 hpr]

/-- The n of S(q) before sifting: 1 ≤ n ≤ N, (n, N) = 1, q ∣ n(N - n). -/
def Aq (N q : ℕ) : Finset ℕ := (Aset N).filter (fun n => q ∣ n * (N - n))

/-- The density ν(d) = ∏_{p ∣ d} 2/p, which is ω(d)/d of Lemma 1 on squarefree d coprime to N. -/
def nuT : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => 2 / (p : ℝ))

lemma nuT_prime {p : ℕ} (hp : p.Prime) : nuT p = 2 / (p : ℝ) := by
  simp [nuT, hp.ne_zero, hp.primeFactors]

/-- The Selberg sieve problem for S(q): support the values a_n = n(N - n), n ∈ Aq N q, with
multiplicity weights; total mass X = 2φ(N)/q; density ν; sifting primes `siftPrimes N`;
level y. -/
def sieveQ (N q : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Aq N q).image (fun n => n * (N - n))
  prodPrimes := Pz N
  prodPrimes_squarefree := Pz_squarefree N
  weights := fun m => (((Aq N q).filter (fun n => n * (N - n) = m)).card : ℝ)
  weights_nonneg := fun _ => Nat.cast_nonneg _
  totalMass := 2 * (N.totient : ℝ) / q
  nu := nuT
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp _ => by rw [nuT_prime hp]; have := hp.pos; positivity
  nu_lt_one_of_prime := fun p hp hd => by
    have h2 := (mem_siftPrimes.1 (prime_dvd_Pz hp hd)).2.2.1
    rw [nuT_prime hp]
    have h2' : (2 : ℝ) < p := by exact_mod_cast h2
    rw [div_lt_one (by linarith)]; exact h2'
  level := y
  one_le_level := hy

/-- LEAF. Unit U-1544. For even N the sifted sum of `sieveQ` is S(q) of p. 63: the weights
count each n ∈ Aq N q once, and for (n, N) = 1 the condition (P(z), n(N - n)) = 1 is the
condition `sieved N n`, since a prime p ∣ N, 2 included, divides neither n nor N - n. -/
theorem siftedSum_sieveQ {N q : ℕ} (y : ℝ) (hy : 1 ≤ y) (hN : Even N) :
    BoundingSieve.siftedSum (s := (sieveQ N q y hy).toBoundingSieve) = ((Sq N q).card : ℝ) := by
  have hc : ∀ n ∈ Aset N, (Pz N).Coprime (n * (N - n)) ↔ sieved N n := by
    intro n hn
    have hn' := mem_Aset.mp hn
    constructor
    · intro h p hp hprime hpow hdiv
      have hpN : ¬ p ∣ N := by
        intro hpN
        rcases hprime.dvd_mul.mp hdiv with hpn | hpn
        · exact (Nat.not_coprime_of_dvd_of_dvd hprime.one_lt hpn hpN) hn'.2.2
        · have hpn' : p ∣ n := by simpa [Nat.sub_sub_self hn'.2.1] using Nat.dvd_sub hpN hpn
          exact (Nat.not_coprime_of_dvd_of_dvd hprime.one_lt hpn' hpN) hn'.2.2
      have hp2 : 2 < p := by
        have := hprime.two_le
        have h2N : 2 ∣ N := even_iff_two_dvd.mp hN
        by_contra hh
        have : p = 2 := by omega
        exact hpN (this ▸ h2N)
      have hpP : p ∣ Pz N := dvd_prod_of_mem _ (mem_siftPrimes.mpr
        ⟨by have := mem_range.mp hp; omega, hprime, hp2, hpow, hpN⟩)
      exact hprime.not_dvd_one ((Nat.coprime_iff_gcd_eq_one.mp h) ▸ Nat.dvd_gcd hpP hdiv)
    · intro hs
      apply Nat.coprime_of_dvd
      intro p hp hpP hpa
      have hm := mem_siftPrimes.mp (prime_dvd_Pz hp hpP)
      exact hs p (mem_range.mpr (by omega)) hp hm.2.2.2.1 hpa
  unfold BoundingSieve.siftedSum
  change (∑ m ∈ (Aq N q).image (fun n => n * (N - n)),
    if (Pz N).Coprime m then
      (((Aq N q).filter (fun n => n * (N - n) = m)).card : ℝ) else 0) = _
  rw [← sum_filter]
  rw [← Nat.cast_sum, sum_card_fiberwise_eq_card_filter]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext n : 1
  simp +instances only [mem_filter, mem_image, Aq, Sq, S1set]
  constructor
  · rintro ⟨⟨hA, hq⟩, _, hcop⟩
    exact ⟨⟨hA, (hc n hA).mp hcop⟩, hq⟩
  · rintro ⟨⟨hA, hs⟩, hq⟩
    exact ⟨⟨hA, hq⟩, ⟨n, ⟨hA, hq⟩, rfl⟩, (hc n hA).mpr hs⟩

/-- LEAF. Unit U-1544. For q ∈ Qset N and d ∣ P(z), the mass of `sieveQ` on multiples of d is
#{n ∈ Aset N : dq ∣ n(N - n)}: the primes of d are below q, so (d, q) = 1 and
q ∣ a ∧ d ∣ a ↔ dq ∣ a. The count A_{dq} of Lemma 1 used on p. 63. -/
theorem multSum_sieveQ {N q d : ℕ} (y : ℝ) (hy : 1 ≤ y) (hq : q ∈ Qset N) (hd : d ∣ Pz N) :
    BoundingSieve.multSum (s := (sieveQ N q y hy).toBoundingSieve) d =
      (((Aset N).filter (fun n => d * q ∣ n * (N - n))).card : ℝ) := by
  have hqp := (mem_filter.mp hq).2
  have hqd : ¬ q ∣ d := by
    intro h
    have hp := mem_siftPrimes.mp (prime_dvd_Pz hqp.1 (h.trans hd))
    omega
  have hcop : d.Coprime q := ((Nat.Prime.coprime_iff_not_dvd hqp.1).mpr hqd).symm
  unfold BoundingSieve.multSum
  change (∑ m ∈ (Aq N q).image (fun n => n * (N - n)),
    if d ∣ m then
      (((Aq N q).filter (fun n => n * (N - n) = m)).card : ℝ) else 0) = _
  rw [← sum_filter, ← Nat.cast_sum, sum_card_fiberwise_eq_card_filter]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  ext n : 1
  simp +instances only [mem_filter, mem_image, Aq]
  constructor
  · rintro ⟨⟨hA, hq⟩, _, hd⟩
    exact ⟨hA, hcop.mul_dvd_of_dvd_of_dvd hd hq⟩
  · rintro ⟨hA, hdiv⟩
    have hq := (dvd_mul_left q d).trans hdiv
    exact ⟨⟨hA, hq⟩, ⟨n, ⟨hA, hq⟩, rfl⟩, (dvd_mul_right d q).trans hdiv⟩

/-- LEAF. Unit U-1544. On squarefree d, ν(d) = 2^{ν(d)}/d, the ratio ω(d)/d of Lemma 1, p. 61. -/
theorem nuT_of_squarefree {d : ℕ} (hd : Squarefree d) : nuT d = 2 ^ ω d / (d : ℝ) := by
  unfold nuT
  rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero, prod_div_distrib,
    prod_const, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

  congr 2

/-- LEAF. Unit U-1544. For q ∈ Qset N and d ∣ P(z): dq is squarefree, (dq, N) = 1 and q ∤ d,
because every prime p of d has p⁶ ≤ N < q⁶ and p ∤ N. Used for A_{dq} on p. 63. -/
theorem sqfree_coprime_mul_q {N q d : ℕ} (hq : q ∈ Qset N) (hd : d ∣ Pz N) :
    Squarefree (d * q) ∧ (d * q).Coprime N ∧ ¬ q ∣ d := by
  have hqp := (mem_filter.mp hq).2
  have hqd : ¬ q ∣ d := by
    intro h
    have hp := mem_siftPrimes.mp (prime_dvd_Pz hqp.1 (h.trans hd))
    omega
  have hdN : d.Coprime N := by
    apply Nat.coprime_of_dvd
    intro p hp hpd hpN
    exact (mem_siftPrimes.mp (prime_dvd_Pz hp (hpd.trans hd))).2.2.2.2 hpN
  exact ⟨Nat.squarefree_mul_iff.mpr
    ⟨((Nat.Prime.coprime_iff_not_dvd hqp.1).mpr hqd).symm,
      (Pz_squarefree N).squarefree_of_dvd hd, hqp.1.squarefree⟩,
    hdN.mul_left hqp.2.2.2, hqd⟩

/-- LEAF. Unit U-1544. The Selberg terms of `sieveQ` are 1/f₁(l) = ∏_{p ∣ l} 2/(p - 2) for
l ∣ P(z): with ν(p) = 2/p, ν(p)/(1 - ν(p)) = 2/(p - 2). These are the terms μ²(m)/f₁(m) of W_q,
pp. 61 and 64. -/
theorem selbergTerms_sieveQ {N q l : ℕ} (y : ℝ) (hy : 1 ≤ y) (hl : l ∣ Pz N) :
    LeanLab.PNTSieve.SelbergSieve.selbergTerms (sieveQ N q y hy).toBoundingSieve l =
      ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2) := by
  rw [LeanLab.PNTSieve.SelbergSieve.selbergTerms_apply]
  change nuT l * (∏ p ∈ l.primeFactors, 1 / (1 - nuT p)) = _
  rw [nuT, ArithmeticFunction.prodPrimeFactors_apply
    (fun h => Pz_ne_zero N (Nat.eq_zero_of_zero_dvd (h ▸ hl))), ← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpm := mem_siftPrimes.mp (prime_dvd_Pz hprime ((Nat.dvd_of_mem_primeFactors hp).trans hl))
  change 2 / (p : ℝ) * (1 / (1 - nuT p)) = _
  rw [nuT_prime hprime]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hp2 : (p : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < p := by exact_mod_cast hpm.2.2.1
    linarith
  field_simp


/-- A sharper elementary estimate for the remainder bookkeeping on p. 64. Counting the
first coordinate of each six-factor tuple exactly saves one harmonic factor. This bound is
derived here and does not assert the paper's sharper squared logarithmic remainder. -/
theorem sum_six_pow_omega_le_five {y : ℝ} (hy : 1 ≤ y) :
    ∑ d ∈ (Icc 1 ⌊y⌋₊).filter Squarefree, (6 : ℝ) ^ ω d ≤ y * (1 + log y) ^ 5 := by
  let n := ⌊y⌋₊
  let A := Fintype.piFinset (fun _ : Fin 6 => Icc 1 n)
  let S := (Icc 1 n).filter Squarefree
  have hf (d : ℕ) (hd : d ∈ S) :
      A.filter (fun f => ∏ i, f i = d) = Nat.finMulAntidiag 6 d := by
    have hd' := mem_filter.mp hd
    have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd'.1).1; omega
    ext f
    simp only [mem_filter, Nat.mem_finMulAntidiag]
    constructor
    · rintro ⟨_, he⟩; exact ⟨he, hd0⟩
    · intro he
      refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), he.1⟩
      have hi : f i ∣ d := Nat.dvd_of_mem_finMulAntidiag (Nat.mem_finMulAntidiag.mpr he) i
      have hi0 : f i ≠ 0 := ne_zero_of_dvd_ne_zero hd0 hi
      exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi0,
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hi).trans (mem_Icc.mp hd'.1).2⟩
  have hcard : (∑ d ∈ S, (6 : ℝ) ^ ω d) =
      ((A.filter (fun f => ∏ i, f i ∈ S)).card : ℝ) := by
    rw [← sum_card_fiberwise_eq_card_filter A S (fun f => ∏ i, f i), Nat.cast_sum]
    apply sum_congr rfl
    intro d hd
    rw [hf d hd, Nat.card_finMulAntidiag_of_squarefree (mem_filter.mp hd).2]
    norm_cast
  change (∑ d ∈ S, (6 : ℝ) ^ ω d) ≤ _
  rw [hcard]
  let B := Fintype.piFinset (fun _ : Fin 5 => Icc 1 n)
  let T := A.filter (fun f => ∏ i, f i ∈ S)
  let tail : (Fin 6 → ℕ) → (Fin 5 → ℕ) := fun f i => f i.succ
  have hmaps : ∀ f ∈ T, tail f ∈ B := by
    intro f hf
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Fintype.mem_piFinset.mp (mem_filter.mp hf).1 i.succ
  have hbound (g : Fin 5 → ℕ) (hg : g ∈ B) :
      ((T.filter (fun f => tail f = g)).card : ℝ) ≤
        y * ∏ i : Fin 5, (1 : ℝ) / g i := by
    have hP : 0 < ∏ i : Fin 5, g i := by
      apply prod_pos
      intro i _
      exact (mem_Icc.mp (Fintype.mem_piFinset.mp hg i)).1
    have hcount : (T.filter (fun f => tail f = g)).card ≤ n / (∏ i : Fin 5, g i) := by
      calc
        _ ≤ (Icc 1 (n / (∏ i : Fin 5, g i))).card := by
          apply card_le_card_of_injOn (fun f : Fin 6 → ℕ => f 0)
          · intro f hf
            have hfT := (mem_filter.mp hf).1
            have hfg := (mem_filter.mp hf).2
            have hfA := (mem_filter.mp hfT).1
            have hfS := (mem_filter.mp (mem_filter.mp hfT).2).1
            apply mem_Icc.mpr
            refine ⟨(mem_Icc.mp (Fintype.mem_piFinset.mp hfA 0)).1, ?_⟩
            apply (Nat.le_div_iff_mul_le hP).mpr
            have he : (∏ i : Fin 6, f i) = f 0 * ∏ i : Fin 5, g i := by
              rw [Fin.prod_univ_succ]
              have ht : (fun i : Fin 5 => f i.succ) = g := hfg
              rw [ht]
            rw [← he]
            exact (mem_Icc.mp hfS).2
          · intro f hf f' hf' h0
            have hfT := (mem_filter.mp hf).2
            have hfT' := (mem_filter.mp hf').2
            funext i
            refine Fin.cases h0 (fun j => ?_) i
            exact (congrFun hfT j).trans (congrFun hfT' j).symm
        _ = _ := by simp
    calc
      _ ≤ ((n / (∏ i : Fin 5, g i) : ℕ) : ℝ) := by exact_mod_cast hcount
      _ ≤ (n : ℝ) / (∏ i : Fin 5, (g i : ℝ)) := by
        rw [← Nat.cast_prod]
        exact Nat.cast_div_le
      _ ≤ y / (∏ i : Fin 5, (g i : ℝ)) := by
        apply div_le_div_of_nonneg_right (Nat.floor_le (by linarith))
        positivity
      _ = _ := by rw [prod_div_distrib, prod_const_one]; ring
  change (T.card : ℝ) ≤ _
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  calc
    _ ≤ ∑ g ∈ B, y * ∏ i : Fin 5, (1 : ℝ) / g i := sum_le_sum hbound
    _ = y * (∑ j ∈ Icc 1 n, (1 : ℝ) / j) ^ 5 := by
      rw [← mul_sum]
      dsimp [B]
      rw [sum_prod_piFinset (Icc 1 n) (fun (_ : Fin 5) (j : ℕ) => (1 : ℝ) / j)]
      simp
    _ ≤ y * (1 + log y) ^ 5 := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply pow_le_pow_left₀ (by positivity)
      have hh := harmonic_floor_le_one_add_log y hy
      rw [harmonic_eq_sum_Icc, Rat.cast_sum] at hh
      simpa only [Rat.cast_inv, Rat.cast_natCast, one_div] using hh

/-- LEAF. Unit U-1544. For y ≥ 1, Σ_{d ≤ y, d squarefree} 6^{ν(d)} ≤ y (1 + log y)⁶.
Route: the sum is at most y Σ_{d ≤ y} μ²(d) 6^{ν(d)}/d, and the true size is ≍ y log⁵ y.
This bounds the remainder R_q = O(B_N z^{2a} ...) of p. 64, where 3^{ν(d)}|R(dq)| ≤ 2 B_N 6^{ν(d)}. -/
theorem sum_six_pow_omega_le {y : ℝ} (hy : 1 ≤ y) :
    ∑ d ∈ (Icc 1 ⌊y⌋₊).filter Squarefree, (6 : ℝ) ^ ω d ≤ y * (1 + log y) ^ 6 := by
  have hbase : 1 ≤ 1 + log y := by have := log_nonneg hy; linarith
  exact (sum_six_pow_omega_le_five hy).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega : 5 ≤ 6)) (by linarith))

lemma omega_mul_prime {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    ω (d * p) = ω d + 1 := by
  rw [ArithmeticFunction.cardDistinctFactors_mul
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm,
    ArithmeticFunction.cardDistinctFactors_apply_prime hp]

/-- The remainder of `sieveQ`: |r_d| ≤ 2^{ν(d)+1} 2^{ν(N)} for d ∣ P(z), q ∈ Qset N, N ≥ 1.
Assembly from `multSum_sieveQ`, `nuT_of_squarefree`, `sqfree_coprime_mul_q` and the
leaves of `lemma1`. This is R(dq) of Lemma 1 with ω(dq) = 2ω(d), p. 63. -/
theorem rem_sieveQ_le {N q d : ℕ} (y : ℝ) (hy : 1 ≤ y) (hN : 1 ≤ N) (hq : q ∈ Qset N)
    (hd : d ∣ Pz N) :
    |BoundingSieve.rem (s := (sieveQ N q y hy).toBoundingSieve) d| ≤
      2 ^ (ω d + 1) * 2 ^ ω N := by
  obtain ⟨hsq, hcop, hqd⟩ := sqfree_coprime_mul_q hq hd
  have hqp : q.Prime := (mem_filter.mp hq).2.1
  have hd0 : d ≠ 0 := fun h => Pz_ne_zero N (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hdsq : Squarefree d := (Pz_squarefree N).squarefree_of_dvd hd
  have hL := lemma1 hN hsq hcop
  rw [omega_mul_prime hqp hqd] at hL
  unfold BoundingSieve.rem
  rw [multSum_sieveQ y hy hq hd]
  have hnu : (sieveQ N q y hy).toBoundingSieve.nu d = 2 ^ ω d / (d : ℝ) := nuT_of_squarefree hdsq
  have hX : (sieveQ N q y hy).toBoundingSieve.totalMass = 2 * (N.totient : ℝ) / q := rfl
  rw [hnu, hX]
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have heq : (2 : ℝ) ^ ω d / d * (2 * (N.totient : ℝ) / q) =
      2 ^ (ω d + 1) * (N.totient : ℝ) / ((d * q : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [heq]
  exact hL

/-- W_q of p. 64: the sum of μ²(m)/f₁(m) = ∏_{p ∣ m} 2/(p - 2) over m ≤ w with every prime
factor of m at most z = N^{1/6}, odd and prime to N; that is, over the divisors m ≤ w of P(z).
On p. 64, w = z^a. -/
def Wq (N : ℕ) (w : ℝ) : ℝ :=
  ∑ l ∈ (Pz N).divisors.filter (fun l : ℕ => (l : ℝ) ≤ w),
    ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2)

/-- The p. 63 Selberg step with the sharper elementary fifth-logarithm remainder proved
here. The paper's squared logarithmic remainder on p. 64 is not asserted by this theorem. -/
theorem Sq_le_selberg_five {N q : ℕ} {w : ℝ} (hN : Even N) (hN1 : 1 ≤ N) (hq : q ∈ Qset N)
    (hw : 1 ≤ w) :
    ((Sq N q).card : ℝ) ≤ 2 * (N.totient : ℝ) / (q * Wq N w) +
      2 ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 5) := by
  have hy : (1 : ℝ) ≤ w ^ 2 := by nlinarith
  set s := sieveQ N q (w ^ 2) hy with hs
  have hb := LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple s
  rw [hs, siftedSum_sieveQ (w ^ 2) hy hN] at hb
  have hS : LeanLab.PNTSieve.SelbergSieve.selbergBoundingSum (sieveQ N q (w ^ 2) hy) = Wq N w := by
    rw [LeanLab.PNTSieve.SelbergSieve.selbergBoundingSum, Wq, sum_filter]
    refine sum_congr rfl fun l hl => ?_
    have hlP : l ∣ Pz N := Nat.dvd_of_mem_divisors hl
    rw [selbergTerms_sieveQ (w ^ 2) hy hlP]
    have hiff : ((l : ℝ) ^ 2 ≤ w ^ 2) ↔ ((l : ℝ) ≤ w) :=
      pow_le_pow_iff_left₀ (Nat.cast_nonneg l) (by linarith) two_ne_zero
    have hlev : (sieveQ N q (w ^ 2) hy).level = w ^ 2 := rfl
    rw [hlev]
    by_cases h : (l : ℝ) ≤ w
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  rw [hS] at hb
  have hX : (sieveQ N q (w ^ 2) hy).toBoundingSieve.totalMass = 2 * (N.totient : ℝ) / q := rfl
  rw [hX] at hb
  have hmain : 2 * (N.totient : ℝ) / q / Wq N w = 2 * (N.totient : ℝ) / (q * Wq N w) := by
    rw [div_div]
  rw [hmain] at hb
  refine hb.trans (add_le_add le_rfl ?_)
  -- the remainder
  have hP : (sieveQ N q (w ^ 2) hy).toBoundingSieve.prodPrimes = Pz N := rfl
  rw [hP]
  calc ∑ d ∈ (Pz N).divisors, (if (d : ℝ) ≤ w ^ 2 then (3 : ℝ) ^ ω d *
          |BoundingSieve.rem (s := (sieveQ N q (w ^ 2) hy).toBoundingSieve) d| else 0)
      ≤ ∑ d ∈ (Pz N).divisors, (if (d : ℝ) ≤ w ^ 2 then
          2 ^ (ω N + 1) * (6 : ℝ) ^ ω d else 0) := by
        refine sum_le_sum fun d hd => ?_
        split_ifs
        · have hr := rem_sieveQ_le (w ^ 2) hy hN1 hq (Nat.dvd_of_mem_divisors hd)
          calc (3 : ℝ) ^ ω d * |BoundingSieve.rem (s := (sieveQ N q (w ^ 2) hy).toBoundingSieve) d|
              ≤ 3 ^ ω d * (2 ^ (ω d + 1) * 2 ^ ω N) :=
                mul_le_mul_of_nonneg_left hr (by positivity)
            _ = 2 ^ (ω N + 1) * (6 : ℝ) ^ ω d := by
                rw [show (6 : ℝ) = 3 * 2 by norm_num, mul_pow]; ring
        · exact le_rfl
    _ = 2 ^ (ω N + 1) * ∑ d ∈ (Pz N).divisors.filter (fun d : ℕ => (d : ℝ) ≤ w ^ 2),
          (6 : ℝ) ^ ω d := by
        rw [mul_sum, sum_filter]
    _ ≤ 2 ^ (ω N + 1) * ∑ d ∈ (Icc 1 ⌊w ^ 2⌋₊).filter Squarefree, (6 : ℝ) ^ ω d := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ ?_) (by positivity)
        · intro d hd
          rw [mem_filter, Nat.mem_divisors] at hd
          have hd0 : d ≠ 0 := fun h => Pz_ne_zero N (Nat.eq_zero_of_zero_dvd (h ▸ hd.1.1))
          rw [mem_filter, mem_Icc]
          exact ⟨⟨Nat.pos_of_ne_zero hd0, Nat.le_floor hd.2⟩,
            (Pz_squarefree N).squarefree_of_dvd hd.1.1⟩
        · intro d _ _; positivity
    _ ≤ 2 ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 5) :=
        mul_le_mul_of_nonneg_left (sum_six_pow_omega_le_five hy) (by positivity)

/-- **The Selberg step**, first display of Section 3, p. 63: for even N ≥ 1, q ∈ Qset N and
w ≥ 1, with sieve level w², S(q) ≤ 2φ(N)/(q W_q) + R_q where
R_q ≤ 2^{ν(N)+1} w² (1 + log w²)⁶. Assembly from the lab's PROVED
`LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple`, using `siftedSum_sieveQ`,
`selbergTerms_sieveQ`, `sum_six_pow_omega_le` and the leaves of `rem_sieveQ_le`. -/
theorem Sq_le_selberg {N q : ℕ} {w : ℝ} (hN : Even N) (hN1 : 1 ≤ N) (hq : q ∈ Qset N)
    (hw : 1 ≤ w) :
    ((Sq N q).card : ℝ) ≤ 2 * (N.totient : ℝ) / (q * Wq N w) +
      2 ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6) := by
  have hy : (1 : ℝ) ≤ w ^ 2 := by nlinarith
  have hbase : 1 ≤ 1 + log (w ^ 2) := by have := log_nonneg hy; linarith
  refine (Sq_le_selberg_five hN hN1 hq hw).trans (add_le_add le_rfl ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ hbase (by omega : 5 ≤ 6)

/-! ### Vacuity instances -/

/-- The hypotheses of `Sq_le_selberg` can hold: N = 30030 = 2·3·5·7·11·13 is even and
q = 17 lies in Qset N, since 17⁶ > 30030 ≥ 17³ and 17 ∤ 30030; w = 1. -/
theorem vacuity_a1 : Even 30030 ∧ 1 ≤ 30030 ∧ 17 ∈ Qset 30030 ∧ (1 : ℝ) ≤ 1 := by
  refine ⟨by decide, by norm_num, ?_, le_rfl⟩
  simp only [Qset, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The hypotheses of `lemma1` can hold: N = 8, d = 15 squarefree and coprime to 8. -/
theorem vacuity_a2 : 1 ≤ 8 ∧ Squarefree 15 ∧ Nat.Coprime 15 8 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  show Squarefree (3 * 5)
  exact Nat.squarefree_mul_iff.2
    ⟨by norm_num, Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩

/-- The sieve problem `sieveQ` exists for concrete data, and its level is 1. -/
theorem vacuity_a3 : (sieveQ 30030 17 1 le_rfl).level = 1 := rfl

/-- Lemma 1, p. 61 for every positive modulus. The density vanishes when the modulus
shares a prime factor with N. The absolute error constant is 2 to omega N. -/
theorem lemma1_all_moduli {N d : ℕ} (hN : 1 ≤ N) (hd : 0 < d) :
    |(((Aset N).filter (fun n => d ∣ n * (N - n))).card : ℝ) -
        (if d.Coprime N then (2 : ℝ) ^ ω d else 0) * (N.totient : ℝ) / d| ≤
      (if d.Coprime N then (2 : ℝ) ^ ω d else 0) * 2 ^ ω N := by
  by_cases hc : d.Coprime N
  · rw [ite_eq_left hc]
    exact lemma1_coprime hN hd hc
  · obtain ⟨p, hp, hpd, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hempty : (Aset N).filter (fun n => d ∣ n * (N - n)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro n hn hdiv
      have hn' := mem_Aset.mp hn
      rcases hp.dvd_mul.mp (hpd.trans hdiv) with hpn | hpn
      · exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpn hpN) hn'.2.2
      · have hpn' : p ∣ n := by
          simpa [Nat.sub_sub_self hn'.2.1] using Nat.dvd_sub hpN hpn
        exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpn' hpN) hn'.2.2
    simp [hc, hempty]

/-- The Selberg denominator Wq is at least one for w at least one. The divisor 1 contributes one and all other terms are nonnegative. Section 3 p. 64. -/
theorem one_le_Wq (N : ℕ) {w : ℝ} (hw : 1 ≤ w) : 1 ≤ Wq N w := by
  have h1 : 1 ∈ (Pz N).divisors.filter (fun l : ℕ => (l : ℝ) ≤ w) := by
    simp [Pz_ne_zero, hw]
  calc
    1 = ∏ p ∈ (1 : ℕ).primeFactors, 2 / ((p : ℝ) - 2) := by simp
    _ ≤ Wq N w := by
      unfold Wq
      refine single_le_sum (f := fun l : ℕ => ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2)) ?_ h1
      intro l hl
      apply prod_nonneg
      intro p hp
      have hpd := Nat.dvd_of_mem_divisors (mem_filter.mp hl).1
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpP := prime_dvd_Pz hprime ((Nat.dvd_of_mem_primeFactors hp).trans hpd)
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_siftPrimes.mp hpP).2.2.1
      positivity

/-- For fixed N the finite denominator Wq is monotone in its cutoff w since all terms are nonnegative. Section 3 p. 64. -/
theorem Wq_mono (N : ℕ) : Monotone (Wq N) := by
  intro a b hab
  unfold Wq
  apply sum_le_sum_of_subset_of_nonneg
  · intro l hl
    exact mem_filter.mpr ⟨(mem_filter.mp hl).1, (mem_filter.mp hl).2.trans hab⟩
  · intro l hl _
    apply prod_nonneg
    intro p hp
    have hpd := Nat.dvd_of_mem_divisors (mem_filter.mp hl).1
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpP := prime_dvd_Pz hprime ((Nat.dvd_of_mem_primeFactors hp).trans hpd)
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_siftPrimes.mp hpP).2.2.1
    positivity

/-- On squarefree d the sum over e dividing d of mu of e times the ratio of d/e to 2 to omega of d/e equals the product of p minus 2 divided by 2. This is the finite coprime-modulus formula for f1 in p. 61. -/
theorem moebius_transform_density {d : ℕ} (hd : Squarefree d) :
    (∑ e ∈ d.divisors, (μ e : ℝ) * (((d / e : ℕ) : ℝ) / 2 ^ ω (d / e))) =
      ∏ p ∈ d.primeFactors, ((p : ℝ) - 2) / 2 := by
  let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => (p : ℝ) / 2)
  have hf (n : ℕ) (hn : Squarefree n) : f n = (n : ℝ) / 2 ^ ω n := by
    rw [ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero, prod_div_distrib,
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn, prod_const]
    congr 2
  have hi := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
    ArithmeticFunction.isMultiplicative_moebius.intCast
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors (fun p => (p : ℝ) / 2)) hd
  rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ((μ : ArithmeticFunction ℝ) a) * f b)] at hi
  calc
    _ = ∑ e ∈ d.divisors, ((μ : ArithmeticFunction ℝ) e) * f (d / e) := by
      apply sum_congr rfl
      intro e he
      rw [hf _ (hd.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)))]
      rfl
    _ = _ := by
      rw [← hi]
      apply prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      simp only [ArithmeticFunction.add_apply, ArithmeticFunction.intCoe_apply,
        ArithmeticFunction.moebius_apply_prime hprime, Int.cast_neg, Int.cast_one]
      rw [ArithmeticFunction.prodPrimeFactors_apply hprime.ne_zero, hprime.primeFactors, prod_singleton]
      ring

/-- For every positive delta, 2 to omega of N is bounded by C times N to delta for all N at least one, with a positive C depending only on delta. This proves the B_N growth assertion on p. 63. The proof uses the lab divisor bound from HeathBrown1985.DivisorEps. -/
theorem two_pow_omega_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (2 : ℝ) ^ ω N ≤ C * (N : ℝ) ^ δ := by
  let k : ℕ := ⌈δ⁻¹⌉₊ + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkle : (k : ℝ)⁻¹ ≤ δ := by
    rw [inv_eq_one_div, div_le_iff₀ hkR]
    have hc := Nat.le_ceil (δ⁻¹)
    have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hcR : δ⁻¹ ≤ (k : ℝ) := by dsimp [k]; push_cast; linarith
    have := mul_le_mul_of_nonneg_left hcR hδ.le
    rw [mul_inv_cancel₀ hδ.ne'] at this
    nlinarith
  obtain ⟨C, hC, hb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨C, hC, fun N hN => ?_⟩
  have hcount : (2 : ℝ) ^ ω N ≤ (N.divisors.card : ℝ) := by
    rw [← sum_abs_moebius_divisors (by omega)]
    calc
      ∑ e ∈ N.divisors, |(μ e : ℝ)| ≤ ∑ e ∈ N.divisors, (1 : ℝ) := by
        apply sum_le_sum
        intro e _
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      _ = _ := by simp
  refine hcount.trans ((hb N hN).trans ?_)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hkle

/-- The full sum of products of 2 divided by p minus 2 over divisors of P of z equals the finite product of p divided by p minus 2 over the sifting primes. This is the finite Euler product normalization of Wq in Section 3 p. 64. -/
theorem Wq_full_sum (N : ℕ) :
    (∑ l ∈ (Pz N).divisors, ∏ p ∈ l.primeFactors, 2 / ((p : ℝ) - 2)) =
      ∏ p ∈ siftPrimes N, (p : ℝ) / ((p : ℝ) - 2) := by
  let f : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (fun p => 2 / ((p : ℝ) - 2))
  have hi := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p => 2 / ((p : ℝ) - 2))).prodPrimeFactors_one_add_of_squarefree (Pz_squarefree N)
  have hpf : (Pz N).primeFactors = siftPrimes N :=
    Nat.primeFactors_prod (fun p hp => (mem_siftPrimes.mp hp).2.1)
  calc
    _ = ∑ l ∈ (Pz N).divisors, f l := by
      apply sum_congr rfl
      intro l hl
      rw [ArithmeticFunction.prodPrimeFactors_apply (Nat.pos_of_mem_divisors hl).ne']
    _ = ∏ p ∈ (Pz N).primeFactors, (1 + f p) := hi.symm
    _ = _ := by
      rw [hpf]
      apply prod_congr rfl
      intro p hp
      have hprime := (mem_siftPrimes.mp hp).2.1
      rw [ArithmeticFunction.prodPrimeFactors_apply hprime.ne_zero, hprime.primeFactors, prod_singleton]
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_siftPrimes.mp hp).2.2.1
      field_simp
      ring

/-- At every real cutoff w, Wq is bounded above by the finite product of p divided by p minus 2 over the sifting primes. Section 3 p. 64 and positivity of its summands. -/
theorem Wq_le_eulerProduct (N : ℕ) (w : ℝ) :
    Wq N w ≤ ∏ p ∈ siftPrimes N, (p : ℝ) / ((p : ℝ) - 2) := by
  rw [← Wq_full_sum N]
  unfold Wq
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro l hl _
  apply prod_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpP := prime_dvd_Pz hprime ((Nat.dvd_of_mem_primeFactors hp).trans (Nat.dvd_of_mem_divisors hl))
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_siftPrimes.mp hpP).2.2.1
  positivity

/-! ### CODEX task178 concrete instances

These examples verify the listed statement instances and include nonsquarefree moduli.
-/

example : Nat.Coprime 9 8 ∧ ¬ Squarefree 9 := by
  refine ⟨by norm_num, ?_⟩
  change ¬ Squarefree (3 ^ 2)
  rw [Nat.squarefree_pow_iff Nat.prime_three.ne_one (by norm_num)]
  norm_num
example : (rootsMod 8 9).card = 2 := by
  have h := card_rootsMod_coprime (N := 8) (d := 9) (by norm_num) (by norm_num)
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num,
    ArithmeticFunction.cardDistinctFactors_apply_prime_pow Nat.prime_three (by norm_num)] at h
  exact h
example : ((Aset 8).filter (fun n => 4 ∣ n * (8 - n))).card = 0 := by decide
example : (∑ e ∈ (6 : ℕ).divisors, (μ e : ℝ) * ((6 / e : ℕ) : ℝ)) = 2 := by
  convert sum_moebius_div_eq_totient 6 using 1
  norm_cast
example : (∑ e ∈ (12 : ℕ).divisors, |(μ e : ℝ)|) = 4 := by
  rw [sum_abs_moebius_divisors (by norm_num)]
  norm_num [ArithmeticFunction.cardDistinctFactors_apply]
example : ((sieveQ 30030 17 1 le_rfl).level : ℝ) = 1 := vacuity_a3
example : Even 30030 ∧ 17 ∈ Qset 30030 := ⟨vacuity_a1.1, vacuity_a1.2.2.1⟩
example : 1 ≤ Wq 30030 1 := one_le_Wq _ le_rfl
example : Wq 30030 1 ≤ Wq 30030 2 := Wq_mono _ (by norm_num)
example : (∑ e ∈ (15 : ℕ).divisors, (μ e : ℝ) * (((15 / e : ℕ) : ℝ) / 2 ^ ω (15 / e))) =
    ∏ p ∈ (15 : ℕ).primeFactors, ((p : ℝ) - 2) / 2 := by
  apply moebius_transform_density
  exact vacuity_a2.2.1
example : ∑ d ∈ (Icc 1 ⌊(2 : ℝ)⌋₊).filter Squarefree, (6 : ℝ) ^ ω d ≤
    2 * (1 + log 2) ^ 5 := sum_six_pow_omega_le_five (by norm_num)
example : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (2 : ℝ) ^ ω N ≤ C * (N : ℝ) ^ (1 : ℝ) :=
  two_pow_omega_le (by norm_num)

/-- An elementary convolution identity for the route to Lemma 3 on p. 62. The reciprocal
Moebius function is the Dirichlet inverse of the reciprocal function. This auxiliary identity
uses Mathlib's Moebius inversion and does not assume any analytic input. -/
theorem moebius_reciprocal_convolution (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, f n = (μ n : ℝ) / n) (hg : ∀ n, g n = (n : ℝ)⁻¹) : f * g = 1 := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  have hmu := congrArg (fun h : ArithmeticFunction ℝ => h n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmu
  have hsum : ∑ e ∈ n.divisors, f e * g (n / e) =
      (∑ e ∈ n.divisors, (μ e : ℝ)) / n := by
    rw [sum_div]
    apply sum_congr rfl
    intro e he
    rw [hf, hg]
    have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
    have hq0 : ((n / e : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors he))
        (Nat.pos_of_mem_divisors he)).ne'
    have heq : (e : ℝ) * ((n / e : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)
    rw [← heq]
    field_simp
  rw [hsum]
  change (∑ e ∈ n.divisors, (μ e : ℝ)) / n = if n = 1 then 1 else 0
  change (∑ e ∈ n.divisors, (μ e : ℝ)) = if n = 1 then 1 else 0 at hmu
  rw [hmu]
  split_ifs with h
  · subst n; norm_num
  · simp

example : ∃ f g : ArithmeticFunction ℝ,
    (∀ n, f n = (μ n : ℝ) / n) ∧ (∀ n, g n = (n : ℝ)⁻¹) ∧ f * g = 1 := by
  let f : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩
  exact ⟨f, g, (fun _ => rfl), (fun _ => rfl),
    moebius_reciprocal_convolution f g (fun _ => rfl) (fun _ => rfl)⟩

end LeanLab.AlmostPrimeSums.Decomp1544a
