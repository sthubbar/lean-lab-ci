/-
Kaniecki 1995, P0022: Section 3 assembled. The interval property and the Theorem, p. 373,
CONDITIONAL on the cited inputs `Lemma5`, `Eq23`, `Lemma6`, `YoungPotler`, `Sinisalo`,
`ChenWang`, and RH where the paper assumes it.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here proves it.

The assembled route differs from the paper's text in one place: Section 3 applies (23)-(24)
to the length `h` of an empty interval and uses `h ≤ λ(λ(x))` to keep `T ≥ e^{51}`; here
(23)-(24) are applied with `h = 1.4045 · 10^{12}` itself, and the Lemma 6 range is extended
from `e^{78}` to `e^{78.5}`, which keeps `T = 2x/h ≥ e^{51}` without that step.
-/
import Mathlib
import LeanLab.Kaniecki1995.Statements
import LeanLab.Kaniecki1995.Numerics
import LeanLab.Kaniecki1995.Section3

namespace LeanLab.Kaniecki1995
open Real Finset MeasureTheory LeanLab.SchnirelmannConstant

/-! ### Primes: next prime, largest prime below, gaps -/

theorem nextPrime_spec (p : ℕ) : p + 1 ≤ nextPrime p ∧ (nextPrime p).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (p + 1))

theorem nextPrime_min {p q : ℕ} (h1 : p < q) (h2 : q.Prime) : nextPrime p ≤ q :=
  Nat.find_min' _ ⟨h1, h2⟩

theorem lp_facts {m : ℕ} (hm : 3 ≤ m) :
    (Nat.findGreatest Nat.Prime m).Prime ∧ 3 ≤ Nat.findGreatest Nat.Prime m ∧
      Nat.findGreatest Nat.Prime m ≤ m ∧ m < nextPrime (Nat.findGreatest Nat.Prime m) := by
  refine ⟨Nat.findGreatest_spec hm Nat.prime_three, Nat.le_findGreatest hm Nat.prime_three,
    Nat.findGreatest_le m, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := nextPrime_spec (Nat.findGreatest Nat.Prime m)
  exact Nat.findGreatest_is_greatest (by omega) hc h2

theorem odd_of_prime_ge3 {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : Odd p :=
  hp.odd_of_ne_two (by omega)

theorem gap_le_lam {x : ℝ} (hx : 7 < x) {p : ℕ} (hp : p.Prime) (hpx : (p : ℝ) ≤ x) :
    nextPrime p - p ≤ lam x := by
  unfold lam
  rw [if_neg (by linarith)]
  apply Finset.le_sup (f := fun p => nextPrime p - p)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpx), hp⟩

/-- [16] in next-prime form. -/
theorem YP_next (hYP : YoungPotler) {p : ℕ} (hp : p.Prime) (hle : p ≤ 72630000000000) :
    nextPrime p ≤ p + 778 := by
  have h := gap_le_lam (x := 72630000000000) (by norm_num) hp (by exact_mod_cast hle)
  have h' : lam 72630000000000 ≤ 778 := by
    have h0 := hYP; unfold YoungPotler at h0; exact_mod_cast h0
  have := (nextPrime_spec p).1
  omega

/-- Lemma 6 in next-prime form. -/
theorem L6_next (hRH : RiemannHypothesis) (h6 : Lemma6) {x : ℝ} (hx : 2.3e9 ≤ x) {p : ℕ}
    (hp : p.Prime) (hpx : (p : ℝ) ≤ x) : (nextPrime p : ℝ) < p + gL6 x := by
  have h1 := gap_le_lam (by linarith) hp hpx
  have h2 := h6 hRH x hx
  have h3 := (nextPrime_spec p).1
  have : ((nextPrime p - p : ℕ) : ℝ) ≤ lam x := by exact_mod_cast h1
  rw [Nat.cast_sub (by omega)] at this
  linarith

/-! ### `λ(778) = 18`, p. 371, PROVED -/

/-- Every `p ≤ 778` has a prime in `[p+1, p+18]`; checked by the kernel. -/
def gap18OK : Bool :=
  (List.range 779).all (fun p => (List.range 18).any (fun j => primeB (p + 1 + j)))

theorem gap18OK_true : gap18OK = true := by decide +kernel

theorem nextPrime_le18 {p : ℕ} (hp : p ≤ 778) : nextPrime p ≤ p + 18 := by
  have h := gap18OK_true
  simp only [gap18OK, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨j, hj, hpj⟩ := h p (by omega)
  exact (nextPrime_min (by omega) (primeB_sound hpj)).trans (by omega)

theorem nextPrime_523 : nextPrime 523 = 541 := by
  apply le_antisymm (nextPrime_min (by norm_num) (by norm_num))
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := nextPrime_spec 523
  generalize nextPrime 523 = q at h1 h2 hc
  interval_cases q <;> norm_num at h2

/-- p. 371: `λ(778) = 18`, the maximal gap between consecutive primes `p ≤ 778` is
`541 - 523 = 18`. -/
theorem lam_778 : lam 778 = 18 := by
  unfold lam
  rw [if_neg (by norm_num)]
  have hfl : ⌊(778 : ℝ)⌋₊ = 778 := by norm_num
  rw [hfl]
  apply le_antisymm
  · apply Finset.sup_le
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have := nextPrime_le18 (p := p) (by omega)
    omega
  · have h : nextPrime 523 - 523 = 18 := by rw [nextPrime_523]
    rw [← h]
    apply Finset.le_sup (f := fun p => nextPrime p - p)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by norm_num, by norm_num⟩

/-! ### Small range, `x ≤ 7.263 · 10^{13}`: closed intervals of length 18, p. 371 -/

/-- Every `y ∈ [3, 780]` has a prime in `[y, y + 18]`; checked by the kernel. -/
def smallGapOK : Bool :=
  (List.range 778).all (fun i => (List.range 19).any (fun j => primeB (i + 3 + j)))

theorem smallGapOK_true : smallGapOK = true := by decide +kernel

theorem prime_in_short {y : ℕ} (h3 : 3 ≤ y) (h780 : y ≤ 780) :
    ∃ q, y ≤ q ∧ q ≤ y + 18 ∧ q.Prime := by
  have h := smallGapOK_true
  simp only [smallGapOK, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨j, hj, hpj⟩ := h (y - 3) (by omega)
  refine ⟨y - 3 + 3 + j, by omega, by omega, primeB_sound hpj⟩

/-- p. 371, first range: every `[x, x+18]`, `x ≤ 7.263 · 10^{13}`, contains a sum of two odd
primes, from the gap bound 778 of [16]. The paper takes `h = λ(778) = 18`. -/
theorem range1 (hYP : YoungPotler) (x : ℕ) (hx : x ≤ 72630000000000) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ x ≤ p + q ∧ p + q ≤ x + 18 := by
  rcases Nat.lt_or_ge x 7 with h | h
  · exact ⟨3, 3, Nat.prime_three, Nat.prime_three, by decide, by decide, by omega, by omega⟩
  obtain ⟨hp, hp3, hple, hq⟩ := lp_facts (m := x - 3) (by omega)
  set p1 := Nat.findGreatest Nat.Prime (x - 3)
  have hn := YP_next hYP hp (by omega)
  obtain ⟨q, hq1, hq2, hqp⟩ := prime_in_short (y := x - p1) (by omega) (by omega)
  exact ⟨p1, q, hp, hqp, odd_of_prime_ge3 hp hp3, odd_of_prime_ge3 hqp (by omega), by omega,
    by omega⟩

/-! ### Second range, `7.263 · 10^{13} < x ≤ e^{78.5}`, via Lemma 6, p. 371 -/

theorem range2 (hRH : RiemannHypothesis) (h6 : Lemma6) (hYP : YoungPotler) (x : ℕ)
    (hx1 : 72630000000000 < x) (hx2 : (x : ℝ) ≤ Real.exp 78.5) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ x ≤ p + q ∧ p + q ≤ x + 1404500000000 := by
  obtain ⟨hp1, hp13, hp1le, hq1⟩ := lp_facts (m := x - 3) (by omega)
  set p1 := Nat.findGreatest Nat.Prime (x - 3) with hp1def
  have hxR : (72630000000000 : ℝ) < x := by exact_mod_cast hx1
  have g1 := L6_next hRH h6 (x := x) (by linarith) hp1 (by exact_mod_cast (by omega : p1 ≤ x))
  have gx : gL6 x ≤ 5.4599e19 := (gL6_mono (by linarith) hx2).trans a1_gL6_e785
  set y := x - p1 with hydef
  have hy3 : 3 ≤ y := by omega
  have hyR : (y : ℝ) ≤ 5.46e19 := by
    have e1 : (y : ℝ) = x - p1 := by rw [hydef, Nat.cast_sub (by omega)]
    have e2 : (x : ℝ) ≤ nextPrime p1 + 2 := by exact_mod_cast (by omega : x ≤ nextPrime p1 + 2)
    linarith
  obtain ⟨hp0, hp03, hp0le, hq0⟩ := lp_facts hy3
  set p0 := Nat.findGreatest Nat.Prime y with hp0def
  have g0 : nextPrime p0 < p0 + 1220000000000 := by
    rcases Nat.lt_or_ge 72630000000000 p0 with hbig | hsmall
    · have hp0R : (72630000000000 : ℝ) < p0 := by exact_mod_cast hbig
      have h := L6_next hRH h6 (x := p0) (by linarith) hp0 le_rfl
      have hp0y : (p0 : ℝ) ≤ y := by exact_mod_cast hp0le
      have : gL6 p0 ≤ 1.22e12 := (gL6_mono (by linarith) (hp0y.trans hyR)).trans a1_gL6_546
      have : (nextPrime p0 : ℝ) < p0 + 1220000000000 := by linarith
      exact_mod_cast this
    · have := YP_next hYP hp0 hsmall
      omega
  obtain ⟨hq0a, hq0p⟩ := nextPrime_spec p0
  exact ⟨p1, nextPrime p0, hp1, hq0p, odd_of_prime_ge3 hp1 hp13,
    odd_of_prime_ge3 hq0p (by omega), by omega, by omega⟩

/-! ### Ranges 3 and 4, `e^{78.5} < x ≤ n₀`: (23), Lemma 5, (24), (25), pp. 372-373 -/

theorem range34 (hRH : RiemannHypothesis) (h5 : Lemma5) (h23 : Eq23) (x : ℕ)
    (hx1 : Real.exp 78.5 < (x : ℝ)) (hx2 : (x : ℝ) ≤ n0) : HasOddPairSumIn x 1.4045e12 := by
  by_contra hno
  set X : ℝ := (x : ℝ) with hXdef
  have hX0 : 0 < X := lt_trans (Real.exp_pos _) hx1
  have hX1 : 1 < X := lt_trans (by
    have : (1 : ℝ) < Real.exp 78.5 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)
    exact this) hx1
  set L := Real.log X with hLdef
  have hL1 : 78.5 < L := (Real.lt_log_iff_exp_lt hX0).2 hx1
  have hL2 : L ≤ Real.exp 11.503 := (Real.log_le_iff_le_exp hX0).2 (by simpa [n0] using hx2)
  set T := 2 * X / 1.4045e12 with hTdef
  have hT0 : 0 < T := by positivity
  have hlogT : Real.log T = L - Real.log (1.4045e12 / 2) := by
    rw [hTdef, show 2 * X / 1.4045e12 = X / (1.4045e12 / 2) by ring,
      Real.log_div hX0.ne' (by norm_num)]
  obtain ⟨kk1, kk2⟩ := kk_bounds
  have hlogT51 : 51 ≤ Real.log T := by rw [hlogT]; linarith
  have hTexp : Real.exp 51 ≤ T := by rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 hlogT51
  have hT1 : 1 < T := by linarith [exp51_ge]
  have hT702 : 7.02 < T := by linarith [exp51_ge]
  obtain ⟨hs0, hs1, _⟩ := sig_facts (le_refl 51) hTexp
  have hHle : (1.4045e12 : ℝ) ≤ 2 * Real.exp (-12) * X := by
    have : Real.exp 51 ≤ Real.exp (-12) * X := by
      have h1 : Real.exp 51 * Real.exp 12 ≤ X := by
        rw [← Real.exp_add]; exact le_trans (Real.exp_le_exp.2 (by norm_num)) hx1.le
      rw [Real.exp_neg]
      rw [le_inv_mul_iff₀ (Real.exp_pos _)]; linarith [mul_comm (Real.exp 51) (Real.exp 12)]
    linarith [exp51_ge]
  have hlow := h23 X 1.4045e12 aK cK (by norm_num) hHle (by norm_num [aK]) (by norm_num [aK])
    (by norm_num [cK]) (by norm_num [cK]) hno
  have hJI : JInt (2 * X / 1.4045e12) (sig aK cK (2 * X / 1.4045e12)) ≤
      IInt (2 * X / 1.4045e12) (sig aK cK (2 * X / 1.4045e12)) :=
    lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hpos : 0 < Real.log T ^ 2 / T := by positivity
  rcases le_or_gt L 84000 with hL84 | hL84
  · have hI := h5 hRH aK cK T 1.07 hT702 (by norm_num [cK]) (by norm_num) (by norm_num [aK])
      (by linarith)
    have hJc := Jconst_set1 (le_refl 51) hTexp
    set U := 1 / π * (√(fK aK cK T 1.07) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 *
      Real.log T ^ 2 / T with hU
    have hU0 : 0 ≤ U := by
      rw [hU, mul_div_assoc]; exact mul_nonneg (by have := Real.pi_pos; positivity) hpos.le
    have hlowU := (ENNReal.ofReal_le_ofReal_iff hU0).1 (hlow.trans (hJI.trans hI))
    have hUK : U < 0.271 * Real.log T ^ 2 / T := by
      rw [hU, mul_div_assoc, mul_div_assoc]; exact mul_lt_mul_of_pos_right hJc hpos
    have h25 := eq25 hX1 (by norm_num) hT1 hlowU hUK
    rw [← hTdef, hlogT] at h25
    have := a2_range3 kk1 kk2 hL1.le hL84
    linarith
  · have hlogT4 : 83970 ≤ Real.log T := by rw [hlogT]; linarith
    have hTexp4 : Real.exp 83970 ≤ T := by
      rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 hlogT4
    have hI := h5 hRH aK cK T 1.00013 hT702 (by norm_num [cK]) (by norm_num) (by norm_num [aK])
      (by linarith)
    have hJc := Jconst_set2 hTexp4
    set U := 1 / π * (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 *
      Real.log T ^ 2 / T with hU
    have hU0 : 0 ≤ U := by
      rw [hU, mul_div_assoc]; exact mul_nonneg (by have := Real.pi_pos; positivity) hpos.le
    have hlowU := (ENNReal.ofReal_le_ofReal_iff hU0).1 (hlow.trans (hJI.trans hI))
    have hUK : U < 0.1973261 * Real.log T ^ 2 / T := by
      rw [hU, mul_div_assoc, mul_div_assoc]; exact mul_lt_mul_of_pos_right hJc hpos
    have h25 := eq25 hX1 (by norm_num) hT1 hlowU hUK
    rw [← hTdef, hlogT] at h25
    have := a3_range4 kk1 kk2 hL84.le hL2
    linarith

/-! ### The interval property, p. 373, CONDITIONAL -/

/-- Every `[x, x + 1.4045 · 10^{12}]`, `x ≤ n₀`, contains a sum of two odd primes:
CONDITIONAL on RH, Lemma 5, (23), Lemma 6 and [16]. -/
theorem interval_of (hRH : RiemannHypothesis) (h5 : Lemma5) (h23 : Eq23) (h6 : Lemma6)
    (hYP : YoungPotler) : IntervalProperty := by
  intro x hx
  rcases Nat.lt_or_ge 72630000000000 x with h1 | h1
  · by_cases h2 : (x : ℝ) ≤ Real.exp 78.5
    · exact range2 hRH h6 hYP x h1 h2
    · push Not at h2
      obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := range34 hRH h5 h23 x h2 hx
      refine ⟨p, q, hp, hq, hop, hoq, by exact_mod_cast hlo, ?_⟩
      have : ((p + q : ℕ) : ℝ) ≤ ((x + 1404500000000 : ℕ) : ℝ) := by push_cast at hhi ⊢; linarith
      exact_mod_cast this
  · obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := range1 hYP x h1
    exact ⟨p, q, hp, hq, hop, hoq, hlo, by omega⟩

/-! ### Odd numbers below `1.405 · 10^{12}`: at most three primes, from [14] and [16] -/

theorem atMost3_of_ternary {n : ℕ} (h : IsTernarySum n) : AtMostPrimes 3 n := by
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := h
  exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add (AtMostPrimes.prime hr)

/-- Every odd `1 < m ≤ 7.263 · 10^{13}` is a sum of at most three primes, from the gap bound
of [16] and even Goldbach to `4 · 10^{11}` of [14]. -/
theorem odd_atMost3_small (hYP : YoungPotler) (hS : Sinisalo) {m : ℕ} (ho : Odd m) (h1 : 1 < m)
    (hm : m ≤ 72630000000000) : AtMostPrimes 3 m := by
  have h3 : 3 ≤ m := by obtain ⟨k, rfl⟩ := ho; omega
  obtain ⟨hp, hp3, hple, hq⟩ := lp_facts h3
  set p := Nat.findGreatest Nat.Prime m
  rcases Nat.eq_or_lt_of_le hple with heq | hlt
  · rw [← heq]; exact (AtMostPrimes.prime hp).mono (by norm_num)
  have hn := YP_next hYP hp (by omega)
  have hop := odd_of_prime_ge3 hp hp3
  have hev : Even (m - p) := by
    obtain ⟨a, ha⟩ := ho; obtain ⟨b, hb⟩ := hop; exact ⟨a - b, by omega⟩
  have hsplit : m = p + (m - p) := by omega
  rcases Nat.lt_or_ge (m - p) 4 with hs | hs
  · have h2 : m - p = 2 := by obtain ⟨c, hc⟩ := hev; omega
    rw [hsplit, h2]
    exact ((AtMostPrimes.prime hp).add (AtMostPrimes.prime Nat.prime_two)).mono (by norm_num)
  · have hg := hS (m - p) hev hs (by omega)
    rw [hsplit]
    exact ((AtMostPrimes.prime hp).add (AtMostPrimes.of_goldbach hg)).mono (by norm_num)

/-! ### The Theorem, p. 362, from the interval property, p. 373 -/

theorem odd_of_interval (hI : IntervalProperty) (hCW : ChenWang) (hYP : YoungPotler)
    (hS : Sinisalo) : ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  intro n ho h1
  rcases Nat.lt_or_ge 1405000000000 n with hbig | hsmall
  · set x := n - 1405000000000
    by_cases hx : (x : ℝ) ≤ n0
    · obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := hI x hx
      have hm : Odd (n - (p + q)) := by
        obtain ⟨a, ha⟩ := ho; obtain ⟨b, hb⟩ := hop; obtain ⟨c, hc⟩ := hoq
        exact ⟨a - b - c - 1, by omega⟩
      have h3 := odd_atMost3_small hYP hS hm (by omega) (by omega)
      have : n = (p + q) + (n - (p + q)) := by omega
      rw [this]
      exact (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add h3).mono (by norm_num)
    · push Not at hx
      have : n0 ≤ (n : ℝ) := by
        have : (x : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n _)
        linarith
      exact (atMost3_of_ternary (hCW n ho this)).mono (by norm_num)
  · exact (odd_atMost3_small hYP hS ho h1 (by omega)).mono (by norm_num)

theorem even_of_interval (hI : IntervalProperty) (hCW : ChenWang)
    (hG : ∃ G2 : ℕ, 1405 * 10 ^ 9 < G2 ∧ EvenGoldbachUpTo G2) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  obtain ⟨G2, hG2, hGb⟩ := hG
  intro n he
  rcases Nat.lt_or_ge 1405000000000 n with hbig | hsmall
  · set x := n - 1405000000000
    by_cases hx : (x : ℝ) ≤ n0
    · obtain ⟨p, q, hp, hq, hop, hoq, hlo, hhi⟩ := hI x hx
      have hm : Even (n - (p + q)) := by
        obtain ⟨a, ha⟩ := he; obtain ⟨b, hb⟩ := hop; obtain ⟨c, hc⟩ := hoq
        exact ⟨a - b - c - 1, by omega⟩
      have h2 := atMost2_of_even hGb hm (by norm_num at hG2; omega)
      have : n = (p + q) + (n - (p + q)) := by omega
      rw [this]
      exact (((AtMostPrimes.prime hp).add (AtMostPrimes.prime hq)).add h2).mono (by norm_num)
    · push Not at hx
      have ho : Odd (n - 3) := by obtain ⟨a, ha⟩ := he; exact ⟨a - 2, by omega⟩
      have : n0 ≤ ((n - 3 : ℕ) : ℝ) := by
        have : (x : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : x ≤ n - 3)
        linarith
      have h3 := atMost3_of_ternary (hCW (n - 3) ho this)
      have : n = 3 + (n - 3) := by omega
      rw [this]
      exact (AtMostPrimes.prime Nat.prime_three).add h3
  · exact (atMost2_of_even hGb he (by norm_num at hG2; omega)).mono (by norm_num)

/-- The Theorem, odd part, p. 362: CONDITIONAL on Lemma 5, (23), Lemma 6, [16], [14], [1]. -/
theorem theoremOdd_of (h5 : Lemma5) (h23 : Eq23) (h6 : Lemma6) (hYP : YoungPotler)
    (hS : Sinisalo) (hCW : ChenWang) : TheoremOdd :=
  fun hRH => odd_of_interval (interval_of hRH h5 h23 h6 hYP) hCW hYP hS

/-- The Theorem, even part, p. 362: CONDITIONAL on Lemma 5, (23), Lemma 6, [16], [1]. -/
theorem theoremEven_of (h5 : Lemma5) (h23 : Eq23) (h6 : Lemma6) (hYP : YoungPotler)
    (hCW : ChenWang) : TheoremEven :=
  fun hRH hG => even_of_interval (interval_of hRH h5 h23 h6 hYP) hCW hG

/-! ### The Remark, p. 373, CONDITIONAL on Lemma 5 and (23) -/

theorem remark_of (h5 : Lemma5) (h23 : Eq23) : RemarkStatement := by
  intro hRH x hx
  by_contra hno
  have hX0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hL : 84000 ≤ L := (Real.le_log_iff_exp_le hX0).2 hx
  have hX1 : 1 < x := by
    have : (1 : ℝ) < Real.exp 84000 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by norm_num)
    linarith
  set h := 144 * L ^ 2 with hhdef
  have hh0 : 0 < h := by positivity
  obtain ⟨hM, hR⟩ := p373_remark_num hL
  set T := 2 * x / h with hTdef
  have hT0 : 0 < T := by positivity
  have hlogT : Real.log T = L + Real.log 2 - Real.log h := by
    rw [hTdef, Real.log_div (by positivity) hh0.ne', Real.log_mul (by norm_num) hX0.ne']; ring
  have hTexp4 : Real.exp 83970 ≤ T := by
    rw [← Real.exp_log hT0]; exact Real.exp_le_exp.2 (by rw [hlogT]; exact hM)
  have hTexp : Real.exp 51 ≤ T := (Real.exp_le_exp.2 (by norm_num)).trans hTexp4
  have hT1 : 1 < T := by linarith [exp51_ge]
  have hT702 : 7.02 < T := by linarith [exp51_ge]
  obtain ⟨hs0, hs1, _⟩ := sig_facts (le_refl 51) hTexp
  have hh7 : (7 : ℝ) ≤ h := by rw [hhdef]; nlinarith
  have hHle : h ≤ 2 * Real.exp (-12) * x := by
    have h1 : Real.exp 12 ≤ T := (Real.exp_le_exp.2 (by norm_num)).trans hTexp4
    have h2 : h * T = 2 * x := by rw [hTdef]; field_simp
    have h3 : h * Real.exp 12 ≤ 2 * x := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hh0.le
    rw [Real.exp_neg, mul_comm 2, mul_assoc, le_inv_mul_iff₀ (Real.exp_pos _)]
    linarith
  have hlow := h23 x h aK cK hh7 hHle (by norm_num [aK]) (by norm_num [aK])
    (by norm_num [cK]) (by norm_num [cK]) hno
  have hJI : JInt (2 * x / h) (sig aK cK (2 * x / h)) ≤ IInt (2 * x / h) (sig aK cK (2 * x / h)) :=
    lintegral_mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hpos : 0 < Real.log T ^ 2 / T := by
    have : 0 < Real.log T := by rw [hlogT]; linarith
    positivity
  have hI := h5 hRH aK cK T 1.00013 hT702 (by norm_num [cK]) (by norm_num) (by norm_num [aK])
    (by linarith)
  have hJc := Jconst_set2 hTexp4
  set U := 1 / π * (√(fK aK cK T 1.00013) + √(f6 aK cK T) + √(f7 aK cK T)) ^ 2 *
    Real.log T ^ 2 / T with hU
  have hU0 : 0 ≤ U := by
    rw [hU, mul_div_assoc]; exact mul_nonneg (by have := Real.pi_pos; positivity) hpos.le
  have hlowU := (ENNReal.ofReal_le_ofReal_iff hU0).1 (hlow.trans (hJI.trans hI))
  have hUK : U < 0.1973261 * Real.log T ^ 2 / T := by
    rw [hU, mul_div_assoc, mul_div_assoc]; exact mul_lt_mul_of_pos_right hJc hpos
  have h25 := eq25 hX1 hh0 hT1 hlowU hUK
  rw [← hTdef, hlogT] at h25
  linarith

end LeanLab.Kaniecki1995

#print axioms LeanLab.Kaniecki1995.lam_778
#print axioms LeanLab.Kaniecki1995.nextPrime_523
#print axioms LeanLab.Kaniecki1995.smallGapOK_true
#print axioms LeanLab.Kaniecki1995.YP_next
#print axioms LeanLab.Kaniecki1995.L6_next
#print axioms LeanLab.Kaniecki1995.range1
#print axioms LeanLab.Kaniecki1995.range2
#print axioms LeanLab.Kaniecki1995.range34
#print axioms LeanLab.Kaniecki1995.interval_of
#print axioms LeanLab.Kaniecki1995.odd_atMost3_small
#print axioms LeanLab.Kaniecki1995.odd_of_interval
#print axioms LeanLab.Kaniecki1995.even_of_interval
#print axioms LeanLab.Kaniecki1995.theoremOdd_of
#print axioms LeanLab.Kaniecki1995.theoremEven_of
#print axioms LeanLab.Kaniecki1995.remark_of
