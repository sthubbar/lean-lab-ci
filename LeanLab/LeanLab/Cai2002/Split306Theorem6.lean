/-
Split of the input leaf306_theorem6, Bordignon, Johnston and Starichkova Theorem 6,
along the proof the paper gives in Section 2.4, pages 10 to 16.
Source: arXiv 2207.09452v6, papers/P0009.pdf. The paper proves Theorem 6 as
Nathanson's Theorem 9.7, reference 40 of the paper, with the constants of Lemma 14.
Pieces:
* Rosser weights with beta = 2, Nathanson Theorem 9.3, as summed in BJS display 28;
* the sieve inequalities and the support bound of those weights, Nathanson Theorem 9.3;
* the identities G(z, lambda plus or minus) = V(z) plus or minus the sum of T_n,
  Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14;
* the bounds for the sums of T_n, BJS Lemma 11, displays 13 and 14, Lemma 14 and Table 1;
* the constant K of BJS displays 29 and 30 from the strict hypothesis 4;
* the reduction from weights to displays 5 and 6 with the set Q, Nathanson Theorem 9.7.
The assembly theorem6_of_leaves306 is proved from these pieces.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ChenExplicit.LinearSieve

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

open Classical in
/-- The Rosser weights with beta = 2 of Nathanson Theorem 9.3, the weights lambda plus and
lambda minus of BJS Proposition 13, page 14, with the truncation of BJS display 28.
For squarefree d with prime factors p_1 > ... > p_r, the index of p_m is m, the number of
prime factors at least p_m, and p_m < y_m, y_m = (D / (p_1 ... p_m)) ^ (1 / 2), reads
p_1 ... p_(m-1) p_m ^ 3 < D. The weight is mu d when this holds for every index m of the
parity of j, and 0 otherwise; j = 1 gives lambda plus, j = 0 gives lambda minus. -/
def rosserWeight306 (D : ℝ) (j : ℕ) (d : ℕ) : ℝ :=
  if Squarefree d ∧ ∀ p ∈ d.primeFactors,
      (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = j % 2 →
        ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D
  then (ArithmeticFunction.moebius d : ℝ) else 0

open Classical in
/-- BJS display 28, T_n(D, z): the sum over d = p_1 ... p_n dividing P(z), p_1 > ... > p_n,
with y_n ≤ p_n, that is D ≤ d p_n ^ 2, and p_m < y_m for every m < n with m ≡ n mod 2,
of g(d) V(p_n). Here p_n is the least prime factor of d and V(u) is the product of
1 - g(p) over the primes p of P below u, BJS display 11. -/
def rosserT306 (P : Set ℕ) (g : ArithmeticFunction ℝ) (z D : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors.filter (fun d : ℕ =>
      d.primeFactors.card = n ∧ D ≤ (d : ℝ) * (d.minFac : ℝ) ^ 2 ∧
      ∀ p ∈ d.primeFactors, (d.primeFactors.filter (fun q => p ≤ q)).card < n →
        (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = n % 2 →
          ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D),
    g d * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (d.minFac : ℝ), (1 - g p)

/-- The Rosser weights are mu d or 0, so they lie in [-1, 1]. Nathanson Theorem 9.3. -/
theorem rosserWeight306_abs_le (D : ℝ) (j d : ℕ) : |rosserWeight306 D j d| ≤ 1 := by
  unfold rosserWeight306
  split_ifs
  · rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  · simp

/-- Primes of P below z are prime and lie below z. Helper for the assembly. -/
theorem mem_primesBelowIn306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) {z : ℝ} {p : ℕ}
    (hp : p ∈ LeanLab.ChenExplicit.primesBelowIn P z) : p.Prime ∧ (p : ℝ) < z := by
  classical
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨hP p hp.2, Nat.lt_ceil.mp hp.1⟩

/-- The product of the primes of P below z is squarefree. Helper for the assembly. -/
theorem squarefree_primesBelowIn306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    Squarefree (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (mem_primesBelowIn306 hP hp).1.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_primesBelowIn306 hP hp).1
    (mem_primesBelowIn306 hP hq).1).mpr hpq

/-- A prime factor of a divisor of the product of the primes of P below z lies below z.
Helper for the assembly. -/
theorem primeFactor_lt_of_dvd306 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) {z : ℝ} {d : ℕ}
    (hd : d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors) :
    ∀ p ∈ d.primeFactors, (p : ℝ) < z := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.mem_divisors.mp hd).1
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
  have hr' := mem_primesBelowIn306 hP hr
  rw [(Nat.prime_dvd_prime_iff_eq hpp hr'.1).mp hpr]
  exact hr'.2

/-! Helpers for leaf306_rosser_sieve, written by a workflow subagent, burst-20261122 S61. -/

theorem rw_mod_rs306 (D : ℝ) (j d : ℕ) : rosserWeight306 D (j % 2) d = rosserWeight306 D j d := by
  simp only [rosserWeight306, Nat.mod_mod]

theorem rw_one_rs306 (D : ℝ) (j : ℕ) : ∑ d ∈ (1:ℕ).divisors, rosserWeight306 D j d = 1 := by
  unfold rosserWeight306; simp

theorem sum_divisors_mul_rs306 (f : ℕ → ℝ) (p m : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ∑ d ∈ (p*m).divisors, f d = ∑ d ∈ m.divisors, f d + ∑ d ∈ m.divisors, f (p * d) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun d => p ∣ d), add_comm]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      refine ⟨?_, hm0⟩
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2).symm.dvd_of_dvd_mul_left h1
    · rintro ⟨h1, _⟩
      refine ⟨⟨Dvd.dvd.mul_left h1 p, mul_ne_zero hp.ne_zero hm0⟩, ?_⟩
      intro h; exact hpm (h.trans h1)
  · have : (p*m).divisors.filter (fun d => p ∣ d) = m.divisors.image (fun d => p * d) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h0⟩, ⟨e, rfl⟩⟩
        exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos h1, hm0⟩, rfl⟩
      · rintro ⟨e, ⟨h1, _⟩, rfl⟩
        exact ⟨⟨mul_dvd_mul_left p h1, mul_ne_zero hp.ne_zero hm0⟩, dvd_mul_right p e⟩
    rw [this, Finset.sum_image]
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h

theorem rw_mul_rs306 (D : ℝ) (j p d : ℕ) (hp : p.Prime) (hd : Squarefree d)
    (hlt : ∀ q ∈ d.primeFactors, q < p) :
    rosserWeight306 D j (p * d) =
      if (1 % 2 = j % 2 → (p:ℝ)^3 < D) then - rosserWeight306 (D / p) (j+1) d else 0 := by
  classical
  have hpd : p ∉ d.primeFactors := fun h => lt_irrefl _ (hlt p h)
  have hd0 : d ≠ 0 := hd.ne_zero
  have hndvd : ¬ p ∣ d := fun h => hpd (Nat.mem_primeFactors.mpr ⟨hp, h, hd0⟩)
  have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have hF : (p * d).primeFactors = insert p d.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hd0, hp.primeFactors]; rfl
  have hsq : Squarefree (p * d) ↔ Squarefree d := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨hcop, hp.squarefree, h⟩⟩
  have hmu : (ArithmeticFunction.moebius (p * d) : ℝ) = - (ArithmeticFunction.moebius d : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast; ring
  have hpp : (0:ℝ) < p := by exact_mod_cast hp.pos
  have f1 : (insert p d.primeFactors).filter (fun q => p ≤ q) = {p} := by
    rw [Finset.filter_insert, if_pos le_rfl]
    have : d.primeFactors.filter (fun q => p ≤ q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro q hq; exact not_le.mpr (hlt q hq)
    rw [this]; rfl
  have f2 : (insert p d.primeFactors).filter (fun q => p < q) = ∅ := by
    rw [Finset.filter_insert, if_neg (lt_irrefl p), Finset.filter_eq_empty_iff]
    intro q hq; exact not_lt.mpr (hlt q hq).le
  have f3 : ∀ r ∈ d.primeFactors, ((insert p d.primeFactors).filter (fun q => r ≤ q)).card
      = (d.primeFactors.filter (fun q => r ≤ q)).card + 1 := by
    intro r hr
    rw [Finset.filter_insert, if_pos (hlt r hr).le, Finset.card_insert_of_notMem]
    intro h; exact hpd (Finset.mem_filter.mp h).1
  have f4 : ∀ r ∈ d.primeFactors, ((∏ q ∈ (insert p d.primeFactors).filter (fun q => r < q), q : ℕ) : ℝ)
      = p * ((∏ q ∈ d.primeFactors.filter (fun q => r < q), q : ℕ) : ℝ) := by
    intro r hr
    rw [Finset.filter_insert, if_pos (hlt r hr), Finset.prod_insert]
    · push_cast; ring
    · intro h; exact hpd (Finset.mem_filter.mp h).1
  have key : (∀ r ∈ (p * d).primeFactors,
      ((p * d).primeFactors.filter (fun q => r ≤ q)).card % 2 = j % 2 →
        ((∏ q ∈ (p * d).primeFactors.filter (fun q => r < q), q : ℕ) : ℝ) * (r : ℝ) ^ 3 < D) ↔
      ((1 % 2 = j % 2 → (p:ℝ)^3 < D) ∧ ∀ r ∈ d.primeFactors,
      (d.primeFactors.filter (fun q => r ≤ q)).card % 2 = (j+1) % 2 →
        ((∏ q ∈ d.primeFactors.filter (fun q => r < q), q : ℕ) : ℝ) * (r : ℝ) ^ 3 < D / p) := by
    rw [hF, Finset.forall_mem_insert, f1, f2]
    apply and_congr
    · simp
    · apply forall₂_congr
      intro r hr
      rw [f3 r hr, f4 r hr, lt_div_iff₀ hpp]
      have : ((d.primeFactors.filter (fun q => r ≤ q)).card + 1) % 2 = j % 2 ↔
          (d.primeFactors.filter (fun q => r ≤ q)).card % 2 = (j+1) % 2 := by omega
      rw [this]
      constructor <;> intro h h' <;> have := h h' <;> linarith
  unfold rosserWeight306
  rw [hmu]
  by_cases hc : (1 % 2 = j % 2 → (p:ℝ)^3 < D)
  · rw [if_pos hc]
    by_cases h2 : Squarefree d ∧ ∀ r ∈ d.primeFactors,
      (d.primeFactors.filter (fun q => r ≤ q)).card % 2 = (j+1) % 2 →
        ((∏ q ∈ d.primeFactors.filter (fun q => r < q), q : ℕ) : ℝ) * (r : ℝ) ^ 3 < D / p
    · rw [if_pos h2, if_pos ⟨hsq.mpr h2.1, key.mpr ⟨hc, h2.2⟩⟩]
    · rw [if_neg h2, if_neg]
      · simp
      · rintro ⟨h3, h4⟩; exact h2 ⟨hsq.mp h3, (key.mp h4).2⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨_, h4⟩; exact hc (key.mp h4).1

theorem main_rs306 : ∀ m : ℕ, Squarefree m → m ≠ 1 → ∀ D : ℝ,
    0 ≤ ∑ d ∈ m.divisors, rosserWeight306 D 1 d ∧
      ∑ d ∈ m.divisors, rosserWeight306 D 0 d ≤ 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm hm1 D
  have hm0 : m ≠ 0 := hm.ne_zero
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  set p := m.primeFactors.max' hne with hpdef
  have hpmem : p ∈ m.primeFactors := Finset.max'_mem _ _
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpmem
  obtain ⟨m', hmm'⟩ := hpdvd
  have hm'0 : m' ≠ 0 := by rintro rfl; simp at hmm'; exact hm0 hmm'
  have hsq' : Squarefree m' := by rw [hmm'] at hm; exact hm.of_mul_right
  have hnd : ¬ p ∣ m' := by
    rintro ⟨k, rfl⟩
    have : p * p ∣ m := ⟨k, by rw [hmm']; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hm p this))
  have hlt' : ∀ q ∈ m'.primeFactors, q < p := by
    intro q hq
    have hqm : q ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors] at hq ⊢
      exact ⟨hq.1, hmm' ▸ Dvd.dvd.mul_left hq.2.1 p, hm0⟩
    have hle : q ≤ p := Finset.le_max' _ _ hqm
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (h ▸ Nat.dvd_of_mem_primeFactors hq) hnd
  have hm'lt : m' < m := by
    rw [hmm']; have := hp.two_le
    nlinarith [Nat.pos_of_ne_zero hm'0]
  have hsplit : ∀ (j : ℕ) (E : ℝ), ∑ d ∈ m.divisors, rosserWeight306 E j d =
      ∑ d ∈ m'.divisors, rosserWeight306 E j d +
        ∑ d ∈ m'.divisors, (if (1 % 2 = j % 2 → (p:ℝ)^3 < E)
          then - rosserWeight306 (E / p) (j+1) d else 0) := by
    intro j E
    rw [hmm', sum_divisors_mul_rs306 _ p m' hp hnd]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hdm : d ∣ m' := Nat.dvd_of_mem_divisors hd
    apply rw_mul_rs306 E j p d hp (hsq'.squarefree_of_dvd hdm)
    intro q hq
    exact hlt' q (Nat.primeFactors_mono hdm hm'0 hq)
  have h1 := hsplit 1 D
  have h0 := hsplit 0 D
  have e2 : ∀ d, rosserWeight306 (D / p) (1+1) d = rosserWeight306 (D / p) 0 d := by
    intro d; rw [← rw_mod_rs306]
  simp only [e2, zero_add] at h1 h0
  have hz : ¬ (1 % 2 = 0 % 2) := by decide
  simp only [hz, false_implies, if_true, Finset.sum_neg_distrib] at h0
  by_cases m'1 : m' = 1
  · subst m'1
    rw [rw_one_rs306] at h1 h0
    rw [rw_one_rs306] at h0
    refine ⟨?_, by rw [h0]; norm_num⟩
    rw [h1]
    split_ifs <;> simp only [Finset.sum_neg_distrib, Finset.sum_const_zero, rw_one_rs306] <;> norm_num
  · obtain ⟨a1, a0⟩ := ih m' hm'lt hsq' m'1 D
    obtain ⟨b1, b0⟩ := ih m' hm'lt hsq' m'1 (D / p)
    refine ⟨?_, by rw [h0]; linarith⟩
    rw [h1]
    split_ifs <;> simp only [Finset.sum_neg_distrib, Finset.sum_const_zero] <;> linarith

/-- Nathanson Theorem 9.3, the sieve property of the Rosser weights used by BJS
Proposition 13, page 14: for squarefree m, the sum of lambda plus over the divisors of m is
at least the indicator of m = 1, and the sum of lambda minus is at most it.
PROVED in burst-20261122 S61 by induction on the largest prime factor. -/
theorem leaf306_rosser_sieve (D : ℝ) (m : ℕ) (hm : Squarefree m) :
    (if m = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ m.divisors, rosserWeight306 D 1 d ∧
      ∑ d ∈ m.divisors, rosserWeight306 D 0 d ≤ (if m = 1 then (1 : ℝ) else 0) := by
  by_cases h : m = 1
  · subst h; simp only [if_true, rw_one_rs306]; exact ⟨le_rfl, le_rfl⟩
  · simp only [if_neg h]; exact main_rs306 m hm h D

/-- Nathanson Theorem 9.3, the level of the Rosser weights, as used in BJS display 10:
a nonzero weight at d with all prime factors below z ≤ D has d < D.
PROVED in burst-20261122 S61. For lambda plus apply the condition at the last odd index, for lambda minus at
the last even index, or use p_1 < z ≤ D when d is a single prime. -/
theorem leaf306_rosser_support (D z : ℝ) (hz : 1 < z) (hzD : z ≤ D) (j d : ℕ)
    (hd : ∀ p ∈ d.primeFactors, (p : ℝ) < z) (hw : rosserWeight306 D j d ≠ 0) :
    (d : ℝ) < D := by
  classical
  unfold rosserWeight306 at hw
  split_ifs at hw with hc
  · obtain ⟨hsq, hcond⟩ := hc
    have hprod : ∏ q ∈ d.primeFactors, q = d := Nat.prod_primeFactors_of_squarefree hsq
    have hD1 : 1 < D := by linarith
    rcases d.primeFactors.eq_empty_or_nonempty with hE | hne
    · rw [hE, prod_empty] at hprod
      rw [← hprod]; simpa using hD1
    set S := d.primeFactors with hS
    set p := S.min' hne with hpdef
    have hpS : p ∈ S := min'_mem _ _
    have hfle : S.filter (fun q => p ≤ q) = S :=
      filter_true_of_mem (fun q hq => min'_le _ _ hq)
    have hflt : S.filter (fun q => p < q) = S.erase p := by
      ext q; simp only [mem_filter, mem_erase]; constructor
      · rintro ⟨hq, hlt⟩; exact ⟨hlt.ne', hq⟩
      · rintro ⟨hne', hq⟩; exact ⟨hq, lt_of_le_of_ne (min'_le _ _ hq) (Ne.symm hne')⟩
    have hdp : d = p * ∏ q ∈ S.erase p, q :=
      hprod.symm.trans (mul_prod_erase S (fun x => x) hpS).symm
    have hp1 : (1:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpS).one_lt.le
    by_cases hpar : S.card % 2 = j % 2
    · have h := hcond p hpS (by rw [hfle]; exact hpar)
      rw [hflt] at h
      have hA : (0:ℝ) ≤ ((∏ q ∈ S.erase p, q : ℕ) : ℝ) := by positivity
      have : (d:ℝ) = (p:ℝ) * ((∏ q ∈ S.erase p, q : ℕ) : ℝ) := by
        rw [hdp]; push_cast; ring
      rw [this]
      have h2 : (0:ℝ) ≤ (p:ℝ)^2 - 1 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hA (by linarith : (0:ℝ) ≤ p)) h2]
    · rcases (S.erase p).eq_empty_or_nonempty with hE2 | hne2
      · rw [hE2, prod_empty, mul_one] at hdp
        have := hd p hpS
        rw [hdp]; linarith
      · set q := (S.erase p).min' hne2 with hqdef
        have hqS' : q ∈ S.erase p := min'_mem _ _
        have hqS : q ∈ S := mem_of_mem_erase hqS'
        have hpq : p < q := lt_of_le_of_ne (min'_le _ _ hqS) (Ne.symm (ne_of_mem_erase hqS'))
        have hfle2 : S.filter (fun x => q ≤ x) = S.erase p := by
          ext x; simp only [mem_filter, mem_erase]; constructor
          · rintro ⟨hx, hle⟩; exact ⟨by rintro rfl; omega, hx⟩
          · rintro ⟨hxp, hx⟩; exact ⟨hx, min'_le _ _ (mem_erase.mpr ⟨hxp, hx⟩)⟩
        have hflt2 : S.filter (fun x => q < x) = (S.erase p).erase q := by
          ext x; simp only [mem_filter, mem_erase]; constructor
          · rintro ⟨hx, hlt⟩; exact ⟨hlt.ne', by rintro rfl; omega, hx⟩
          · rintro ⟨hxq, hxp, hx⟩
            exact ⟨hx, lt_of_le_of_ne (min'_le _ _ (mem_erase.mpr ⟨hxp, hx⟩)) (Ne.symm hxq)⟩
        have hcard : 1 ≤ S.card := card_pos.mpr hne
        have h := hcond q hqS (by rw [hfle2, card_erase_of_mem hpS]; omega)
        rw [hflt2] at h
        have hB : (0:ℝ) ≤ ((∏ x ∈ (S.erase p).erase q, x : ℕ) : ℝ) := by positivity
        have hA : ∏ x ∈ S.erase p, x = q * ∏ x ∈ (S.erase p).erase q, x :=
          (mul_prod_erase _ _ hqS').symm
        have : (d:ℝ) = (p:ℝ) * (q:ℝ) * ((∏ x ∈ (S.erase p).erase q, x : ℕ) : ℝ) := by
          rw [hdp, hA]; push_cast; ring
        rw [this]
        have hpq' : (p:ℝ) < q := by exact_mod_cast hpq
        have hq1 : (1:ℝ) ≤ q := by linarith
        have h1 : (p:ℝ) * q ≤ q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_right hpq'.le (by linarith : (0:ℝ) ≤ q),
            mul_nonneg (sq_nonneg (q:ℝ)) (by linarith : (0:ℝ) ≤ q - 1)]
        nlinarith [mul_le_mul_of_nonneg_right h1 hB]
  · exact absurd rfl hw

/-! Helpers for leaf306_rosser_identity_upper, written by a workflow subagent, burst-20261122 S61. -/

open Classical in
def W_iu306 (D c : ℝ) (j : ℕ) (A : Finset ℕ) : Prop :=
  ∀ q ∈ A, (A.filter (fun x => q ≤ x)).card % 2 = j % 2 →
    c * ((∏ x ∈ A.filter (fun x => q < x), x : ℕ) : ℝ) * (q : ℝ) ^ 3 < D

open Classical in
def Tc_iu306 (D c : ℝ) (j : ℕ) (A : Finset ℕ) : Prop :=
  A.card % 2 = j % 2 ∧
  (∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ D ≤ c * ((∏ a ∈ A, a : ℕ) : ℝ) * (m : ℝ) ^ 2) ∧
  ∀ q ∈ A, (A.filter (fun x => q ≤ x)).card < A.card →
    (A.filter (fun x => q ≤ x)).card % 2 = j % 2 →
    c * ((∏ x ∈ A.filter (fun x => q < x), x : ℕ) : ℝ) * (q : ℝ) ^ 3 < D

open Classical in
noncomputable def G_iu306 (D : ℝ) (g : ℕ → ℝ) (c : ℝ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ A ∈ S.powerset, if W_iu306 D c j A then (-1 : ℝ) ^ A.card * ∏ a ∈ A, g a else 0

open Classical in
noncomputable def T_iu306 (D : ℝ) (g : ℕ → ℝ) (c : ℝ) (j : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ A ∈ S.powerset, if Tc_iu306 D c j A then
    (∏ a ∈ A, g a) * ∏ x ∈ S.filter (fun x => ∀ a ∈ A, x < a), (1 - g x) else 0

theorem filter_le_ins_iu306 (p q : ℕ) (B : Finset ℕ) (hq : q < p) :
    (insert p B).filter (fun x => q ≤ x) = insert p (B.filter (fun x => q ≤ x)) := by
  rw [filter_insert, if_pos hq.le]

theorem filter_lt_ins_iu306 (p q : ℕ) (B : Finset ℕ) (hq : q < p) :
    (insert p B).filter (fun x => q < x) = insert p (B.filter (fun x => q < x)) := by
  rw [filter_insert, if_pos hq]

theorem filter_le_top_iu306 (p : ℕ) (B : Finset ℕ) (hB : ∀ x ∈ B, x < p) :
    (insert p B).filter (fun x => p ≤ x) = {p} := by
  rw [filter_insert, if_pos le_rfl, filter_false_of_mem (fun x hx => by have := hB x hx; omega)]
  rfl

theorem filter_lt_top_iu306 (p : ℕ) (B : Finset ℕ) (hB : ∀ x ∈ B, x < p) :
    (insert p B).filter (fun x => p < x) = ∅ := by
  rw [filter_insert, if_neg (lt_irrefl p), filter_false_of_mem (fun x hx => by have := hB x hx; omega)]

theorem W_insert_iu306 (D c : ℝ) (j p : ℕ) (B : Finset ℕ) (hB : ∀ x ∈ B, x < p) :
    W_iu306 D c j (insert p B) ↔ ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D) ∧
      W_iu306 D (c * p) (j + 1) B := by
  have hpB : p ∉ B := fun h => lt_irrefl _ (hB p h)
  unfold W_iu306
  constructor
  · intro h
    refine ⟨fun hj => ?_, fun q hq hpar => ?_⟩
    · have := h p (mem_insert_self _ _) (by rw [filter_le_top_iu306 p B hB]; simpa using hj)
      rw [filter_lt_top_iu306 p B hB] at this
      simpa using this
    · have hqp := hB q hq
      have hpf : p ∉ B.filter (fun x => q ≤ x) := fun h' => hpB (mem_filter.1 h').1
      have hpf' : p ∉ B.filter (fun x => q < x) := fun h' => hpB (mem_filter.1 h').1
      have := h q (mem_insert_of_mem hq)
        (by rw [filter_le_ins_iu306 p q B hqp, card_insert_of_notMem hpf]; omega)
      rw [filter_lt_ins_iu306 p q B hqp, prod_insert hpf'] at this
      push_cast at this ⊢
      linarith
  · rintro ⟨h1, h2⟩ q hq hpar
    rcases mem_insert.1 hq with rfl | hq
    · rw [filter_le_top_iu306 q B hB] at hpar
      rw [filter_lt_top_iu306 q B hB]
      simpa using h1 (by simpa using hpar)
    · have hqp := hB q hq
      have hpf : p ∉ B.filter (fun x => q ≤ x) := fun h' => hpB (mem_filter.1 h').1
      have hpf' : p ∉ B.filter (fun x => q < x) := fun h' => hpB (mem_filter.1 h').1
      rw [filter_le_ins_iu306 p q B hqp, card_insert_of_notMem hpf] at hpar
      have := h2 q hq (by omega)
      rw [filter_lt_ins_iu306 p q B hqp, prod_insert hpf']
      push_cast at this ⊢
      linarith

theorem Tc_insert_iu306 (D c : ℝ) (j p : ℕ) (B : Finset ℕ) (hB : ∀ x ∈ B, x < p)
    (hne : B.Nonempty) :
    Tc_iu306 D c j (insert p B) ↔ ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D) ∧
      Tc_iu306 D (c * p) (j + 1) B := by
  have hpB : p ∉ B := fun h => lt_irrefl _ (hB p h)
  have hcard : (insert p B).card = B.card + 1 := card_insert_of_notMem hpB
  have hc1 : 1 ≤ B.card := card_pos.mpr hne
  unfold Tc_iu306
  rw [hcard, prod_insert hpB]
  constructor
  · rintro ⟨hpar, ⟨m, hm, hmin, hD⟩, h⟩
    refine ⟨fun hj => ?_, by omega, ?_, fun q hq hlt hpar' => ?_⟩
    · have := h p (mem_insert_self _ _) (by rw [filter_le_top_iu306 p B hB]; simp; omega)
        (by rw [filter_le_top_iu306 p B hB]; simpa using hj)
      rw [filter_lt_top_iu306 p B hB] at this
      simpa using this
    · rcases mem_insert.1 hm with rfl | hm
      · obtain ⟨b, hb⟩ := hne
        exact absurd (hmin b (mem_insert_of_mem hb)) (not_le.2 (hB b hb))
      · refine ⟨m, hm, fun a ha => hmin a (mem_insert_of_mem ha), ?_⟩
        push_cast at hD ⊢; linarith
    · have hqp := hB q hq
      have hpf : p ∉ B.filter (fun x => q ≤ x) := fun h' => hpB (mem_filter.1 h').1
      have hpf' : p ∉ B.filter (fun x => q < x) := fun h' => hpB (mem_filter.1 h').1
      have := h q (mem_insert_of_mem hq)
        (by rw [filter_le_ins_iu306 p q B hqp, card_insert_of_notMem hpf]; omega)
        (by rw [filter_le_ins_iu306 p q B hqp, card_insert_of_notMem hpf]; omega)
      rw [filter_lt_ins_iu306 p q B hqp, prod_insert hpf'] at this
      push_cast at this ⊢
      linarith
  · rintro ⟨h1, hpar, ⟨m, hm, hmin, hD⟩, h2⟩
    refine ⟨by omega, ⟨m, mem_insert_of_mem hm, fun a ha => ?_, ?_⟩, fun q hq hlt hpar' => ?_⟩
    · rcases mem_insert.1 ha with rfl | ha
      · exact (hB m hm).le
      · exact hmin a ha
    · push_cast at hD ⊢; linarith
    · rcases mem_insert.1 hq with rfl | hq
      · rw [filter_le_top_iu306 q B hB] at hpar'
        rw [filter_lt_top_iu306 q B hB]
        simpa using h1 (by simpa using hpar')
      · have hqp := hB q hq
        have hpf : p ∉ B.filter (fun x => q ≤ x) := fun h' => hpB (mem_filter.1 h').1
        have hpf' : p ∉ B.filter (fun x => q < x) := fun h' => hpB (mem_filter.1 h').1
        rw [filter_le_ins_iu306 p q B hqp, card_insert_of_notMem hpf] at hpar' hlt
        have := h2 q hq (by omega) (by omega)
        rw [filter_lt_ins_iu306 p q B hqp, prod_insert hpf']
        push_cast at this ⊢
        linarith

theorem Tc_single_iu306 (D c : ℝ) (j p : ℕ) :
    Tc_iu306 D c j {p} ↔ (1 % 2 = j % 2) ∧ D ≤ c * (p : ℝ) ^ 3 := by
  unfold Tc_iu306
  simp only [card_singleton, prod_singleton, mem_singleton, forall_eq, exists_eq_left, le_refl,
    true_and]
  constructor
  · rintro ⟨h1, h2, -⟩; refine ⟨h1, ?_⟩; push_cast at h2; nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by push_cast; nlinarith, fun h => ?_⟩
    rw [filter_singleton, if_pos le_rfl, card_singleton] at h
    exact absurd h (lt_irrefl 1)


theorem G_insert_iu306 (D : ℝ) (g : ℕ → ℝ) (c : ℝ) (j p : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < p) :
    G_iu306 D g c j (insert p S) = G_iu306 D g c j S +
      -(g p) * (if ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D) then G_iu306 D g (c * p) (j + 1) S
        else 0) := by
  classical
  have hpS : p ∉ S := fun h => lt_irrefl _ (hS p h)
  unfold G_iu306
  rw [sum_powerset_insert hpS]
  congr 1
  by_cases hc : ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D)
  · rw [if_pos hc, mul_sum]
    apply sum_congr rfl
    intro B hB
    have hBp : ∀ x ∈ B, x < p := fun x hx => hS x (mem_powerset.1 hB hx)
    have hpB : p ∉ B := fun h => lt_irrefl _ (hBp p h)
    rw [W_insert_iu306 D c j p B hBp, and_iff_right hc]
    split_ifs
    · rw [prod_insert hpB, card_insert_of_notMem hpB]; ring
    · ring
  · rw [if_neg hc, mul_zero]
    apply sum_eq_zero
    intro B hB
    have hBp : ∀ x ∈ B, x < p := fun x hx => hS x (mem_powerset.1 hB hx)
    rw [if_neg]
    rw [W_insert_iu306 D c j p B hBp]
    tauto

theorem T_insert_iu306 (D : ℝ) (g : ℕ → ℝ) (c : ℝ) (j p : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < p) :
    T_iu306 D g c j (insert p S) = T_iu306 D g c j S +
      (if (1 % 2 = j % 2) ∧ D ≤ c * (p : ℝ) ^ 3 then g p * ∏ x ∈ S, (1 - g x) else 0) +
      g p * (if ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D) then T_iu306 D g (c * p) (j + 1) S
        else 0) := by
  classical
  have hpS : p ∉ S := fun h => lt_irrefl _ (hS p h)
  unfold T_iu306
  rw [sum_powerset_insert hpS, add_assoc]
  congr 1
  · apply sum_congr rfl
    intro A hA
    split_ifs with hT
    · obtain ⟨m, hm, -⟩ := hT.2.1
      have hmp := hS m (mem_powerset.1 hA hm)
      rw [filter_insert, if_neg (fun h => lt_asymm (h m hm) hmp)]
    · rfl
  · have key : ∀ B ∈ S.powerset,
        (if Tc_iu306 D c j (insert p B) then
          (∏ a ∈ insert p B, g a) *
            ∏ x ∈ (insert p S).filter (fun x => ∀ a ∈ insert p B, x < a), (1 - g x) else 0) =
        (if B = ∅ then
          (if (1 % 2 = j % 2) ∧ D ≤ c * (p : ℝ) ^ 3 then g p * ∏ x ∈ S, (1 - g x) else 0)
          else 0) +
        g p * (if ((1 % 2 = j % 2) → c * (p : ℝ) ^ 3 < D) then
          (if Tc_iu306 D (c * p) (j + 1) B then
            (∏ a ∈ B, g a) * ∏ x ∈ S.filter (fun x => ∀ a ∈ B, x < a), (1 - g x) else 0)
          else 0) := by
      intro B hB
      have hBp : ∀ x ∈ B, x < p := fun x hx => hS x (mem_powerset.1 hB hx)
      have hpB : p ∉ B := fun h => lt_irrefl _ (hBp p h)
      rcases B.eq_empty_or_nonempty with rfl | hne
      · have hT0 : ¬ Tc_iu306 D (c * p) (j + 1) ∅ := by
          rintro ⟨-, ⟨m, hm, -⟩, -⟩; simp at hm
        have hf : (insert p S).filter (fun x => ∀ a ∈ ({p} : Finset ℕ), x < a) = S := by
          rw [filter_insert]
          simp only [mem_singleton, forall_eq, lt_irrefl, if_false]
          exact filter_true_of_mem hS
        simp only [insert_empty_eq, hf, Tc_single_iu306, if_true, hT0, if_false, ite_self,
          mul_zero, add_zero, prod_singleton]
      · have hf : (insert p S).filter (fun x => ∀ a ∈ insert p B, x < a) =
            S.filter (fun x => ∀ a ∈ B, x < a) := by
          rw [filter_insert, if_neg (fun h => lt_irrefl p (h p (mem_insert_self _ _)))]
          apply filter_congr
          intro x hx
          simp only [mem_insert, forall_eq_or_imp, hS x hx, true_and]
        rw [if_neg hne.ne_empty, zero_add, Tc_insert_iu306 D c j p B hBp hne, hf,
          prod_insert hpB]
        split_ifs <;> first | ring1 | (exfalso; tauto)
    rw [sum_congr rfl key, sum_add_distrib, ← mul_sum, sum_ite_eq' S.powerset ∅,
      if_pos (empty_mem_powerset S)]
    congr 2
    split_ifs <;> simp

theorem main_iu306 (D : ℝ) (g : ℕ → ℝ) (S : Finset ℕ) :
    ∀ (c : ℝ) (j : ℕ), G_iu306 D g c j S =
      ∏ x ∈ S, (1 - g x) + (if j % 2 = 1 then 1 else -1) * T_iu306 D g c j S := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro c j
    have hT : T_iu306 D g c j ∅ = 0 := by
      unfold T_iu306
      simp only [powerset_empty, sum_singleton]
      rw [if_neg]
      rintro ⟨-, ⟨m, hm, -⟩, -⟩; simp at hm
    have hG : G_iu306 D g c j ∅ = 1 := by
      unfold G_iu306
      simp only [powerset_empty, sum_singleton]
      rw [if_pos (show W_iu306 D c j ∅ from fun q hq => by simp at hq)]
      simp
    rw [hT, hG]; simp
  | insert p S hS ih =>
    intro c j
    have hpS : p ∉ S := fun h => lt_irrefl _ (hS p h)
    rw [G_insert_iu306 D g c j p S hS, T_insert_iu306 D g c j p S hS, prod_insert hpS,
      ih c j, ih (c * p) (j + 1)]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      split_ifs <;> first | ring1 | (exfalso; omega) | (exfalso; linarith) | (exfalso; tauto)
    · have h' : (j + 1) % 2 = 0 := by omega
      have hj : (1 % 2 = j % 2) = True := eq_true (by omega)
      simp only [hj, true_and, forall_const]
      split_ifs <;> first | ring1 | (exfalso; omega) | (exfalso; linarith) | (exfalso; tauto)

theorem sum_divisors_prod_iu306 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℝ) :
    ∑ d ∈ (∏ p ∈ S, p).divisors, f d = ∑ A ∈ S.powerset, f (∏ a ∈ A, a) := by
  classical
  have hsq : Squarefree (∏ p ∈ S, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (hS p hp).squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  have h0 : (∏ p ∈ S, p) ≠ 0 := prod_ne_zero_iff.2 (fun p hp => (hS p hp).ne_zero)
  refine sum_nbij' (fun d => d.primeFactors) (fun A => ∏ a ∈ A, a) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_powerset, ← Nat.primeFactors_prod hS]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) h0
  · intro A hA
    exact Nat.mem_divisors.2 ⟨prod_dvd_prod_of_subset _ _ _ (mem_powerset.1 hA), h0⟩
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro A hA
    exact Nat.primeFactors_prod (fun p hp => hS p (mem_powerset.1 hA hp))
  · intro d hd
    rw [Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

/-- Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14:
G(z, lambda plus) = V(z) + the sum of T_n(D, z) over odd n.
PROVED in burst-20261122 S61 by induction adding the largest prime. -/
theorem leaf306_rosser_identity_upper (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (z D : ℝ) :
    ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
        rosserWeight306 D 1 d * g d =
      ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) +
        ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
          rosserT306 P g z D n := by
  unfold rosserT306
  have hSp : ∀ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p.Prime :=
    fun p hp => (mem_primesBelowIn306 hP hp).1
  have hmain := main_iu306 D (⇑g) (LeanLab.ChenExplicit.primesBelowIn P z) 1 1
  simp only [Nat.one_mod, if_true, one_mul] at hmain
  have hL : ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
      rosserWeight306 D 1 d * g d = G_iu306 D g 1 1 (LeanLab.ChenExplicit.primesBelowIn P z) := by
    rw [sum_divisors_prod_iu306 _ hSp, G_iu306]
    apply sum_congr rfl
    intro A hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hSp p (mem_powerset.1 hA hp)
    have hpf : (∏ a ∈ A, a).primeFactors = A := Nat.primeFactors_prod hAp
    have hsqA : Squarefree (∏ a ∈ A, a) := by
      refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
        fun p hp => (hAp p hp).squarefree
      simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hAp p hp) (hAp q hq)).mpr hpq
    have hmu : ((ArithmeticFunction.moebius (∏ a ∈ A, a) : ℤ) : ℝ) = (-1) ^ A.card := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime A hAp]
      push_cast
      rw [prod_congr rfl (fun p hp => by
        rw [ArithmeticFunction.moebius_apply_prime (hAp p hp)])]
      simp
    have hgA : g (∏ a ∈ A, a) = ∏ a ∈ A, g a := hg.map_prod_of_prime A hAp
    unfold rosserWeight306
    rw [hpf, hgA]
    by_cases hW : W_iu306 D 1 1 A
    · rw [if_pos ⟨hsqA, fun p hp hpar => by simpa using hW p hp hpar⟩, if_pos hW, hmu]
    · rw [if_neg (fun h => hW (fun p hp hpar => by simpa using h.2 p hp hpar)), if_neg hW,
        zero_mul]
  have hR : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
      ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors.filter (fun d : ℕ =>
        d.primeFactors.card = n ∧ D ≤ (d : ℝ) * (d.minFac : ℝ) ^ 2 ∧
        ∀ p ∈ d.primeFactors, (d.primeFactors.filter (fun q => p ≤ q)).card < n →
          (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = n % 2 →
            ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D),
      g d * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (d.minFac : ℝ), (1 - g p) =
      T_iu306 D g 1 1 (LeanLab.ChenExplicit.primesBelowIn P z) := by
    rw [sum_congr rfl (fun n _ => sum_filter _ _), sum_comm, sum_divisors_prod_iu306 _ hSp, T_iu306]
    apply sum_congr rfl
    intro A hA
    have hAS := mem_powerset.1 hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hSp p (hAS hp)
    have hpf : (∏ a ∈ A, a).primeFactors = A := Nat.primeFactors_prod hAp
    have hgA : g (∏ a ∈ A, a) = ∏ a ∈ A, g a := hg.map_prod_of_prime A hAp
    have hd0 : (∏ a ∈ A, a) ≠ 0 := prod_ne_zero_iff.2 (fun p hp => (hAp p hp).ne_zero)
    simp only [hpf, hgA]
    by_cases hN : A.card ∈ (Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd
    · have hodd : A.card % 2 = 1 := Nat.odd_iff.1 (mem_filter.1 hN).2
      have hne : A.Nonempty :=
        card_pos.1 (by have := (mem_Icc.1 (mem_filter.1 hN).1).1; omega)
      have hd1 : (∏ a ∈ A, a) ≠ 1 := by
        intro h; rw [h, Nat.primeFactors_one] at hpf; exact hne.ne_empty hpf.symm
      set m := (∏ a ∈ A, a).minFac with hm
      have hmA : m ∈ A := by
        rw [← hpf]; exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hd1, Nat.minFac_dvd _, hd0⟩
      have hmle : ∀ a ∈ A, m ≤ a := fun a ha =>
        Nat.minFac_le_of_dvd (hAp a ha).two_le (dvd_prod_of_mem _ ha)
      have hfilt : LeanLab.ChenExplicit.primesBelowIn P (m : ℝ) =
          (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun x => ∀ a ∈ A, x < a) := by
        have hmS := hAS hmA
        ext x
        simp only [LeanLab.ChenExplicit.primesBelowIn, mem_filter, mem_range,
          Nat.ceil_natCast] at hmS ⊢
        constructor
        · rintro ⟨hx, hxP⟩; exact ⟨⟨by omega, hxP⟩, fun a ha => lt_of_lt_of_le hx (hmle a ha)⟩
        · rintro ⟨⟨_, hxP⟩, h⟩; exact ⟨h m hmA, hxP⟩
      rw [sum_eq_single_of_mem A.card hN (fun n _ hn => if_neg (fun h => hn h.1.symm)), hfilt]
      have hiff : (A.card = A.card ∧ D ≤ ((∏ a ∈ A, a : ℕ) : ℝ) * (m : ℝ) ^ 2 ∧
          ∀ p ∈ A, (A.filter (fun q => p ≤ q)).card < A.card →
            (A.filter (fun q => p ≤ q)).card % 2 = A.card % 2 →
            ((∏ q ∈ A.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D) ↔
            Tc_iu306 D 1 1 A := by
        unfold Tc_iu306
        rw [hodd]
        simp only [one_mul, Nat.one_mod, true_and]
        constructor
        · rintro ⟨hD, h⟩; exact ⟨⟨m, hmA, hmle, hD⟩, h⟩
        · rintro ⟨⟨m', hm'A, hm'le, hD⟩, h⟩
          have : m' = m := le_antisymm (hm'le m hmA) (hmle m' hm'A)
          subst this; exact ⟨hD, h⟩
      by_cases hT : Tc_iu306 D 1 1 A
      · rw [if_pos (hiff.2 hT), if_pos hT]
      · rw [if_neg (fun h => hT (hiff.1 h)), if_neg hT]
    · rw [sum_eq_zero (fun n hn => if_neg (fun h => hN (by rw [h.1]; exact hn))), if_neg]
      rintro ⟨hpar, ⟨m, hmA, -⟩, -⟩
      apply hN
      rw [mem_filter, mem_Icc, Nat.odd_iff]
      refine ⟨⟨card_pos.2 ⟨m, hmA⟩, card_le_card hAS⟩, ?_⟩
      simpa using hpar
  rw [hL, hR, hmain]

/-- Nathanson Lemma 9.3, as used in the proof of BJS Proposition 13, page 14:
G(z, lambda minus) = V(z) - the sum of T_n(D, z) over even n.
PROVED in burst-20261122 S61 from main_iu306 with parity 0. -/
theorem leaf306_rosser_identity_lower (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (z D : ℝ) :
    ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
        rosserWeight306 D 0 d * g d =
      ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) -
        ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
          rosserT306 P g z D n := by
  unfold rosserT306
  have hSp : ∀ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p.Prime :=
    fun p hp => (mem_primesBelowIn306 hP hp).1
  have hmain := main_iu306 D (⇑g) (LeanLab.ChenExplicit.primesBelowIn P z) 1 0
  simp only [Nat.zero_mod, zero_ne_one, ite_false] at hmain
  have hL : ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors,
      rosserWeight306 D 0 d * g d = G_iu306 D g 1 0 (LeanLab.ChenExplicit.primesBelowIn P z) := by
    rw [sum_divisors_prod_iu306 _ hSp, G_iu306]
    apply sum_congr rfl
    intro A hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hSp p (mem_powerset.1 hA hp)
    have hpf : (∏ a ∈ A, a).primeFactors = A := Nat.primeFactors_prod hAp
    have hsqA : Squarefree (∏ a ∈ A, a) := by
      refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
        fun p hp => (hAp p hp).squarefree
      simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hAp p hp) (hAp q hq)).mpr hpq
    have hmu : ((ArithmeticFunction.moebius (∏ a ∈ A, a) : ℤ) : ℝ) = (-1) ^ A.card := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime A hAp]
      push_cast
      rw [prod_congr rfl (fun p hp => by
        rw [ArithmeticFunction.moebius_apply_prime (hAp p hp)])]
      simp
    have hgA : g (∏ a ∈ A, a) = ∏ a ∈ A, g a := hg.map_prod_of_prime A hAp
    unfold rosserWeight306
    rw [hpf, hgA]
    by_cases hW : W_iu306 D 1 0 A
    · rw [if_pos ⟨hsqA, fun p hp hpar => by simpa using hW p hp hpar⟩, if_pos hW, hmu]
    · rw [if_neg (fun h => hW (fun p hp hpar => by simpa using h.2 p hp hpar)), if_neg hW,
        zero_mul]
  have hR : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
      ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors.filter (fun d : ℕ =>
        d.primeFactors.card = n ∧ D ≤ (d : ℝ) * (d.minFac : ℝ) ^ 2 ∧
        ∀ p ∈ d.primeFactors, (d.primeFactors.filter (fun q => p ≤ q)).card < n →
          (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = n % 2 →
            ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D),
      g d * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P (d.minFac : ℝ), (1 - g p) =
      T_iu306 D g 1 0 (LeanLab.ChenExplicit.primesBelowIn P z) := by
    rw [sum_congr rfl (fun n _ => sum_filter _ _), sum_comm, sum_divisors_prod_iu306 _ hSp, T_iu306]
    apply sum_congr rfl
    intro A hA
    have hAS := mem_powerset.1 hA
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hSp p (hAS hp)
    have hpf : (∏ a ∈ A, a).primeFactors = A := Nat.primeFactors_prod hAp
    have hgA : g (∏ a ∈ A, a) = ∏ a ∈ A, g a := hg.map_prod_of_prime A hAp
    have hd0 : (∏ a ∈ A, a) ≠ 0 := prod_ne_zero_iff.2 (fun p hp => (hAp p hp).ne_zero)
    simp only [hpf, hgA]
    by_cases hN : A.card ∈ (Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even
    · have hodd : A.card % 2 = 0 := Nat.even_iff.1 (mem_filter.1 hN).2
      have hne : A.Nonempty :=
        card_pos.1 (by have := (mem_Icc.1 (mem_filter.1 hN).1).1; omega)
      have hd1 : (∏ a ∈ A, a) ≠ 1 := by
        intro h; rw [h, Nat.primeFactors_one] at hpf; exact hne.ne_empty hpf.symm
      set m := (∏ a ∈ A, a).minFac with hm
      have hmA : m ∈ A := by
        rw [← hpf]; exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hd1, Nat.minFac_dvd _, hd0⟩
      have hmle : ∀ a ∈ A, m ≤ a := fun a ha =>
        Nat.minFac_le_of_dvd (hAp a ha).two_le (dvd_prod_of_mem _ ha)
      have hfilt : LeanLab.ChenExplicit.primesBelowIn P (m : ℝ) =
          (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun x => ∀ a ∈ A, x < a) := by
        have hmS := hAS hmA
        ext x
        simp only [LeanLab.ChenExplicit.primesBelowIn, mem_filter, mem_range,
          Nat.ceil_natCast] at hmS ⊢
        constructor
        · rintro ⟨hx, hxP⟩; exact ⟨⟨by omega, hxP⟩, fun a ha => lt_of_lt_of_le hx (hmle a ha)⟩
        · rintro ⟨⟨_, hxP⟩, h⟩; exact ⟨h m hmA, hxP⟩
      rw [sum_eq_single_of_mem A.card hN (fun n _ hn => if_neg (fun h => hn h.1.symm)), hfilt]
      have hiff : (A.card = A.card ∧ D ≤ ((∏ a ∈ A, a : ℕ) : ℝ) * (m : ℝ) ^ 2 ∧
          ∀ p ∈ A, (A.filter (fun q => p ≤ q)).card < A.card →
            (A.filter (fun q => p ≤ q)).card % 2 = A.card % 2 →
            ((∏ q ∈ A.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < D) ↔
            Tc_iu306 D 1 0 A := by
        unfold Tc_iu306
        rw [hodd]
        simp only [one_mul, Nat.zero_mod, true_and]
        constructor
        · rintro ⟨hD, h⟩; exact ⟨⟨m, hmA, hmle, hD⟩, h⟩
        · rintro ⟨⟨m', hm'A, hm'le, hD⟩, h⟩
          have : m' = m := le_antisymm (hm'le m hmA) (hmle m' hm'A)
          subst this; exact ⟨hD, h⟩
      by_cases hT : Tc_iu306 D 1 0 A
      · rw [if_pos (hiff.2 hT), if_pos hT]
      · rw [if_neg (fun h => hT (hiff.1 h)), if_neg hT]
    · rw [sum_eq_zero (fun n hn => if_neg (fun h => hN (by rw [h.1]; exact hn))), if_neg]
      rintro ⟨hpar, ⟨m, hmA, -⟩, -⟩
      apply hN
      rw [mem_filter, mem_Icc, Nat.even_iff]
      refine ⟨⟨card_pos.2 ⟨m, hmA⟩, card_le_card hAS⟩, ?_⟩
      simpa using hpar
  rw [hL, hR, hmain]; ring

/-- The functions f_n of BJS displays 15 to 17, Nathanson Chapter 9:
s f_1(s) = 3 - s for s ≤ 3 and 0 for s > 3; for n ≥ 2,
s f_n(s) = the integral over t > s of f_(n-1)(t - 1), display 16, except that for odd n and
s ≤ 3, s f_n(s) = 3 f_n(3) = the integral over t > 3 of f_(n-1)(t - 1), display 17.
The paper uses f_n only for s ≥ 1, n odd, and s ≥ 2, n even; other values are not used.
f_0 is set to 0 and is not used. -/
def bjsF306 : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun s => if s ≤ 3 then (3 - s) / s else 0
  | (n + 2) => fun s =>
      if Odd (n + 2) ∧ s ≤ 3 then (∫ t in Set.Ioi (3 : ℝ), bjsF306 (n + 1) (t - 1)) / s
      else (∫ t in Set.Ioi s, bjsF306 (n + 1) (t - 1)) / s

/-- The values c_n of BJS Table 2, page 7, for 2 ≤ n ≤ 500, with c_1 = 1 as stated after
display 18, and c_n = 0.9607 of Lemma 8 for n > 500. c_0 is set to 1 and is not used. -/
def bjsC306 (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else if n = 2 then 0.33 else if n = 3 then 0.39 else if n = 4 then 0.45
  else if n = 5 then 0.51 else if n = 6 then 0.54 else if n = 7 then 0.57
  else if n = 8 then 0.58 else if n ≤ 10 then 0.61 else if n ≤ 12 then 0.63
  else if n = 13 then 0.64 else if n = 14 then 0.65 else if n ≤ 18 then 0.66
  else if n ≤ 20 then 0.67 else if n ≤ 26 then 0.68 else if n ≤ 34 then 0.69
  else if n ≤ 46 then 0.7 else if n ≤ 82 then 0.71 else if n ≤ 345 then 0.72
  else if n ≤ 500 then 0.73 else 0.9607

/-- The quantity ξ_(s0) of BJS Lemma 11, page 11, for given γ_(s0), κ_(s0), ε,
cp = c_(n-1) ^ (n-2), cc = c_n ^ (n-1) and t = τ_(n-1). -/
def bjsXi306 (γ κ ε cp cc t : ℝ) : ℝ :=
  κ + (γ + κ) * ε + 2 * γ * cp / t + 2 * cc / t

/-- τ_n of BJS display 31, page 11, for a sequence c: τ_1 = 3; for even n ≥ 2,
τ_n = τ_(n-1) max of ξ_2, ξ_2.2, ξ_2.4, ξ_2.6, ξ_2.8, ξ_3; for odd n ≥ 3,
τ_n = τ_(n-1) max of ξ_3 and ξ tilde. γ_(s0) = e ^ (s0 - 2) for s0 ≤ 2.8 and γ_3 = 4 e / 3
by Lemma 9, page 8; κ_2 = 0.9607, κ_2.2 = 0.9557, κ_2.4 = 0.9457, κ_2.6 = 0.9261,
κ_2.8 = 0.8914, κ_3 = 0.8349 and κ tilde = 0.9214 by Lemma 10, pages 8 and 9.
τ_0 is set to 0 and is not used. -/
def bjsTau306 (c : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | (n + 2) =>
      let t := bjsTau306 c ε (n + 1)
      let cp := c (n + 1) ^ n
      let cc := c (n + 2) ^ (n + 1)
      if Even (n + 2) then
        t * max (max (max (bjsXi306 1 0.9607 ε cp cc t) (bjsXi306 (exp 0.2) 0.9557 ε cp cc t))
          (max (bjsXi306 (exp 0.4) 0.9457 ε cp cc t) (bjsXi306 (exp 0.6) 0.9261 ε cp cc t)))
          (max (bjsXi306 (exp 0.8) 0.8914 ε cp cc t) (bjsXi306 (4 * exp 1 / 3) 0.8349 ε cp cc t))
      else
        t * max (bjsXi306 (4 * exp 1 / 3) 0.8349 ε cp cc t)
          (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * cp / t + 2 * (2 + ε) * cc / t)

/-- The functions f_n are nonnegative where the paper uses them, BJS displays 15 to 17:
n odd with s ≥ 1, or n even with s ≥ 2.
PROVED in burst-20261122 S61 by strong induction on n with setIntegral_nonneg; the integrand is evaluated at t - 1 ≥ 1
for odd n - 1 and at t - 1 ≥ 2 for even n - 1. -/
theorem leaf306_fn_nonneg (n : ℕ) (s : ℝ) (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    0 ≤ bjsF306 n s := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    match n, ih, hs with
    | 0, _, _ => simp [bjsF306]
    | 1, _, hs =>
      have hs1 : 1 ≤ s := by rcases hs with h | h <;> [exact h.2; exact absurd h.1 (by decide)]
      simp only [bjsF306]
      split_ifs with h3
      · exact div_nonneg (by linarith) (by linarith)
      · exact le_refl 0
    | m + 2, ih, hs =>
      have hs1 : 1 ≤ s := by rcases hs with h | h <;> linarith [h.2]
      simp only [bjsF306]
      split_ifs with h
      · refine div_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
          (by linarith)
        have ht' : (3 : ℝ) < t := ht
        refine ih (m + 1) (by omega) (t - 1) (Or.inr ⟨?_, by linarith⟩)
        rcases Nat.even_or_odd (m + 1) with he | ho
        · exact he
        · exact absurd h.1 (by rw [Nat.not_odd_iff_even]; exact ho.add_one)
      · refine div_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
          (by linarith)
        have ht' : s < t := ht
        rcases Nat.even_or_odd (m + 2) with he | ho
        · have hs2 : 2 ≤ s := by
            rcases hs with h' | h'
            · exact absurd h'.1 (by rw [Nat.not_odd_iff_even]; exact he)
            · exact h'.2
          refine ih (m + 1) (by omega) (t - 1) (Or.inl ⟨?_, by linarith⟩)
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact he'.add_one)
          · exact ho'
        · have hs3 : 3 < s := by
            by_contra hc; exact h ⟨ho, by linarith⟩
          refine ih (m + 1) (by omega) (t - 1) (Or.inr ⟨?_, by linarith⟩)
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact he'
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact ho'.add_one)

/-- LEAF: BJS display 13, Nathanson Theorem 9.4: for s ≥ 1, F(s) = 1 + the sum of f_n(s)
over odd n, for the solution F, f of display 8.
Class HARD: the delay differential equations against the integral recursion 15 to 17. -/
theorem leaf306_display13 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 1 ≤ s) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F s - 1) := by
  sorry

/-- LEAF: BJS display 14, Nathanson Theorem 9.4: for s ≥ 2, f(s) = 1 - the sum of f_n(s)
over even n ≥ 2, for the solution F, f of display 8. The term n = 0 is f_0 = 0.
Class HARD: as display 13. -/
theorem leaf306_display14 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (s : ℝ) (hs : 2 ≤ s) :
    HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f s) := by
  sorry

/-- h(s) of display 7 is nonnegative for s ≥ 0. -/
theorem hSieve_nonneg306 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ LeanLab.ChenExplicit.hSieve s := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs
  · exact (exp_pos _).le
  · exact (exp_pos _).le
  · exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hs)) (exp_pos _).le

/-- c_n = 0.9607 for n > 500, the value of Lemma 8 in bjsC306. -/
theorem bjsC306_large (n : ℕ) (hn : 500 < n) : bjsC306 n = 0.9607 := by
  unfold bjsC306
  repeat rw [if_neg (show ¬ _ by omega)]

/-- Display 18 for n = 1 with c_1 = 1, as stated after display 18 on page 6. -/
theorem display18_one306 (s : ℝ) (hs : 1 ≤ s) :
    bjsF306 1 s ≤ 2 * exp 2 * bjsC306 1 ^ (1 - 1) * LeanLab.ChenExplicit.hSieve s := by
  rw [Nat.sub_self, pow_zero, mul_one]
  have hspos : 0 < s := by linarith
  have hh := hSieve_nonneg306 s hspos.le
  simp only [bjsF306]
  by_cases h3 : s ≤ 3
  · rw [if_pos h3]
    unfold LeanLab.ChenExplicit.hSieve
    by_cases h2 : s ≤ 2
    · rw [if_pos h2, mul_assoc, ← exp_add]; norm_num
      rw [div_le_iff₀ hspos]; linarith
    · rw [if_neg h2, if_pos h3, mul_assoc, ← exp_add]
      have he : exp (-1) ≤ exp (2 + -s) := exp_le_exp.mpr (by linarith)
      have he1 : (0.36 : ℝ) < exp (-1) := lt_trans (by norm_num) Real.exp_neg_one_gt_d9
      rw [div_le_iff₀ hspos]
      nlinarith
  · rw [if_neg h3]
    exact mul_nonneg (by positivity) hh

/-- LEAF: BJS Lemma 7, page 7: display 18 holds with c_n of Table 2 for 2 ≤ n ≤ 500,
that is f_n(s) ≤ 2 e ^ 2 c_n ^ (n - 1) h(s) for n odd and s ≥ 1 or n even and s ≥ 2.
Class HARD: the Riemann sum computation of Section 2.2, display 21, with step 1 / 1000. -/
theorem leaf306_lemma7 (n : ℕ) (hn2 : 2 ≤ n) (hn500 : n ≤ 500) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    bjsF306 n s ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  sorry

/-- LEAF: BJS Lemma 8, page 7, Nathanson Lemma 9.7: display 18 holds with c_n = 0.9607 for
every n ≥ 2. Class HARD: Nathanson's induction with H(s) ≤ α s h(s), Remark 1 on page 10. -/
theorem leaf306_lemma8 (n : ℕ) (hn2 : 2 ≤ n) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    bjsF306 n s ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  sorry

/-- BJS Lemmas 7 and 8, pages 6 and 7: display 18,
f_n(s) ≤ 2 e ^ 2 c_n ^ (n - 1) h(s) for n odd and s ≥ 1 or n even and s ≥ 2,
with c_n of Table 2 for n ≤ 500, c_1 = 1, and c_n = 0.9607 beyond, Nathanson Lemma 9.7.
Proved in burst-20261122 S61 from leaf306_lemma7, leaf306_lemma8 and the case n = 1. -/
theorem leaf306_display18 (n : ℕ) (hn : 1 ≤ n) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    bjsF306 n s ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    exact display18_one306 s (by rcases hs with h | h <;> linarith [h.2])
  · rcases Nat.lt_or_ge 500 n with hbig | hsmall
    · rw [bjsC306_large n hbig]
      exact leaf306_lemma8 n h2 s hs
    · exact leaf306_lemma7 n h2 hsmall s hs

/-- LEAF: BJS Lemma 11, page 11, the case n = 1: for s ≥ 1, T_1(D, z) ≤ V(z) (f_1(s) + 3 ε e ^ 2 h(s)).
For s > 3 the sum is empty, Nathanson Lemma 9.3 with β = 2; for 1 ≤ s ≤ 3 it telescopes to
V(D ^ (1/3)) - V(z), Nathanson display 9.13, and display 29 at u = D ^ (1/3) gives
(3 / s - 1) + 3 (K - 1) / s. This case does not use γ or κ.
Class MEDIUM: telescoping g(p) V(p) = V(p) - V(p') over the primes of P in [D ^ (1/3), z). -/
theorem leaf306_lemma11_base (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hs : 1 ≤ log D / log z) :
    rosserT306 P g z D 1 ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 1 (log D / log z) +
          ε * 3 * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- LEAF: BJS Lemma 11, pages 11 to 13, the cases n ≥ 2: displays 34 to 39 through Nathanson
Lemma 9.8 and Theorem 9.5, with Lemmas 9 and 10.
Class HARD. QUESTION: bjsTau306 uses γ_(s0) = e ^ (s0 - 2) as printed in Lemma 9, while display 22
needs e ^ (s0 - 1.8); and the induction applies display 29 at z' = p below z, which the
one parameter form of display 29 does not state. See the repair note of burst-20261122. -/
theorem leaf306_lemma11_step (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (h18 : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) →
      bjsF306 n s ≤ 2 * exp 2 * c n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s)
    (n : ℕ) (hn : 2 ≤ n) (D : ℝ)
    (hs : (Odd n ∧ 1 ≤ log D / log z) ∨ (Even n ∧ 2 ≤ log D / log z)) :
    rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n (log D / log z) +
          ε * bjsTau306 c ε n * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- BJS Lemma 11, pages 10 to 13: under displays 29 and 30 with 1 < K < 1 + ε and
any positive c_n satisfying display 18, T_n(D, z) ≤ V(z) (f_n(s) + ε τ_n e ^ 2 h(s)) for
n ≥ 1, with s ≥ 1 for odd n and s ≥ 2 for even n. The paper's strict inequality is weakened.
Proved in burst-20261122 S61 from leaf306_lemma11_base and leaf306_lemma11_step. -/
theorem leaf306_lemma11 (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    (h18 : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) →
      bjsF306 n s ≤ 2 * exp 2 * c n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s)
    (n : ℕ) (hn : 1 ≤ n) (D : ℝ)
    (hs : (Odd n ∧ 1 ≤ log D / log z) ∨ (Even n ∧ 2 ≤ log D / log z)) :
    rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n (log D / log z) +
          ε * bjsTau306 c ε n * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hs1 : 1 ≤ log D / log z := by
      rcases hs with h | h
      · exact h.2
      · exact absurd h.1 (by decide)
    have := leaf306_lemma11_base P hP z hz g hg hgp ε hε K hK1 hKε h29 D hs1
    simpa [bjsTau306] using this
  · exact leaf306_lemma11_step P hP z hz g hg hgp ε hε K hK1 hKε h29 c hc h18 n h2 D hs

/-- V(z) is nonnegative when 0 ≤ g(p) < 1 on P. -/
theorem V_nonneg306 (P : Set ℕ) (z : ℝ) (g : ArithmeticFunction ℝ)
    (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    0 ≤ ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) := by
  classical
  refine Finset.prod_nonneg fun p hp => ?_
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter] at hp
  linarith [(hgp p hp.2).2]

/-- The values c_n of Table 2 are positive. -/
theorem bjsC306_pos (n : ℕ) : 0 < bjsC306 n := by
  unfold bjsC306
  positivity

/-- LEAF: BJS Lemma 11 summed over odd n with display 13, then Lemma 14 and Table 1,
pages 10 to 16, the upper half of Proposition 13: under displays 29 and 30 with s ≥ 1,
the sum of T_n(D, z) over odd n is at most V(z) (F(s) - 1 + ε C_1 e ^ 2 h(s)).
Table 1 is read for every ε ≤ 1 / k, as LinearSieve.lean records.
Class HARD. The τ route, tau_T_odd_bound306, gives this only with C at least the
sum of τ_n of display 31, which as printed exceeds Table 1; see the repair note of burst-20261122. -/
theorem leaf306_T_odd_bound (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- The τ route of BJS Lemma 11 and Proposition 13, pages 10 to 14, upper half: under
displays 29 and 30, with any bound C for the partial sums of τ_n over odd n, the sum of
T_n(D, z) over odd n is at most V(z) times the main term plus ε C e ^ 2 h(s).
CONDITIONAL ON leaf306_lemma11, leaf306_display13 and leaf306_display18. -/
theorem tau_T_odd_bound306 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (C : ℝ) (htau : ∀ N : ℕ,
      ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsTau306 bjsC306 ε n ≤ C)
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * C * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz, one_mul]; exact log_le_log (by linarith) hD
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (Or.inl ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s ≤ F s - 1 := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display13 F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inl ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := htau (LeanLab.ChenExplicit.primesBelowIn P z).card
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (F s - 1) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * C :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring


/-- LEAF: BJS Lemma 11 summed over even n with display 14, then Lemma 14 and Table 1,
pages 10 to 16, the lower half of Proposition 13: under displays 29 and 30 with s ≥ 2,
the sum of T_n(D, z) over even n is at most V(z) (1 - f(s) + ε C_2 e ^ 2 h(s)).
Class HARD. The τ route, tau_T_even_bound306, gives this only with C at least the
sum of τ_n of display 31, which as printed exceeds Table 1; see the repair note of burst-20261122. -/
theorem leaf306_T_even_bound (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ^ 2 ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (1 - f (log D / log z) +
          ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- The τ route of BJS Lemma 11 and Proposition 13, pages 10 to 14, lower half: under
displays 29 and 30, with any bound C for the partial sums of τ_n over even n, the sum of
T_n(D, z) over even n is at most V(z) times the main term plus ε C e ^ 2 h(s).
CONDITIONAL ON leaf306_lemma11, leaf306_display14 and leaf306_display18. -/
theorem tau_T_even_bound306 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (ε : ℝ) (hε : 0 < ε)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (C : ℝ) (htau : ∀ N : ℕ,
      ∑ n ∈ (Finset.Icc 1 N).filter Even, bjsTau306 bjsC306 ε n ≤ C)
    (D : ℝ) (hD : z ^ 2 ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (1 - f (log D / log z) +
          ε * C * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  classical
  set s := log D / log z with hsdef
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs1 : 2 ≤ s := by
    rw [hsdef, le_div_iff₀ hlogz]
    have h2 : log (z ^ 2) ≤ log D := log_le_log (by positivity) hD
    rw [Real.log_pow] at h2; push_cast at h2; linarith
  have hV0 := V_nonneg306 P z g hgp
  have hh0 : 0 ≤ LeanLab.ChenExplicit.hSieve s := hSieve_nonneg306 s (by linarith)
  have hcpos : ∀ n, 0 < bjsC306 n := bjsC306_pos
  have hT : ∀ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact leaf306_lemma11 P hP z hz g hg hgp ε hε K hK1 hKε h29 bjsC306 hcpos
      (fun m hm s' hs' => leaf306_display18 m hm s' hs') n hn.1.1 D (Or.inr ⟨hn.2, hs1⟩)
  have hf : ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s ≤ 1 - f s := by
    rw [Finset.sum_filter]
    refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display14 F f hF s hs1)
    split_ifs with ho
    · exact leaf306_fn_nonneg n s (Or.inr ⟨ho, hs1⟩)
    · exact le_refl 0
  have hτ := htau (LeanLab.ChenExplicit.primesBelowIn P z).card
  have hco : 0 ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
      LeanLab.ChenExplicit.hSieve s :=
    mul_nonneg (mul_nonneg (mul_nonneg hV0 hε.le) (exp_pos _).le) hh0
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (bjsF306 n s + ε * bjsTau306 bjsC306 ε n * exp 2 * LeanLab.ChenExplicit.hSieve s) :=
        Finset.sum_le_sum hT
    _ = (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsF306 n s +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Even, bjsTau306 bjsC306 ε n := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * (1 - f s) +
        ((∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) * ε * exp 2 *
          LeanLab.ChenExplicit.hSieve s) * C :=
        add_le_add (mul_le_mul_of_nonneg_left hf hV0) (mul_le_mul_of_nonneg_left hτ hco)
    _ = _ := by ring


/-- The constant K of BJS displays 29 and 30 from the strict display 4. With finitely
many primes below z, the ratio of the product to log z / log u has supremum below 1 + ε,
so one K with 1 < K < 1 + ε serves every u. The paper uses this step silently when it
applies Lemma 11 in the proof of Theorem 6, page 16.
PROVED in burst-20261122 S61: the product is a step function of u, constant between consecutive primes. -/
theorem leaf306_uniform_K (P : Set ℕ) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (ε : ℝ) (hε : 0 < ε)
    (h4 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ < (1 + ε) * (log z / log u)) :
    ∃ K : ℝ, 1 < K ∧ K < 1 + ε ∧ ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u) := by
  classical
  set S := LeanLab.ChenExplicit.primesBelowIn P z with hS
  have hmemS : ∀ p ∈ S, p ∈ P ∧ (p : ℝ) < z := by
    intro p hp
    simp only [hS, LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range,
      Nat.lt_ceil] at hp
    exact ⟨hp.2, hp.1⟩
  set Pr : ℝ → ℝ := fun u => ∏ p ∈ S.filter (fun p : ℕ => u ≤ (p : ℝ)), (1 - g p)⁻¹ with hPr
  have hlogz : 0 < log z := Real.log_pos (by linarith)
  set T := S.filter (fun p : ℕ => 1 < (p : ℝ)) with hT
  set a : ℕ → ℝ := fun p => Pr p * log p / log z with ha
  set M := T.fold max 1 a with hM
  have hM1 : 1 ≤ M := by
    rw [hM, Finset.le_fold_max]; left; exact le_refl _
  have hMlt : M < 1 + ε := by
    rw [hM, Finset.fold_max_lt]
    refine ⟨by linarith, ?_⟩
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    have hp1 := hp.2
    have hpz := (hmemS p hp.1).2
    have h := h4 p hp1 hpz
    have hlp : 0 < log (p : ℝ) := Real.log_pos hp1
    show Pr p * log p / log z < 1 + ε
    rw [div_lt_iff₀ hlogz]
    have := mul_lt_mul_of_pos_right h hlp
    calc Pr p * log p < (1 + ε) * (log z / log p) * log p := this
      _ = (1 + ε) * log z := by field_simp
  refine ⟨(M + 1 + ε) / 2, by linarith, by linarith, ?_⟩
  intro u hu1 huz
  have hlu : 0 < log u := Real.log_pos hu1
  have hluz : log u < log z := Real.log_lt_log (by linarith) huz
  have hratio : 1 < log z / log u := by rw [one_lt_div hlu]; exact hluz
  show Pr u ≤ _
  by_cases hF : (S.filter (fun p : ℕ => u ≤ (p : ℝ))).Nonempty
  · set p0 := (S.filter (fun p : ℕ => u ≤ (p : ℝ))).min' hF with hp0
    have hp0mem := Finset.min'_mem _ hF
    rw [← hp0, Finset.mem_filter] at hp0mem
    have hfeq : S.filter (fun p : ℕ => u ≤ (p : ℝ)) = S.filter (fun p : ℕ => (p0 : ℝ) ≤ (p : ℝ)) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : p0 ≤ p := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨h1, h2⟩)
        exact_mod_cast this
      · rintro ⟨h1, h2⟩
        exact ⟨h1, le_trans hp0mem.2 h2⟩
    have hPreq : Pr u = Pr p0 := by
      simp only [hPr]; rw [hfeq]
    have hp01 : 1 < (p0 : ℝ) := lt_of_lt_of_le hu1 hp0mem.2
    have hp0T : p0 ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨hp0mem.1, hp01⟩
    have hap0 : a p0 ≤ M := by
      rw [hM, Finset.le_fold_max]; right; exact ⟨p0, hp0T, le_refl _⟩
    have hlp0 : 0 < log (p0 : ℝ) := Real.log_pos hp01
    have hlup : log u ≤ log (p0 : ℝ) := Real.log_le_log (by linarith) hp0mem.2
    have hPr0 : Pr p0 ≤ M * (log z / log p0) := by
      have : Pr p0 * log p0 / log z ≤ M := hap0
      rw [div_le_iff₀ hlogz] at this
      rw [mul_div_assoc', le_div_iff₀ hlp0]
      linarith
    have h2 : log z / log p0 ≤ log z / log u :=
      div_le_div_of_nonneg_left hlogz.le hlu hlup
    rw [hPreq]
    calc Pr p0 ≤ M * (log z / log p0) := hPr0
      _ ≤ M * (log z / log u) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ (M + 1 + ε) / 2 * (log z / log u) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    have : Pr u = 1 := by simp only [hPr]; rw [hF, Finset.prod_empty]
    rw [this]
    have hK1 : 1 < (M + 1 + ε) / 2 := by linarith
    nlinarith

/-! Helpers for leaf306_reduction_upper, written by a workflow subagent, burst-20261122 S61. -/

theorem sum_moebius_ru306 (k : ℕ) :
    ∑ e ∈ k.divisors, (ArithmeticFunction.moebius e : ℝ) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F k)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h

theorem divisors_filter_dvd_ru306 (A n : ℕ) (hA : A ≠ 0) :
    A.divisors.filter (· ∣ n) = (Nat.gcd n A).divisors := by
  ext e
  have : Nat.gcd n A ≠ 0 := by
    intro h; exact hA (Nat.eq_zero_of_gcd_eq_zero_right h)
  simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  tauto

theorem pointwise_ru306 (PQ PP' n : ℕ) (hPQ : PQ ≠ 0) (hPP' : PP' ≠ 0)
    (hcop : Nat.Coprime PQ PP') (lam : ℕ → ℝ)
    (hsieve : ∀ m ∈ PP'.divisors, (if m = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ m.divisors, lam d) :
    (if Nat.Coprime n (PQ * PP') then (1:ℝ) else 0) ≤
      ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
        (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then 1 else 0) := by
  have hsplit : ∀ e ∈ PQ.divisors, ∀ d ∈ PP'.divisors,
      (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then 1 else 0) =
        ((if e ∣ n then (ArithmeticFunction.moebius e : ℝ) else 0)) *
          (if d ∣ n then lam d else 0) := by
    intro e he d hd
    have hde : Nat.Coprime d e :=
      (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he)).coprime_dvd_right
        (Nat.dvd_of_mem_divisors hd) |>.symm
    by_cases h1 : e ∣ n <;> by_cases h2 : d ∣ n
    · rw [if_pos (hde.mul_dvd_of_dvd_of_dvd h2 h1)]; simp [h1, h2]
    · rw [if_neg (fun h => h2 ((Nat.dvd_mul_right d e).trans h))]; simp [h2]
    · rw [if_neg (fun h => h1 ((Nat.dvd_mul_left e d).trans h))]; simp [h1]
    · rw [if_neg (fun h => h1 ((Nat.dvd_mul_left e d).trans h))]; simp [h1]
  rw [sum_congr rfl (fun e he => sum_congr rfl (hsplit e he)), ← sum_mul_sum,
    ← sum_filter, ← sum_filter, divisors_filter_dvd_ru306 _ _ hPQ,
    divisors_filter_dvd_ru306 _ _ hPP', sum_moebius_ru306]
  have hm : Nat.gcd n PP' ∈ PP'.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hPP'⟩
  have := hsieve _ hm
  by_cases hk : Nat.gcd n PQ = 1
  · rw [if_pos hk, one_mul]
    by_cases hm1 : Nat.gcd n PP' = 1
    · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hk, hm1⟩)]; rw [if_pos hm1] at this; exact this
    · rw [if_neg (fun h => hm1 (Nat.coprime_mul_iff_right.mp h).2)]; rw [if_neg hm1] at this
      exact this
  · rw [if_neg hk, if_neg (fun h => hk (Nat.coprime_mul_iff_right.mp h).1)]; simp

open Classical in
/-- Nathanson Theorem 9.7, upper half, the step the proof of BJS Theorem 6 on page 16
takes over unchanged, with the set Q of display 4 and the level Q D of display 10.
Sieve n coprime to the primes of Q below z by Mobius inversion and the primes of P \ Q by
weights lam with |lam| ≤ 1, level D and the upper sieve property, whose main terms
G_n(lam) are at most c V_n(z) for P \ Q. Then S(A, P, z) ≤ c X_A + R.
PROVED in burst-20261122 S61: interchange of finite sums and the injection (d, e) to d e. -/
theorem leaf306_reduction_upper (supp : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ℕ → ArithmeticFunction ℝ) (hg : ∀ n, (g n).IsMultiplicative)
    (hgp : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q ∈ P) (D : ℝ) (hD : 0 < D)
    (lam : ℕ → ℝ) (c : ℝ) (hlam : ∀ d, |lam d| ≤ 1)
    (hsupp : ∀ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, lam d ≠ 0 → (d : ℝ) < D)
    (hsieve : ∀ m ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, (if m = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ m.divisors, lam d)
    (hmain : ∀ n, ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p | p ∈ P ∧ p ∉ Q} z, p).divisors, lam d * g n d ≤
      c * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z, (1 - g n p)) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    let S : ℝ := ∑ n ∈ supp, if Nat.Coprime n PP then a n else 0
    let XA : ℝ := ∑ n ∈ supp, a n * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g n p)
    let r : ℕ → ℝ := fun d =>
      (∑ n ∈ supp, if d ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n d
    let R : ℝ := ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), |r d|
    S ≤ c * XA + R := by
  intro PP S XA r R
  set T := LeanLab.ChenExplicit.primesBelowIn P z with hT
  set T' := LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z with hT'
  set TQ := LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∈ Q} z with hTQ
  have hT'eq : T' = T.filter (· ∉ Q) := by
    ext p
    simp only [hT, hT', LeanLab.ChenExplicit.primesBelowIn, mem_filter, mem_range,
      Set.mem_setOf_eq]
    tauto
  have hTQeq : TQ = T.filter (· ∈ Q) := by
    ext p
    simp only [hT, hTQ, LeanLab.ChenExplicit.primesBelowIn, mem_filter, mem_range,
      Set.mem_setOf_eq]
    tauto
  have hPQP : ∀ p ∈ ({p | p ∈ P ∧ p ∈ Q} : Set ℕ), p.Prime := fun p hp => hP p hp.1
  have hP'P : ∀ p ∈ ({p | p ∈ P ∧ p ∉ Q} : Set ℕ), p.Prime := fun p hp => hP p hp.1
  have hTQmem : ∀ p ∈ TQ, p ∈ P ∧ p ∈ Q := by
    intro p hp; rw [hTQeq, mem_filter] at hp
    exact ⟨(mem_primesBelowIn306 hP hp.1).1 |> fun _ => by
      simp only [hT, LeanLab.ChenExplicit.primesBelowIn, mem_filter] at hp; exact hp.1.2, hp.2⟩
  have hT'mem : ∀ p ∈ T', p ∈ P ∧ p ∉ Q := by
    intro p hp; rw [hT'eq, mem_filter] at hp
    exact ⟨by simp only [hT, LeanLab.ChenExplicit.primesBelowIn, mem_filter] at hp; exact hp.1.2,
      hp.2⟩
  set PQ := ∏ p ∈ TQ, p with hPQ
  set PP' := ∏ p ∈ T', p with hPP'
  have hPPeq : (∏ p ∈ T, p) = PQ * PP' := by
    rw [hPQ, hPP', hTQeq, hT'eq, prod_filter_mul_prod_filter_not]
  have hprodT : ∀ n, ∏ p ∈ T, (1 - g n p) = (∏ p ∈ TQ, (1 - g n p)) * ∏ p ∈ T', (1 - g n p) := by
    intro n; rw [hTQeq, hT'eq, prod_filter_mul_prod_filter_not]
  have hprTQ : ∀ p ∈ TQ, p.Prime := fun p hp => (mem_primesBelowIn306 hPQP hp).1
  have hprT' : ∀ p ∈ T', p.Prime := fun p hp => (mem_primesBelowIn306 hP'P hp).1
  have hPQ0 : PQ ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprTQ p hp).ne_zero
  have hPP'0 : PP' ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprT' p hp).ne_zero
  have hcop : Nat.Coprime PQ PP' := by
    apply Nat.Coprime.prod_left; intro p hp
    apply Nat.Coprime.prod_right; intro q hq
    refine (Nat.coprime_primes (hprTQ p hp) (hprT' q hq)).mpr ?_
    rintro rfl; exact (hT'mem p hq).2 (hTQmem p hp).2
  have hde : ∀ e ∈ PQ.divisors, ∀ d ∈ PP'.divisors, Nat.Coprime d e := fun e he d hd =>
    ((hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he)).coprime_dvd_right
      (Nat.dvd_of_mem_divisors hd)).symm
  have hsqPQ : Squarefree PQ := squarefree_primesBelowIn306 hPQP z
  have hmuG : ∀ n, ∑ e ∈ PQ.divisors, (ArithmeticFunction.moebius e : ℝ) * g n e =
      ∏ p ∈ TQ, (1 - g n p) := by
    intro n
    rw [← (hg n).prodPrimeFactors_one_sub_of_squarefree _ hsqPQ, hPQ, Nat.primeFactors_prod hprTQ]
  have hr : ∀ m, (∑ n ∈ supp, if m ∣ n then a n else 0) = r m + ∑ n ∈ supp, a n * g n m := by
    intro m; show _ = ((∑ n ∈ supp, if m ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n m) + _
    ring
  -- main term
  have hMain : ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
      (ArithmeticFunction.moebius e : ℝ) * lam d * ∑ n ∈ supp, a n * g n (d * e) ≤ c * XA := by
    calc _ = ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors, ∑ n ∈ supp,
          a n * (((ArithmeticFunction.moebius e : ℝ) * g n e) * (lam d * g n d)) :=
          sum_congr rfl fun e he => sum_congr rfl fun d hd => by
            rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
            rw [(hg n).map_mul_of_coprime (hde e he d hd)]; ring
      _ = ∑ e ∈ PQ.divisors, ∑ n ∈ supp, ∑ d ∈ PP'.divisors,
          a n * (((ArithmeticFunction.moebius e : ℝ) * g n e) * (lam d * g n d)) :=
          sum_congr rfl fun e _ => Finset.sum_comm
      _ = ∑ n ∈ supp, ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
          a n * (((ArithmeticFunction.moebius e : ℝ) * g n e) * (lam d * g n d)) :=
          Finset.sum_comm
      _ = ∑ n ∈ supp, a n * ((∑ e ∈ PQ.divisors, (ArithmeticFunction.moebius e : ℝ) * g n e) *
          ∑ d ∈ PP'.divisors, lam d * g n d) :=
          sum_congr rfl fun n _ => by
            rw [sum_mul_sum, mul_sum]; exact sum_congr rfl fun e _ => by rw [mul_sum]
      _ = ∑ n ∈ supp, a n * ((∏ p ∈ TQ, (1 - g n p)) * ∑ d ∈ PP'.divisors, lam d * g n d) :=
          sum_congr rfl fun n _ => by rw [hmuG n]
      _ ≤ ∑ n ∈ supp, a n * ((∏ p ∈ TQ, (1 - g n p)) * (c * ∏ p ∈ T', (1 - g n p))) :=
          sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hmain n) (prod_nonneg fun p hp =>
              sub_nonneg.mpr (hgp n p (hTQmem p hp).1).2.le)) (ha n)
      _ = c * XA := by
          show _ = c * ∑ n ∈ supp, a n * ∏ p ∈ T, (1 - g n p)
          rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
          rw [hprodT]; ring
  -- remainder
  have hmu1 : ∀ e, |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := fun e => by
    have := ArithmeticFunction.abs_moebius_le_one (n := e)
    rw [← Int.cast_abs]; exact_mod_cast this
  have hQprod0 : (∏ q ∈ Q, q) ≠ 0 := prod_ne_zero_iff.mpr fun q hq => (hP q (hQ q hq)).ne_zero
  have hPQle : PQ ≤ ∏ q ∈ Q, q := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hQprod0)
    apply prod_dvd_prod_of_subset
    intro p hp; exact (hTQmem p hp).2
  have hRem : ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
      (ArithmeticFunction.moebius e : ℝ) * lam d * r (d * e) ≤ R := by
    calc _ ≤ ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors, (if lam d ≠ 0 then |r (d * e)| else 0) :=
          sum_le_sum fun e _ => sum_le_sum fun d _ => by
            split_ifs with h
            · calc _ ≤ |(ArithmeticFunction.moebius e : ℝ) * lam d * r (d * e)| := le_abs_self _
                _ = |(ArithmeticFunction.moebius e : ℝ)| * |lam d| * |r (d * e)| := by
                  rw [abs_mul, abs_mul]
                _ ≤ 1 * 1 * |r (d * e)| := by
                  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                  exact mul_le_mul (hmu1 e) (hlam d) (abs_nonneg _) zero_le_one
                _ = _ := by ring
            · simp only [ne_eq, not_not] at h; simp [h]
      _ = ∑ x ∈ (PQ.divisors ×ˢ PP'.divisors).filter (fun x => lam x.2 ≠ 0),
          |r (x.2 * x.1)| := by
          rw [sum_filter, sum_product]
      _ = ∑ m ∈ ((PQ.divisors ×ˢ PP'.divisors).filter (fun x => lam x.2 ≠ 0)).image
          (fun x => x.2 * x.1), |r m| := by
          rw [sum_image]
          intro x hx y hy hxy
          simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hx hy
          have hx1 : x.1 ∣ PQ := Nat.dvd_of_mem_divisors hx.1.1
          have hy1 : y.1 ∣ PQ := Nat.dvd_of_mem_divisors hy.1.1
          have hcx : Nat.Coprime x.2 PQ :=
            hcop.symm.coprime_dvd_left (Nat.dvd_of_mem_divisors hx.1.2)
          have hcy : Nat.Coprime y.2 PQ :=
            hcop.symm.coprime_dvd_left (Nat.dvd_of_mem_divisors hy.1.2)
          have h1 : x.1 = y.1 := by
            have e1 := Nat.Coprime.gcd_mul_left_cancel x.1 hcx
            have e2 := Nat.Coprime.gcd_mul_left_cancel y.1 hcy
            simp only at hxy
            rw [Nat.gcd_eq_left hx1] at e1
            rw [Nat.gcd_eq_left hy1] at e2
            rw [← e1, ← e2, hxy]
          have hpos : 0 < x.1 := Nat.pos_of_mem_divisors hx.1.1
          have h2 : x.2 = y.2 := by
            simp only at hxy
            rw [← h1] at hxy
            exact Nat.eq_of_mul_eq_mul_right hpos hxy
          exact Prod.ext h1 h2
      _ ≤ R := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
          intro m hm
          simp only [mem_image, mem_filter, mem_product] at hm
          obtain ⟨⟨e, d⟩, ⟨⟨he, hd⟩, hl⟩, rfl⟩ := hm
          simp only at he hd hl ⊢
          rw [mem_filter, Nat.mem_divisors]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · show d * e ∣ ∏ p ∈ T, p
            rw [hPPeq, mul_comm PQ]
            exact Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
          · show ∏ p ∈ T, p ≠ 0
            rw [hPPeq]; exact Nat.mul_ne_zero hPQ0 hPP'0
          · have hdD := hsupp d hd hl
            have he0 : (0:ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
            have hele : (e:ℝ) ≤ ∏ q ∈ Q, (q:ℝ) := by
              have := (Nat.le_of_dvd (Nat.pos_of_ne_zero hPQ0)
                (Nat.dvd_of_mem_divisors he)).trans hPQle
              have h2 : ((e:ℕ):ℝ) ≤ ((∏ q ∈ Q, q : ℕ):ℝ) := by exact_mod_cast this
              rwa [Nat.cast_prod] at h2
            push_cast
            calc (d:ℝ) * e < D * e := mul_lt_mul_of_pos_right hdD he0
              _ ≤ D * ∏ q ∈ Q, (q:ℝ) := mul_le_mul_of_nonneg_left hele hD.le
              _ = _ := by ring
  -- assemble
  calc S ≤ ∑ n ∈ supp, a n * ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
        (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then 1 else 0) := by
        apply sum_le_sum; intro n _
        have h := pointwise_ru306 PQ PP' n hPQ0 hPP'0 hcop lam hsieve
        by_cases hc : Nat.Coprime n (PQ * PP')
        · rw [if_pos (show Nat.Coprime n PP by show Nat.Coprime n (∏ p ∈ T, p); rw [hPPeq]; exact hc)]
          rw [if_pos hc] at h
          simpa using mul_le_mul_of_nonneg_left h (ha n)
        · rw [if_neg (show ¬ Nat.Coprime n PP by
            show ¬ Nat.Coprime n (∏ p ∈ T, p); rw [hPPeq]; exact hc)]
          rw [if_neg hc] at h
          exact mul_nonneg (ha n) h
    _ = ∑ n ∈ supp, ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
        (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then a n else 0) :=
        sum_congr rfl fun n _ => by
          rw [mul_sum]; refine sum_congr rfl fun e _ => ?_
          rw [mul_sum]; refine sum_congr rfl fun d _ => ?_
          split_ifs <;> ring
    _ = ∑ e ∈ PQ.divisors, ∑ n ∈ supp, ∑ d ∈ PP'.divisors,
        (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then a n else 0) :=
        Finset.sum_comm
    _ = ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors, ∑ n ∈ supp,
        (ArithmeticFunction.moebius e : ℝ) * lam d * (if d * e ∣ n then a n else 0) :=
        sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
        ((ArithmeticFunction.moebius e : ℝ) * lam d * r (d * e) +
          (ArithmeticFunction.moebius e : ℝ) * lam d * ∑ n ∈ supp, a n * g n (d * e)) :=
        sum_congr rfl fun e _ => sum_congr rfl fun d _ => by
          rw [← mul_sum, hr]; ring
    _ = (∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
          (ArithmeticFunction.moebius e : ℝ) * lam d * r (d * e)) +
        ∑ e ∈ PQ.divisors, ∑ d ∈ PP'.divisors,
          (ArithmeticFunction.moebius e : ℝ) * lam d * ∑ n ∈ supp, a n * g n (d * e) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun e _ => sum_add_distrib
    _ ≤ R + c * XA := add_le_add hRem hMain
    _ = c * XA + R := add_comm _ _

/-! Helpers for leaf306_reduction_lower, written by a workflow subagent, burst-20261122 S61. -/

theorem sum_moebius_rl306 (m : ℕ) :
    ∑ e ∈ m.divisors, (ArithmeticFunction.moebius e : ℝ) = if m = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)
  have : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta) m =
      (1 : ArithmeticFunction ℝ) m := by rw [h]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
  rw [← this]
  simp [ArithmeticFunction.intCoe_apply]

theorem sum_dvd_gcd_rl306 (N n : ℕ) (hN : N ≠ 0) (f : ℕ → ℝ) :
    ∑ d ∈ N.divisors, f d * (if d ∣ n then (1 : ℝ) else 0) =
      ∑ d ∈ (Nat.gcd n N).divisors, f d := by
  have hg : Nat.gcd n N ≠ 0 := Nat.gcd_ne_zero_right hN
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  exact ⟨fun h => ⟨⟨h.2, h.1.1⟩, hg⟩, fun h => ⟨⟨h.1.2, hN⟩, h.1.1⟩⟩

open Classical in
/-- Nathanson Theorem 9.7, lower half, as in the upper half with the lower sieve
property and main terms G_n(lam) at least c V_n(z) for P \ Q. Then c X_A - R ≤ S(A, P, z).
PROVED in burst-20261122 S61 by the same interchange of sums. -/
theorem leaf306_reduction_lower (supp : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ℕ → ArithmeticFunction ℝ) (hg : ∀ n, (g n).IsMultiplicative)
    (hgp : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q ∈ P) (D : ℝ) (hD : 0 < D)
    (lam : ℕ → ℝ) (c : ℝ) (hlam : ∀ d, |lam d| ≤ 1)
    (hsupp : ∀ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, lam d ≠ 0 → (d : ℝ) < D)
    (hsieve : ∀ m ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
      p).divisors, ∑ d ∈ m.divisors, lam d ≤ (if m = 1 then (1 : ℝ) else 0))
    (hmain : ∀ n, c * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z,
        (1 - g n p) ≤
      ∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p | p ∈ P ∧ p ∉ Q} z, p).divisors, lam d * g n d) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    let S : ℝ := ∑ n ∈ supp, if Nat.Coprime n PP then a n else 0
    let XA : ℝ := ∑ n ∈ supp, a n * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g n p)
    let r : ℕ → ℝ := fun d =>
      (∑ n ∈ supp, if d ∣ n then a n else 0) - ∑ n ∈ supp, a n * g n d
    let R : ℝ := ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), |r d|
    c * XA - R ≤ S := by
  intro PP S XA r R
  set A := LeanLab.ChenExplicit.primesBelowIn P z with hA
  set A1 := LeanLab.ChenExplicit.primesBelowIn {p | p ∈ P ∧ p ∉ Q} z with hA1
  set A2 := A.filter (· ∈ Q) with hA2
  have hA1eq : A1 = A.filter (· ∉ Q) := by
    ext p; simp [hA1, hA, LeanLab.ChenExplicit.primesBelowIn, and_assoc]
  have hAprime : ∀ p ∈ A, p.Prime := fun p hp => (mem_primesBelowIn306 hP hp).1
  have hA1prime : ∀ p ∈ A1, p.Prime := by
    intro p hp; rw [hA1eq] at hp; exact hAprime p (Finset.mem_filter.mp hp).1
  have hA2prime : ∀ p ∈ A2, p.Prime := fun p hp => hAprime p (Finset.mem_filter.mp hp).1
  set PP1 := ∏ p ∈ A1, p with hPP1
  set PQ := ∏ p ∈ A2, p with hPQ
  have hPPeq : PP = PP1 * PQ := by
    show ∏ p ∈ A, p = _
    rw [hPP1, hPQ, hA1eq, mul_comm, hA2, Finset.prod_filter_mul_prod_filter_not]
  have hcop : Nat.Coprime PP1 PQ := by
    apply Nat.Coprime.prod_left; intro p hp; apply Nat.Coprime.prod_right; intro q hq
    rw [Nat.coprime_primes (hA1prime p hp) (hA2prime q hq)]
    rintro rfl
    rw [hA1eq, Finset.mem_filter] at hp
    exact hp.2 (Finset.mem_filter.mp hq).2
  have hPP1ne : PP1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hA1prime p hp).ne_zero
  have hPQne : PQ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hA2prime p hp).ne_zero
  have hsqQ : Squarefree PQ :=
    Squarefree.squarefree_of_dvd ⟨PP1, by rw [← hPPeq.trans (mul_comm _ _)]⟩
      (squarefree_primesBelowIn306 hP z)
  -- step 1, pointwise sieve inequality
  have hpt : ∀ n, a n * ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
      lam d * (ArithmeticFunction.moebius e : ℝ) * (if d * e ∣ n then (1 : ℝ) else 0) ≤
        if Nat.Coprime n PP then a n else 0 := by
    intro n
    have hsplit : ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
        lam d * (ArithmeticFunction.moebius e : ℝ) * (if d * e ∣ n then (1 : ℝ) else 0) =
        (∑ d ∈ PP1.divisors, lam d * (if d ∣ n then (1 : ℝ) else 0)) *
        (∑ e ∈ PQ.divisors, (ArithmeticFunction.moebius e : ℝ) *
          (if e ∣ n then (1 : ℝ) else 0)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro d hd; apply Finset.sum_congr rfl; intro e he
      have hde : Nat.Coprime d e :=
        (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).coprime_dvd_right
          (Nat.dvd_of_mem_divisors he)
      have hiff : (d * e ∣ n) ↔ (d ∣ n ∧ e ∣ n) :=
        ⟨fun h => ⟨(Dvd.intro e rfl).trans h, (Dvd.intro_left d rfl).trans h⟩,
          fun h => hde.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      by_cases h1 : d ∣ n <;> by_cases h2 : e ∣ n <;> simp [hiff, h1, h2]
    rw [hsplit, sum_dvd_gcd_rl306 _ _ hPP1ne, sum_dvd_gcd_rl306 _ _ hPQne, sum_moebius_rl306]
    have hX := hsieve (Nat.gcd n PP1) (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hPP1ne⟩)
    have hcopiff : Nat.Coprime n PP ↔ Nat.gcd n PP1 = 1 ∧ Nat.gcd n PQ = 1 := by
      rw [hPPeq]; exact Nat.coprime_mul_iff_right
    by_cases hQ1 : Nat.gcd n PQ = 1
    · by_cases hP1 : Nat.gcd n PP1 = 1
      · rw [if_pos (hcopiff.mpr ⟨hP1, hQ1⟩), if_pos hQ1, mul_one]
        rw [if_pos hP1] at hX; nlinarith [ha n]
      · rw [if_neg (fun h => hP1 (hcopiff.mp h).1), if_pos hQ1, mul_one]
        rw [if_neg hP1] at hX; nlinarith [ha n]
    · rw [if_neg hQ1, if_neg (fun h => hQ1 (hcopiff.mp h).2)]; simp
  -- step 2, sum over n and swap
  have hswap : ∑ n ∈ supp, a n * ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
      lam d * (ArithmeticFunction.moebius e : ℝ) * (if d * e ∣ n then (1 : ℝ) else 0) =
      ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors, lam d * (ArithmeticFunction.moebius e : ℝ) *
        (∑ n ∈ supp, if d * e ∣ n then a n else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hS : ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors, lam d * (ArithmeticFunction.moebius e : ℝ) *
        (∑ n ∈ supp, if d * e ∣ n then a n else 0) ≤ S := by
    rw [← hswap]
    exact Finset.sum_le_sum fun n _ => hpt n
  have hr : ∀ m, (∑ n ∈ supp, if m ∣ n then a n else 0) = r m + ∑ n ∈ supp, a n * g n m := by
    intro m; simp only [r]; ring
  have hfinal : ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors, lam d *
        (ArithmeticFunction.moebius e : ℝ) * (∑ n ∈ supp, if d * e ∣ n then a n else 0) =
      ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors, lam d * (ArithmeticFunction.moebius e : ℝ) *
        r (d * e) +
      ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors, lam d * (ArithmeticFunction.moebius e : ℝ) *
        ∑ n ∈ supp, a n * g n (d * e) := by
    simp_rw [hr, mul_add, Finset.sum_add_distrib]
  -- step 4, main term
  have hT1 : c * XA ≤ ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
      lam d * (ArithmeticFunction.moebius e : ℝ) * ∑ n ∈ supp, a n * g n (d * e) := by
    have hmul : ∀ d ∈ PP1.divisors, ∀ e ∈ PQ.divisors, ∀ n, g n (d * e) = g n d * g n e := by
      intro d hd e he n
      exact (hg n).map_mul_of_coprime ((hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).coprime_dvd_right
        (Nat.dvd_of_mem_divisors he))
    have heq : ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
        lam d * (ArithmeticFunction.moebius e : ℝ) * ∑ n ∈ supp, a n * g n (d * e) =
        ∑ n ∈ supp, a n * ((∑ d ∈ PP1.divisors, lam d * g n d) *
          (∑ e ∈ PQ.divisors, (ArithmeticFunction.moebius e : ℝ) * g n e)) := by
      have h0 : ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
          lam d * (ArithmeticFunction.moebius e : ℝ) * ∑ n ∈ supp, a n * g n (d * e) =
          ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
          lam d * (ArithmeticFunction.moebius e : ℝ) * ∑ n ∈ supp, a n * (g n d * g n e) := by
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
        congr 1
        exact Finset.sum_congr rfl fun n _ => by rw [hmul d hd e he n]
      rw [h0]
      simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [heq]
    show c * ∑ n ∈ supp, a n * ∏ p ∈ A, (1 - g n p) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n _
    have hE : ∑ e ∈ PQ.divisors, (ArithmeticFunction.moebius e : ℝ) * g n e =
        ∏ p ∈ A2, (1 - g n p) := by
      rw [← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
        (g n) (hg n) hsqQ), hPQ, Nat.primeFactors_prod hA2prime]
    have hsplitA : ∏ p ∈ A, (1 - g n p) =
        (∏ p ∈ A1, (1 - g n p)) * ∏ p ∈ A2, (1 - g n p) := by
      rw [hA1eq, hA2, mul_comm]
      exact (Finset.prod_filter_mul_prod_filter_not A (· ∈ Q) _).symm
    have hpos : 0 ≤ ∏ p ∈ A2, (1 - g n p) := Finset.prod_nonneg fun p hp => by
      have := (hgp n p (hQ p (Finset.mem_filter.mp hp).2)).2
      linarith
    rw [hE, hsplitA]
    have hm := hmain n
    calc c * (a n * ((∏ p ∈ A1, (1 - g n p)) * ∏ p ∈ A2, (1 - g n p)))
        = a n * ((c * ∏ p ∈ A1, (1 - g n p)) * ∏ p ∈ A2, (1 - g n p)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hpos) (ha n)
  -- step 5, remainder
  have hkey : ∀ d e, d ∣ PP1 → e ∣ PQ → Nat.gcd (d * e) PP1 = d := fun d e hd he => by
    rw [Nat.Coprime.gcd_mul_right_cancel d (hcop.symm.coprime_dvd_left he), Nat.gcd_eq_left hd]
  have hT2 : |∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
      lam d * (ArithmeticFunction.moebius e : ℝ) * r (d * e)| ≤ R := by
    calc _ ≤ ∑ d ∈ PP1.divisors, ∑ e ∈ PQ.divisors,
          |lam d * (ArithmeticFunction.moebius e : ℝ) * r (d * e)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun d _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ d ∈ PP1.divisors.filter (fun d => lam d ≠ 0), ∑ e ∈ PQ.divisors, |r (d * e)| := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun d _ => ?_
          split_ifs with hl
          · refine Finset.sum_le_sum fun e _ => ?_
            rw [abs_mul, abs_mul]
            have h1 := hlam d
            have h2 : |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            have h3 := abs_nonneg (r (d * e))
            have h4 := abs_nonneg (lam d)
            have h5 := abs_nonneg (ArithmeticFunction.moebius e : ℝ)
            calc |lam d| * |(ArithmeticFunction.moebius e : ℝ)| * |r (d * e)|
                ≤ 1 * 1 * |r (d * e)| := by gcongr
              _ = _ := by ring
          · simp [not_not.mp hl]
      _ = ∑ m ∈ (PP1.divisors.filter (fun d => lam d ≠ 0) ×ˢ PQ.divisors).image
            (fun x => x.1 * x.2), |r m| := by
          rw [Finset.sum_image, Finset.sum_product]
          intro x hx y hy hxy
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
            Nat.mem_divisors] at hx hy
          simp only at hxy
          have h1 : x.1 = y.1 := by
            rw [← hkey x.1 x.2 hx.1.1.1 hx.2.1, hxy, hkey y.1 y.2 hy.1.1.1 hy.2.1]
          have hx0 : 0 < x.1 := Nat.pos_of_ne_zero (fun h => by
            rw [h, zero_dvd_iff] at hx; exact hPP1ne hx.1.1.1)
          rw [h1] at hxy
          exact Prod.ext h1 (Nat.eq_of_mul_eq_mul_left (h1 ▸ hx0) hxy)
      _ ≤ R := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
          intro m hm
          rw [Finset.mem_image] at hm
          obtain ⟨⟨d, e⟩, hde, rfl⟩ := hm
          simp only [Finset.mem_product, Finset.mem_filter] at hde
          obtain ⟨⟨hd, hl⟩, he⟩ := hde
          rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [Nat.mem_divisors]
            refine ⟨?_, ?_⟩
            · show d * e ∣ PP
              rw [hPPeq]
              exact Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
            · show PP ≠ 0
              rw [hPPeq]; exact mul_ne_zero hPP1ne hPQne
          · have hdD := hsupp d hd hl
            have hele : e ≤ ∏ q ∈ Q, q := (Nat.divisor_le he).trans
              (Finset.prod_le_prod_of_subset_of_one_le'
                (fun p hp => (Finset.mem_filter.mp hp).2)
                (fun q hq _ => (hP q (hQ q hq)).one_lt.le))
            have hQr : (∏ q ∈ Q, (q : ℝ)) = ((∏ q ∈ Q, q : ℕ) : ℝ) := by push_cast; rfl
            have hele' : (e : ℝ) ≤ ((∏ q ∈ Q, q : ℕ) : ℝ) := by exact_mod_cast hele
            have he1 : (1 : ℝ) ≤ e := by exact_mod_cast Nat.pos_of_mem_divisors he
            simp only
            push_cast
            rw [hQr]
            calc (d : ℝ) * e < D * e := mul_lt_mul_of_pos_right hdD (by linarith)
              _ ≤ D * ((∏ q ∈ Q, q : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hele' hD.le
              _ = _ := mul_comm _ _
  have habs := abs_le.mp hT2
  linarith [hS, hfinal, hT1, habs.1]

open Classical in
/-- BJS Theorem 6, the explicit linear sieve, assembled from the pieces of its proof in
Section 2.4: the Rosser weights for the primes of P \ Q, their sieve property and level,
the identities of Nathanson Lemma 9.3, the bounds of BJS Lemma 11, Proposition 13 and
Lemma 14 with Table 1, and the reduction of Nathanson Theorem 9.7.
No sorry occurs in this assembly; it is CONDITIONAL ON the LEAF theorems of this file. -/
theorem theorem6_of_leaves306 : LeanLab.ChenExplicit.Theorem6Stmt := by
  intro F f hF k C₁ C₂ hrow ε hε hεk supp a h0 ha hsuppa P hP z hz g hg hgp Q hQ h4 D
  let P' : Set ℕ := {p | p ∈ P ∧ p ∉ Q}
  have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p hp.1
  have hgp' : ∀ n, ∀ p ∈ P', 0 ≤ g n p ∧ g n p < 1 := fun n p hp => hgp n p hp.1
  have hfil : ∀ u : ℝ,
      (LeanLab.ChenExplicit.primesBelowIn P' z).filter (fun p : ℕ => u ≤ (p : ℝ)) =
        (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => p ∉ Q ∧ u ≤ (p : ℝ)) := by
    intro u
    ext p
    simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range,
      Set.mem_ofPred_eq, P']
    tauto
  have hK : ∀ n, ∃ K : ℝ, 1 < K ∧ K < 1 + ε ∧ ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P' z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g n p)⁻¹ ≤ K * (log z / log u) := fun n =>
    leaf306_uniform_K P' z hz (g n) (hgp' n) ε hε
      (fun u hu1 hu2 => by rw [hfil]; exact h4 n u hu1 hu2)
  have hsqP' := squarefree_primesBelowIn306 hP' z
  intro PP s S XA r R
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · have hDpos : 0 < D := by linarith
    exact leaf306_reduction_upper supp a ha P hP z hz g hg hgp Q hQ D hDpos
      (rosserWeight306 D 1) (F s + ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve s)
      (rosserWeight306_abs_le D 1)
      (fun d hd hw => leaf306_rosser_support D z (by linarith) hD 1 d
        (primeFactor_lt_of_dvd306 hP' hd) hw)
      (fun m hm => (leaf306_rosser_sieve D m
        (hsqP'.squarefree_of_dvd (Nat.mem_divisors.mp hm).1)).1)
      (fun n => by
        obtain ⟨K, hK1, hKε, h29⟩ := hK n
        rw [leaf306_rosser_identity_upper P' hP' (g n) (hg n) z D]
        have hT := leaf306_T_odd_bound F f hF k C₁ C₂ hrow ε hε hεk P' hP' z hz (g n) (hg n)
          (hgp' n) K hK1 hKε h29 D hD
        have he : (F s + ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve s) *
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) =
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) +
              (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p)) *
                (F (log D / log z) - 1 +
                  ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
          simp only [s]; ring
        rw [he]
        linarith)
  · have hDpos : 0 < D := by nlinarith
    have hzD : z ≤ D := by nlinarith
    exact leaf306_reduction_lower supp a ha P hP z hz g hg hgp Q hQ D hDpos
      (rosserWeight306 D 0) (f s - ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve s)
      (rosserWeight306_abs_le D 0)
      (fun d hd hw => leaf306_rosser_support D z (by linarith) hzD 0 d
        (primeFactor_lt_of_dvd306 hP' hd) hw)
      (fun m hm => (leaf306_rosser_sieve D m
        (hsqP'.squarefree_of_dvd (Nat.mem_divisors.mp hm).1)).2)
      (fun n => by
        obtain ⟨K, hK1, hKε, h29⟩ := hK n
        rw [leaf306_rosser_identity_lower P' hP' (g n) (hg n) z D]
        have hT := leaf306_T_even_bound F f hF k C₁ C₂ hrow ε hε hεk P' hP' z hz (g n) (hg n)
          (hgp' n) K hK1 hKε h29 D hD
        have he : (f s - ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve s) *
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) =
            ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p) -
              (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P' z, (1 - g n p)) *
                (1 - f (log D / log z) +
                  ε * C₂ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
          simp only [s]; ring
        rw [he]
        linarith)

#print axioms rosserWeight306_abs_le
#print axioms leaf306_rosser_support
#print axioms leaf306_rosser_identity_upper
#print axioms leaf306_rosser_identity_lower
#print axioms leaf306_reduction_lower
#print axioms leaf306_reduction_upper
#print axioms leaf306_rosser_sieve
#print axioms leaf306_uniform_K
#print axioms tau_T_odd_bound306
#print axioms tau_T_even_bound306
#print axioms hSieve_nonneg306
#print axioms V_nonneg306
#print axioms bjsC306_pos
#print axioms leaf306_fn_nonneg
#print axioms bjsC306_large
#print axioms display18_one306
#print axioms leaf306_display18
#print axioms leaf306_lemma11
#print axioms theorem6_of_leaves306

end LeanLab.Cai2002
