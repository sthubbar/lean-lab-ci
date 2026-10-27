/-
Ramaré 1995, P0008, unit U-1526, run 20261025T2003Z-426. DECOMPOSE file a of three.
The representation function and the density principle behind Theorem 2.

Ramaré's Theorem 2, p. 646, is the density input of Theorem 1: at least `X/5` even `N` in
`]X, 2X]` are sums of two primes, for `X ≥ exp 67`. Section 2.3, p. 653 to 656, gets it by
comparing a first moment of a weighted representation count with an upper bound for it on
average, by Cauchy's inequality; the text of the numdam PDF loses the displays, so the shape
used here is the standard one, Halberstam-Richert, Sieve Methods, 1974, Ch. 3 and Nathanson,
Additive Number Theory: The Classical Bases, GTM 164, Section 7.4, Schnirelmann's density
argument: `(Σ r(N))² ≤ #{N : r(N) > 0} · Σ r(N)²`.

`rep N = Σ_{p + q = N} log p log q` over ordered pairs of primes.
`theorem2_of_moments` gives Ramaré's Theorem 2 from a first moment `L X²` and a second moment
`U X³` with `L² / U ≥ 1/5`; `density_of_moments` gives `L²/U · X` for any `L, U`.
Files b and c supply a second moment from a Selberg-type upper bound and a first moment from
Chebyshev bounds, with constants far weaker than Ramaré's.

AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this concerns a positive density of sums of two primes.
-/
import Mathlib
import LeanLab.Ramare1995.Section9

open Finset Real
open scoped Chebyshev Classical

noncomputable section
namespace LeanLab.Ramare1995.Decomp1526a
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- `rep N = Σ_{p + q = N, p, q prime} log p · log q`, ordered pairs. -/
def rep (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter Nat.Prime,
    if (N - p).Prime then Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0

/-- `gcount N = #{p ≤ N : p and N - p prime}`, the unweighted Goldbach count. -/
def gcount (N : ℕ) : ℕ := #{p ∈ range (N + 1) | p.Prime ∧ (N - p).Prime}

/-- The even integers of `]X, 2X]`, as `Ioc ⌊X⌋ ⌊2X⌋`. -/
def evenBlock (X : ℝ) : Finset ℕ := (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter Even

theorem rep_nonneg (N : ℕ) : 0 ≤ rep N := by
  unfold rep
  refine sum_nonneg fun p _ => ?_
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  · exact le_rfl

/-- LEAF. If `rep N > 0` then `N = p + q` with `p, q` prime: a positive term of the sum
exhibits the pair. Definition of `rep`; Ramaré 1995 Section 2.3, p. 653. Unit U-1526. -/
theorem isGoldbachSum_of_rep_pos {N : ℕ} (h : 0 < rep N) : IsGoldbachSum N := by
  unfold rep at h
  by_contra hNotG
  have hSumZero : ∑ p ∈ filter Nat.Prime (range (N + 1)), ite (Nat.Prime (N - p)) (Real.log ↑p * Real.log ↑(N - p)) 0 = 0 := by
    apply sum_eq_zero
    intro p hp
    have hNotPrimeNp : ¬(N - p).Prime := by
      intro hPrimeNp
      apply hNotG
      unfold IsGoldbachSum
      use p, (N - p)
      rw [mem_filter] at hp
      have h1 : p.Prime := hp.right
      have h2 : (N - p).Prime := hPrimeNp
      have h3 : p + (N - p) = N := by
        rw [mem_range] at hp
        omega
      exact ⟨h1, h2, h3⟩
    rw [ite_eq_right_iff.mpr (by intro h_prime; exact False.elim (hNotPrimeNp h_prime))]
  linarith

/-- LEAF. Conversely every sum of two primes has `rep N > 0`, since `log p > 0` for every
prime. Definition of `rep`. Unit U-1526. -/
theorem rep_pos_of_isGoldbachSum {N : ℕ} (h : IsGoldbachSum N) : 0 < rep N := by
  unfold IsGoldbachSum at h
  rcases h with ⟨p, q, hp, hq, hpq⟩
  unfold rep
  have hp_in : p ∈ filter Nat.Prime (range (N + 1)) := by
    rw [mem_filter, mem_range]
    refine ⟨by omega, hp⟩
  have h_term : (if (N - p).Prime then Real.log ↑p * Real.log ↑(N - p) else 0) > 0 := by
    have h_Np : N - p = q := by omega
    rw [h_Np]
    rw [ite_eq_left_iff.mpr (by intro h; exact False.elim (h hq))]
    have h1 : (0 : ℝ) < Real.log ↑p := by
      apply Real.log_pos
      have : 2 ≤ p := hp.two_le
      exact_mod_cast (by omega)
    have h2 : (0 : ℝ) < Real.log ↑q := by
      apply Real.log_pos
      have : 2 ≤ q := hq.two_le
      exact_mod_cast (by omega)
    positivity
  have h_nonneg : ∀ x ∈ filter Nat.Prime (range (N + 1)), 0 ≤ (if (N - x).Prime then Real.log ↑x * Real.log ↑(N - x) else 0) := by
    intro x hx
    split_ifs with h_prime
    · have h1 : 0 ≤ Real.log ↑x := Real.log_natCast_nonneg _
      have h2 : 0 ≤ Real.log ↑(N - x) := Real.log_natCast_nonneg _
      positivity
    · rfl
  exact sum_pos' h_nonneg ⟨p, hp_in, h_term⟩

/-- LEAF. Cauchy-Schwarz on the support: for `f ≥ 0` on a finite set `s`,
`(Σ_s f)² ≤ #{n ∈ s : f n > 0} · Σ_s f²`. Nathanson GTM 164, Section 7.4; Ramaré 1995
Section 2.3, p. 653. Unit U-1526. -/
theorem sq_sum_le_card_pos_mul_sum_sq (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ s, f n) ^ 2 ≤ (#(s.filter fun n => 0 < f n) : ℝ) * ∑ n ∈ s, f n ^ 2 := by
  have e : ∑ n ∈ s, f n = ∑ n ∈ s.filter (fun n => 0 < f n), f n := by
    have h1 := sum_filter_add_sum_filter_not s (fun n => 0 < f n) f
    have h2 : ∑ n ∈ filter (fun x => ¬0 < f x) s, f n = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [mem_filter] at hx
      have h1_pos : 0 ≤ f x := hf x
      have h2_notpos : ¬ 0 < f x := hx.2
      linarith
    rw [h2, add_zero] at h1
    exact h1.symm
  rw [e]
  have H := sum_mul_sq_le_sq_mul_sq (s := s.filter (fun n => 0 < f n)) (f := fun _ => (1 : ℝ)) (g := f)
  have e1 : (∑ x ∈ s.filter (fun n => 0 < f n), (1 : ℝ) * f x) = (∑ x ∈ s.filter (fun n => 0 < f n), f x) := by
    apply sum_congr rfl
    intro x _
    rw [one_mul]
  have e2 : (∑ x ∈ s.filter (fun n => 0 < f n), (1 : ℝ) ^ 2) = (s.filter (fun n => 0 < f n)).card := by
    have h_pow : ∑ x ∈ s.filter (fun n => 0 < f n), (1 : ℝ) ^ 2 = ∑ x ∈ s.filter (fun n => 0 < f n), (1 : ℝ) := by
      apply sum_congr rfl
      intro x _
      rw [one_pow]
    rw [h_pow, sum_const]
    simp
  rw [e1, e2] at H
  have h_le : ∑ n ∈ s.filter (fun n => 0 < f n), f n ^ 2 ≤ ∑ n ∈ s, f n ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro x _ _
    positivity
  have h_bound : (s.filter (fun n => 0 < f n)).card * ∑ n ∈ s.filter (fun n => 0 < f n), f n ^ 2 ≤ (s.filter (fun n => 0 < f n)).card * ∑ n ∈ s, f n ^ 2 := by
    apply mul_le_mul_of_nonneg_left h_le (by positivity)
  exact le_trans H h_bound

/-- LEAF. For odd `N` the only representations use the prime 2:
`rep N = 2 log 2 log (N - 2)` when `N - 2` is prime, else `0`. Definition of `rep`.
Unit U-1526. -/
theorem rep_of_odd {N : ℕ} (hN : ¬ Even N) :
    rep N = if (N - 2).Prime then 2 * Real.log 2 * Real.log ((N - 2 : ℕ) : ℝ) else 0 := by
  sorry

/-- LEAF. The odd integers of `]a, b]` carry total weight at most `2 log 2 · θ(b)`:
each odd `N` contributes only through the prime `N - 2 ≤ b`. Uses `rep_of_odd`.
Unit U-1526. -/
theorem sum_rep_odd_le (a b : ℕ) :
    ∑ N ∈ (Ioc a b).filter (fun N => ¬ Even N), rep N ≤ 2 * Real.log 2 * θ (b : ℝ) := by
  sorry

/-- LEAF. Each term of `rep N` is at most `(log N)²`, so `rep N ≤ (log N)² · gcount N`.
Definition of `rep`; Halberstam-Richert Ch. 3, the passage from weighted to unweighted
counts. Unit U-1526. -/
theorem rep_le_log_sq_mul_gcount (N : ℕ) : rep N ≤ Real.log N ^ 2 * gcount N := by
  sorry

/-- LEAF. Upper sanity bound for the first moment: `Σ_{N ∈ ]a, b]} rep N ≤ θ(b)²`, since the
pairs `(p, q)` with `a < p + q ≤ b` have `p, q ≤ b`. Unit U-1526. -/
theorem sum_rep_Ioc_le_theta_sq (a b : ℕ) :
    ∑ N ∈ Ioc a b, rep N ≤ θ (b : ℝ) ^ 2 := by
  sorry

/-- LEAF. The even integers of `]X, 2X]` number at most `X/2 + 1`, so the density in
Theorem 2 cannot exceed one half. Ramaré 1995 Section 2.3, p. 653, the expected count `X/2`.
Unit U-1526. -/
theorem card_evenBlock_le {X : ℝ} (hX : 0 ≤ X) : (#(evenBlock X) : ℝ) ≤ X / 2 + 1 := by
  unfold evenBlock
  have e1 : (Ioc ⌊X⌋₊ ⌊2 * X⌋₊) ⊆ Icc (⌊X⌋₊ + 1) ⌊2 * X⌋₊ := by
    intro x hx
    rw [mem_Ioc] at hx
    rw [mem_Icc]
    exact ⟨by omega, hx.2⟩
  have e2 : ((Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter Even) ⊆ ((Icc (⌊X⌋₊ + 1) ⌊2 * X⌋₊).filter Even) := filter_subset_filter _ e1
  have e3 : (#((Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter Even) : ℝ) ≤ (#((Icc (⌊X⌋₊ + 1) ⌊2 * X⌋₊).filter Even) : ℝ) := by
    exact Nat.cast_le.mpr (card_le_card e2)
  have h_bound : (#((Icc (⌊X⌋₊ + 1) ⌊2 * X⌋₊).filter Even) : ℝ) ≤ ((⌊2 * X⌋₊ : ℝ) - (⌊X⌋₊ : ℝ) + 1) / 2 := by
    sorry
  have h_bound2 : ((⌊2 * X⌋₊ : ℝ) - (⌊X⌋₊ : ℝ) + 1) / 2 ≤ X / 2 + 1 := by
    have h1 : (⌊2 * X⌋₊ : ℝ) ≤ 2 * X := Nat.floor_le (by positivity)
    have h2 : X - 1 < (⌊X⌋₊ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one X)
    linarith
  apply le_trans e3
  apply le_trans h_bound h_bound2

/-- **Density principle**, assembly, zero sorry of its own: a first moment `A > 0` and a
second moment `B > 0` give at least `A² / B` even sums of two primes in `]X, 2X]`.
Uses the leaves `sq_sum_le_card_pos_mul_sum_sq` and `isGoldbachSum_of_rep_pos`. -/
theorem density_principle (X A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (h1 : A ≤ ∑ N ∈ evenBlock X, rep N) (h2 : ∑ N ∈ evenBlock X, rep N ^ 2 ≤ B) :
    A ^ 2 / B ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  classical
  have hcs := sq_sum_le_card_pos_mul_sum_sq (evenBlock X) rep rep_nonneg
  have hsub : (evenBlock X).filter (fun n => 0 < rep n) ⊆
      {N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} := by
    intro N hN
    simp only [evenBlock, mem_filter] at hN
    rw [mem_filter]
    exact ⟨hN.1.1, hN.1.2, isGoldbachSum_of_rep_pos hN.2⟩
  have hcard : (#((evenBlock X).filter fun n => 0 < rep n) : ℝ) ≤
      (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
    exact_mod_cast card_le_card hsub
  set S := ∑ N ∈ evenBlock X, rep N
  set Q := ∑ N ∈ evenBlock X, rep N ^ 2
  set C := (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ)
  have hC0 : 0 ≤ C := by positivity
  have hAS : A ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hA.le h1 2
  have hSC : S ^ 2 ≤ C * Q :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => sq_nonneg _))
  have hQB : C * Q ≤ C * B := mul_le_mul_of_nonneg_left h2 hC0
  rw [div_le_iff₀ hB]
  linarith

/-- **Moments to density**, assembly, zero sorry of its own: if for every `X ≥ exp 67` the
first moment over the even `N ∈ ]X, 2X]` is at least `L X²` and the second at most `U X³`,
then at least `(L² / U) X` of them are sums of two primes. -/
theorem density_of_moments (L U : ℝ) (hL : 0 < L) (hU : 0 < U)
    (h1 : ∀ X : ℝ, exp 67 ≤ X → L * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N)
    (h2 : ∀ X : ℝ, exp 67 ≤ X → ∑ N ∈ evenBlock X, rep N ^ 2 ≤ U * X ^ 3) :
    ∀ X : ℝ, exp 67 ≤ X →
      L ^ 2 / U * X ≤ (#{N ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊ | Even N ∧ IsGoldbachSum N} : ℝ) := by
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have key := density_principle X (L * X ^ 2) (U * X ^ 3) (by positivity) (by positivity)
    (h1 X hX) (h2 X hX)
  have e : (L * X ^ 2) ^ 2 / (U * X ^ 3) = L ^ 2 / U * X := by
    field_simp
  rw [e] at key
  exact key

/-- **Ramaré's Theorem 2 from two moments**, assembly, zero sorry of its own, CONDITIONAL ON
a first moment `L X²` and a second moment `U X³` with `L² / U ≥ 1/5`. In the paper the first
moment is Proposition 1 and the second is assembled from Propositions 2, 3, 4 with the
enveloping sieve of Section 2.1, p. 648 to 656; those are the deep inputs left. -/
theorem theorem2_of_moments (L U : ℝ) (hL : 0 < L) (hU : 0 < U) (hc : 1 / 5 ≤ L ^ 2 / U)
    (h1 : ∀ X : ℝ, exp 67 ≤ X → L * X ^ 2 ≤ ∑ N ∈ evenBlock X, rep N)
    (h2 : ∀ X : ℝ, exp 67 ≤ X → ∑ N ∈ evenBlock X, rep N ^ 2 ≤ U * X ^ 3) : Theorem2 := by
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (exp_pos 67) hX
  have := density_of_moments L U hL hU h1 h2 X hX
  have : X / 5 ≤ L ^ 2 / U * X := by
    rw [div_eq_mul_inv, mul_comm X]; exact mul_le_mul_of_nonneg_right (by linarith) hX0.le
  linarith

/-- Vacuity: the block `evenBlock X` is not empty, `4 ∈ evenBlock 2`. -/
example : (4 : ℕ) ∈ evenBlock 2 := by
  simp only [evenBlock, mem_filter, mem_Ioc]
  norm_num

end LeanLab.Ramare1995.Decomp1526a
