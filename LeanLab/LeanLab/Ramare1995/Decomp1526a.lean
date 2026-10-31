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

/-- Helper: for odd `N`, a pair of primes summing to `N` contains `2`. -/
lemma two_of_odd_prime_pair {N p : ℕ} (hN : ¬ Even N) (hpN : p ≤ N) (hp : p.Prime)
    (hq : (N - p).Prime) : p = 2 ∨ N - p = 2 := by
  rcases hp.eq_two_or_odd' with h | h
  · exact Or.inl h
  rcases hq.eq_two_or_odd' with h' | h'
  · exact Or.inr h'
  exfalso
  apply hN
  have : N = p + (N - p) := by omega
  rw [this]
  exact h.add_odd h'

/-- LEAF. For odd `N` the only representations use the prime 2:
`rep N = 2 log 2 log (N - 2)` when `N - 2` is prime, else `0`. Definition of `rep`.
Unit U-1526. -/
theorem rep_of_odd {N : ℕ} (hN : ¬ Even N) :
    rep N = if (N - 2).Prime then 2 * Real.log 2 * Real.log ((N - 2 : ℕ) : ℝ) else 0 := by
  unfold rep
  split_ifs with hN2
  · have h4 : 4 ≤ N := by
      have := hN2.two_le
      omega
    have hne : (2 : ℕ) ≠ N - 2 := by
      intro h
      apply hN
      exact ⟨2, by omega⟩
    rw [sum_eq_add_of_mem 2 (N - 2) (mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two⟩)
      (mem_filter.mpr ⟨mem_range.mpr (by omega), hN2⟩) hne]
    · have e : N - (N - 2) = 2 := by omega
      simp only [hN2, e, Nat.prime_two, if_true]
      push_cast
      ring
    · intro c hc hc2
      rw [mem_filter, mem_range] at hc
      rw [if_neg]
      intro hq
      rcases two_of_odd_prime_pair hN (by omega) hc.2 hq with h | h
      · exact hc2.1 h
      · exact hc2.2 (by omega)
  · apply sum_eq_zero
    intro c hc
    rw [mem_filter, mem_range] at hc
    rw [if_neg]
    intro hq
    rcases two_of_odd_prime_pair hN (by omega) hc.2 hq with h | h
    · subst h; exact hN2 hq
    · have : c = N - 2 := by omega
      subst this; exact hN2 hc.2

/-- Helper: `θ b` as a sum over the primes of `range (b + 1)`. -/
lemma theta_natCast_eq (b : ℕ) :
    θ (b : ℝ) = ∑ p ∈ (range (b + 1)).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  congr 1
  ext x
  simp [mem_range]

/-- LEAF. The odd integers of `]a, b]` carry total weight at most `2 log 2 · θ(b)`:
each odd `N` contributes only through the prime `N - 2 ≤ b`. Uses `rep_of_odd`.
Unit U-1526. -/
theorem sum_rep_odd_le (a b : ℕ) :
    ∑ N ∈ (Ioc a b).filter (fun N => ¬ Even N), rep N ≤ 2 * Real.log 2 * θ (b : ℝ) := by
  set S := (Ioc a b).filter (fun N => ¬ Even N)
  have e1 : ∑ N ∈ S, rep N
      = ∑ N ∈ S.filter (fun N => (N - 2).Prime), 2 * Real.log 2 * Real.log ((N - 2 : ℕ) : ℝ) := by
    rw [sum_filter (fun N : ℕ => (N - 2).Prime)]
    apply sum_congr rfl
    intro N hN
    rw [mem_filter] at hN
    exact rep_of_odd hN.2
  rw [e1, ← mul_sum, theta_natCast_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hinj : Set.InjOn (fun N : ℕ => N - 2) (S.filter (fun N => (N - 2).Prime) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq] at hx hy
    have := hx.2.two_le
    have := hy.2.two_le
    simp only at hxy
    omega
  rw [← sum_image (f := fun q : ℕ => Real.log (q : ℝ)) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rw [mem_image] at hq
    obtain ⟨N, hN, rfl⟩ := hq
    simp only [S, mem_filter, mem_Ioc] at hN
    rw [mem_filter, mem_range]
    exact ⟨by omega, hN.2⟩
  · intro x _ _
    exact Real.log_natCast_nonneg _

/-- LEAF. Each term of `rep N` is at most `(log N)²`, so `rep N ≤ (log N)² · gcount N`.
Definition of `rep`; Halberstam-Richert Ch. 3, the passage from weighted to unweighted
counts. Unit U-1526. -/
theorem rep_le_log_sq_mul_gcount (N : ℕ) : rep N ≤ Real.log N ^ 2 * gcount N := by
  unfold rep gcount
  rw [sum_filter]
  have h : ∀ p ∈ range (N + 1),
      (if p.Prime then (if (N - p).Prime then Real.log p * Real.log ((N - p : ℕ) : ℝ) else 0)
        else 0) ≤ if p.Prime ∧ (N - p).Prime then Real.log N ^ 2 else 0 := by
    intro p hp
    rw [mem_range] at hp
    split_ifs with h1 h2 h3 h3
    · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h1.one_lt.le
      have hq1 : (1 : ℝ) ≤ ((N - p : ℕ) : ℝ) := by exact_mod_cast h2.one_lt.le
      have hpN : (p : ℝ) ≤ N := by exact_mod_cast (by omega : p ≤ N)
      have hqN : ((N - p : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - p ≤ N)
      have a1 : Real.log p ≤ Real.log N := Real.log_le_log (by linarith) hpN
      have a2 : Real.log ((N - p : ℕ) : ℝ) ≤ Real.log N := Real.log_le_log (by linarith) hqN
      have b1 : 0 ≤ Real.log p := Real.log_nonneg hp1
      have b2 : 0 ≤ Real.log ((N - p : ℕ) : ℝ) := Real.log_nonneg hq1
      rw [sq]
      exact mul_le_mul a1 a2 b2 (le_trans b1 a1)
    · exact absurd ⟨h1, h2⟩ h3
    · positivity
    · exact le_rfl
    · positivity
    · exact le_rfl
  refine le_trans (sum_le_sum h) ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- LEAF. Upper sanity bound for the first moment: `Σ_{N ∈ ]a, b]} rep N ≤ θ(b)²`, since the
pairs `(p, q)` with `a < p + q ≤ b` have `p, q ≤ b`. Unit U-1526. -/
theorem sum_rep_Ioc_le_theta_sq (a b : ℕ) :
    ∑ N ∈ Ioc a b, rep N ≤ θ (b : ℝ) ^ 2 := by
  set g : ℕ → ℕ → ℝ := fun i j =>
    if i.Prime ∧ j.Prime then Real.log i * Real.log j else 0 with hg
  have g0 : ∀ i j, 0 ≤ g i j := by
    intro i j
    simp only [hg]
    split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    · exact le_rfl
  have hrep : ∀ N, rep N = ∑ k ∈ range (N + 1), g k (N - k) := by
    intro N
    unfold rep
    rw [sum_filter]
    apply sum_congr rfl
    intro k _
    simp only [hg]
    split_ifs <;> simp_all
  have step1 : ∑ N ∈ Ioc a b, rep N ≤ ∑ N ∈ range (b + 1), rep N := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [mem_Ioc] at hx
      rw [mem_range]
      omega
    · intro x _ _
      exact rep_nonneg x
  refine le_trans step1 ?_
  simp only [hrep]
  rw [sum_comm' (t' := range (b + 1)) (s' := fun k => Icc k b)]
  swap
  · intro x y
    simp only [mem_range, mem_Icc]
    omega
  have hth : θ (b : ℝ) ^ 2 = ∑ i ∈ range (b + 1), ∑ j ∈ range (b + 1), g i j := by
    rw [theta_natCast_eq, sq, sum_mul_sum, sum_filter]
    apply sum_congr rfl
    intro i _
    rw [sum_filter]
    split_ifs with hi
    · apply sum_congr rfl
      intro j _
      simp only [hg]
      split_ifs <;> simp_all
    · symm
      apply sum_eq_zero
      intro j _
      simp only [hg]
      rw [if_neg (by tauto)]
  rw [hth]
  apply sum_le_sum
  intro i _
  have hinj : Set.InjOn (fun N : ℕ => N - i) (Icc i b : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_Icc, Set.mem_Icc] at hx hy
    simp only at hxy
    omega
  rw [← sum_image (f := fun j => g i j) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [mem_image] at hj
    obtain ⟨N, hN, rfl⟩ := hj
    rw [mem_Icc] at hN
    rw [mem_range]
    omega
  · intro j _ _
    exact g0 i j

/-- Helper: `]m, n]` holds at most `(n - m + 1) / 2` even integers. -/
lemma two_mul_card_even_Ioc_le {m n : ℕ} (h : m ≤ n) :
    2 * #((Ioc m n).filter Even) ≤ n - m + 1 := by
  have hu : (Ioc 0 n).filter Even = (Ioc 0 m).filter Even ∪ (Ioc m n).filter Even := by
    rw [← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le m) h]
  have hd : Disjoint ((Ioc 0 m).filter Even) ((Ioc m n).filter Even) := by
    apply disjoint_filter_filter
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_Ioc] at hx hx'
    omega
  have hcount : ∀ k, #((Ioc 0 k).filter Even) = k / 2 := by
    intro k
    rw [← Nat.Ioc_filter_dvd_card_eq_div k 2]
    congr 1
  have := card_union_of_disjoint hd
  rw [← hu, hcount, hcount] at this
  omega

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
    have hmn : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_mono (by linarith)
    have hI : Icc (⌊X⌋₊ + 1) ⌊2 * X⌋₊ = Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := by
      ext x; simp only [mem_Icc, mem_Ioc]; omega
    rw [hI]
    have hc := two_mul_card_even_Ioc_le hmn
    have hc' : (2 : ℝ) * (#((Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter Even) : ℝ)
        ≤ ((⌊2 * X⌋₊ - ⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_add, Nat.cast_sub hmn, Nat.cast_one] at hc'
    linarith
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
