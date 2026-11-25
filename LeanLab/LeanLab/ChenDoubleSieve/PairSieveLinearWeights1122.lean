import LeanLab.ChenDoubleSieve.Decomp348a
import LeanLab.ChenDoubleSieve.Decomp363b
import LeanLab.ChenDoubleSieve.Lemma41

/-!
The linear sieve lower bound weights of Wu 2004 Lemma 2.2, stated once for the sifting
problem of the shifted primes and every level D, free of the prime pairs of
Upsilon 4 and Upsilon 5.
Source: https://arxiv.org/pdf/0705.1652, page 6 Lemma 2.2 equation 2.5, which Wu quotes
from H. Iwaniec, Rosser's sieve, Acta Arith. 36 (1980), Theorem 1.
The pair statements Task366.pair_lower_weights4 and Task367.pair_lower_weights5 are
derived from this one LEAF here, with the moduli coprime to p1 p2 because every prime
factor of a modulus is below z while p1 and p2 are at least z.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set Asymptotics
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.LinearSieveWeights
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- LEAF: Wu 2004 page 6 Lemma 2.2 equation 2.5, single weight Rosser form:
Iwaniec 1980 Rosser's sieve Theorem 1; Opera de Cribro 2010 Theorems 11.12 and 11.18,
kappa 1, beta 2. Class HARD. Shifted primes, density 1 / phi q, sifting primes below
z = N ^ kappa1 not dividing N, level D. The weights are bounded by one, live on the
squarefree q at most D with such primes, satisfy the lower bound sieve inequality for
every n, and have density sum at least V(z) times f(s) minus delta, s = log D / log z,
uniformly in D for large N. For s at most 2 zero weights work since f vanishes there. -/
theorem linear_sieve_lower_weights (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → ∀ D : ℝ, 1 < D →
      ∃ w : ℕ → ℝ, (∀ q, |w q| ≤ 1) ∧
        (∀ q, w q ≠ 0 → q ∈ (Finset.Icc 1 ⌊D⌋₊).filter (fun q => Squarefree q ∧
          q.Coprime N ∧ ∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) < (N : ℝ) ^ kappa1)) ∧
        (∀ n : ℕ, ∑ q ∈ ((Finset.Icc 1 ⌊D⌋₊).filter (fun q => Squarefree q ∧
            q.Coprime N ∧ ∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) < (N : ℝ) ^ kappa1)).filter
              (fun q => q ∣ n), w q ≤
          if Wu41.Sifted N ((N : ℝ) ^ kappa1) n then 1 else 0) ∧
        lowerDensity N * (f (log D / log ((N : ℝ) ^ kappa1)) - δ) ≤
          ∑ q ∈ (Finset.Icc 1 ⌊D⌋₊).filter (fun q => Squarefree q ∧
            q.Coprime N ∧ ∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) < (N : ℝ) ^ kappa1),
            w q / (Nat.totient q : ℝ) := by
  sorry

/-- The logarithmic loss of the level is eventually below N ^ (1 / 6).
Derived from the little o comparison of a power of log with a power. -/
theorem log_rpow_lt_sixth (B : ℝ) : ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N →
    (log (N : ℝ)) ^ B < (N : ℝ) ^ (1 / 6 : ℝ) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop B (show (0 : ℝ) < 1 / 6 by norm_num)).def
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  have h3 := tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h2.and h3)
  refine ⟨N1, fun N hN => ?_⟩
  obtain ⟨hb, hgt⟩ := hN1 N hN
  have hp : 0 < (N : ℝ) ^ (1 / 6 : ℝ) := rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at hb
  have := le_abs_self ((log (N : ℝ)) ^ B)
  linarith

/-- The pair form of Wu 2004 Lemma 2.2 on pages 38 and 39 equation 10.5, for a prime
pair with p1, p2 at least z and p1 p2 below N ^ (1 / 2 - 2 kappa1), at level
D = Q / (p1 p2). CONDITIONAL ON linear_sieve_lower_weights. -/
theorem pair_weights_of_linear_sieve (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ p : ℕ × ℕ, p.1.Prime → p.2.Prime → (N : ℝ) ^ kappa1 ≤ p.1 →
        (N : ℝ) ^ kappa1 ≤ p.2 → ((p.1 * p.2 : ℕ) : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) →
        ∃ w : ℕ → ℝ, (∀ q, |w q| ≤ 1) ∧
          (∀ n : ℕ, ∑ q ∈ ((Finset.Icc 1 ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊).filter
              (fun q => Squarefree q ∧ q.Coprime (N * (p.1 * p.2)))).filter (fun q => q ∣ n),
              w q ≤ if Wu41.Sifted N ((N : ℝ) ^ kappa1) n then 1 else 0) ∧
          lowerDensity N * (f (lowerLevel B N (p.1 * p.2)) - δ) ≤
            ∑ q ∈ (Finset.Icc 1 ⌊Task363.sieveLevel B N / (p.1 * p.2 : ℕ)⌋₊).filter
              (fun q => Squarefree q ∧ q.Coprime (N * (p.1 * p.2))),
              w q / (Nat.totient q : ℝ) := by
  intro δ hδ B _hB
  obtain ⟨N0, hN0⟩ := linear_sieve_lower_weights F f h δ hδ
  obtain ⟨N1, hN1⟩ := log_rpow_lt_sixth B
  refine ⟨max (max N0 N1) 2, ?_⟩
  intro N hE hN p hp1 hp2 hz1 hz2 hprod
  have hN0' : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  set D : ℝ := Task363.sieveLevel B N / ((p.1 * p.2 : ℕ) : ℝ) with hD
  have hlogpos : 0 < log (N : ℝ) := log_pos hN1r
  have hLB : 0 < (log (N : ℝ)) ^ B := rpow_pos_of_pos hlogpos _
  have hd0 : (0 : ℝ) < ((p.1 * p.2 : ℕ) : ℝ) := by
    have := Nat.mul_pos hp1.pos hp2.pos
    exact_mod_cast this
  have hD1 : 1 < D := by
    rw [hD, Task363.sieveLevel, lt_div_iff₀ hd0, one_mul, lt_div_iff₀ hLB]
    have hk : (1 / 2 - 2 * kappa1 : ℝ) = 1 / 3 := by norm_num [kappa1]
    rw [hk] at hprod
    have hsplit : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) := by
      rw [← rpow_add hNpos]
      norm_num
    rw [hsplit]
    have h6 := hN1 N hN1'
    have h3pos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := rpow_pos_of_pos hNpos _
    calc ((p.1 * p.2 : ℕ) : ℝ) * (log (N : ℝ)) ^ B
        < (N : ℝ) ^ (1 / 3 : ℝ) * (log (N : ℝ)) ^ B := mul_lt_mul_of_pos_right hprod hLB
      _ < (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) := mul_lt_mul_of_pos_left h6 h3pos
  obtain ⟨w, hw, hsupp, hsieve, hdens⟩ := hN0 N hE hN0' D hD1
  set M' := (Finset.Icc 1 ⌊D⌋₊).filter (fun q => Squarefree q ∧
    q.Coprime N ∧ ∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) < (N : ℝ) ^ kappa1) with hM'
  set M := (Finset.Icc 1 ⌊D⌋₊).filter
    (fun q => Squarefree q ∧ q.Coprime (N * (p.1 * p.2))) with hM
  have hsub : M' ⊆ M := by
    intro q hq
    rw [hM', Finset.mem_filter] at hq
    obtain ⟨hI, hsq, hcop, hr⟩ := hq
    rw [hM, Finset.mem_filter]
    refine ⟨hI, hsq, Nat.Coprime.mul_right hcop (Nat.Coprime.mul_right ?_ ?_)⟩
    · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp1).2 ?_)
      intro hd
      have := hr p.1 hp1 hd
      linarith
    · refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp2).2 ?_)
      intro hd
      have := hr p.2 hp2 hd
      linarith
  have hzero : ∀ q, q ∉ M' → w q = 0 := by
    intro q hq
    by_contra hne
    exact hq (hsupp q hne)
  refine ⟨w, hw, ?_, ?_⟩
  · intro n
    have heq : ∑ q ∈ M'.filter (fun q => q ∣ n), w q = ∑ q ∈ M.filter (fun q => q ∣ n), w q := by
      apply Finset.sum_subset (Finset.filter_subset_filter _ hsub)
      intro q hq hqn
      apply hzero
      intro hqM'
      exact hqn (Finset.mem_filter.2 ⟨hqM', (Finset.mem_filter.1 hq).2⟩)
    rw [← heq]
    exact hsieve n
  · have heq : ∑ q ∈ M', w q / (Nat.totient q : ℝ) = ∑ q ∈ M, w q / (Nat.totient q : ℝ) := by
      apply Finset.sum_subset hsub
      intro q _ hq
      rw [hzero q hq, zero_div]
    rw [← heq]
    have hlev : lowerLevel B N (p.1 * p.2) = log D / log ((N : ℝ) ^ kappa1) := rfl
    rw [hlev]
    exact hdens

end LeanLab.ChenDoubleSieve.LinearSieveWeights
