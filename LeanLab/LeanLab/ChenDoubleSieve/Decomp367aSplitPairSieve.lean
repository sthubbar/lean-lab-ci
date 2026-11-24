import LeanLab.ChenDoubleSieve.Decomp367a

/-!
Split of Task367.pair_linear_sieve_with_remainder, the F5 lower sieve supply.
Source: https://arxiv.org/pdf/0705.1652, page 6 Lemma 2.2 equation 2.5,
applied on pages 38 and 39 to the sets A_d with d = p1 p2 in equation 10.5.
The linear sieve is split into the existence of lower bound sieve weights
and the finite sieve inequality those weights give for A_d.
The li scale comparison and the summation over prime pairs are proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- LEAF: Wu 2004 page 6 Lemma 2.2, the Rosser Iwaniec lower bound weights of
dimension one at level D = Q / (p1 p2) and sifting level z = N ^ kappa1, used on
page 38 and page 39 equation 10.5 for each pair of Upsilon 5. Class HARD.
The weights are bounded by one, satisfy the lower bound sieve inequality for every
integer when summed over the residual moduli, and their density sum is at least
V(z) times f(s) minus an error delta uniform over the pairs, where
s = lowerLevel B N (p1 p2) = log D / log z.
The density 1 / phi q is the density of A_{dq} relative to A_d. -/
theorem pair_lower_weights5 (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ p ∈ lowerPairs5 N, ∃ w : ℕ → ℝ, (∀ q, |w q| ≤ 1) ∧
        (∀ n : ℕ, ∑ q ∈ (pairModuli5 B N p).filter (fun q => q ∣ n), w q ≤
          if Wu41.Sifted N ((N : ℝ) ^ kappa1) n then 1 else 0) ∧
        lowerDensity N * (f (lowerLevel B N (p.1 * p.2)) - δ) ≤
          ∑ q ∈ pairModuli5 B N p, w q / (Nat.totient q : ℝ) := by
  sorry

/-- Wu 2004 page 6 Lemma 2.2, the finite step of the lower bound sieve for
A_d with d = p1 p2 as used on page 38 and page 39 equation 10.5. Proved here.
Sum the weight inequality over a in A_d, exchange the sums, use that every residual
modulus q is coprime to d so d q divides a exactly when d and q do, use
phi(d q) = phi d phi q, and bound each weighted discrepancy below by minus its
absolute value. No hypothesis on N or on the pair is needed. -/
theorem pair_sifted_ge_of_weights5 (B : ℝ) (N : ℕ) (p : ℕ × ℕ) (w : ℕ → ℝ)
    (hw : ∀ q, |w q| ≤ 1)
    (hs : ∀ n : ℕ, ∑ q ∈ (pairModuli5 B N p).filter (fun q => q ∣ n), w q ≤
      if Wu41.Sifted N ((N : ℝ) ^ kappa1) n then 1 else 0) :
    Wu04.li N / (Nat.totient (p.1 * p.2) : ℝ) *
        ∑ q ∈ pairModuli5 B N p, w q / (Nat.totient q : ℝ) -
      ∑ q ∈ pairModuli5 B N p,
        |(#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℝ) -
          Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| ≤
      (Wu41.S (primeSequence N) (p.1 * p.2) N ((N : ℝ) ^ kappa1) : ℝ) := by
  set A := primeSequence N with hA
  set d := p.1 * p.2 with hd
  set M := pairModuli5 B N p with hM
  set z : ℝ := (N : ℝ) ^ kappa1 with hz
  have hcop : ∀ q ∈ M, Nat.Coprime d q := by
    intro q hq
    have h1 := (Finset.mem_filter.1 hq).2.2
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left d N) h1).symm
  have hdvd : ∀ q ∈ M, ∀ a : ℕ, (d * q ∣ a ↔ d ∣ a ∧ q ∣ a) := by
    intro q hq a
    exact ⟨fun h => ⟨dvd_trans (dvd_mul_right d q) h, dvd_trans (dvd_mul_left q d) h⟩,
      fun h => (hcop q hq).mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  have hS : (Wu41.S A d N z : ℝ) =
      ∑ a ∈ A.filter (fun a => d ∣ a), (if Wu41.Sifted N z a then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole, Finset.filter_filter]
    rfl
  have h2 : ∑ a ∈ A.filter (fun a => d ∣ a), ∑ q ∈ M.filter (fun q => q ∣ a), w q ≤
      (Wu41.S A d N z : ℝ) := by
    rw [hS]
    exact Finset.sum_le_sum (fun a _ => hs a)
  have h3 : ∑ a ∈ A.filter (fun a => d ∣ a), ∑ q ∈ M.filter (fun q => q ∣ a), w q =
      ∑ q ∈ M, w q * (#(A.filter (fun a => d * q ∣ a)) : ℝ) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_filter (fun q => q ∣ a) w)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, Finset.filter_filter]
    congr 3
    apply Finset.filter_congr
    intro a _
    exact (hdvd q hq a).symm
  have h4 : ∀ q ∈ M, Wu04.li N / (Nat.totient d : ℝ) * (w q / (Nat.totient q : ℝ)) -
      |(#(A.filter (fun a => d * q ∣ a)) : ℝ) - Wu04.li N / (Nat.totient (d * q) : ℝ)| ≤
      w q * (#(A.filter (fun a => d * q ∣ a)) : ℝ) := by
    intro q hq
    set X : ℝ := (#(A.filter (fun a => d * q ∣ a)) : ℝ)
    have htot : (Nat.totient (d * q) : ℝ) = (Nat.totient d : ℝ) * (Nat.totient q : ℝ) := by
      rw [Nat.totient_mul (hcop q hq)]
      push_cast
      ring
    have h1 := neg_abs_le (w q * (X - Wu04.li N / (Nat.totient (d * q) : ℝ)))
    rw [abs_mul] at h1
    have h5 := mul_le_mul_of_nonneg_right (hw q)
      (abs_nonneg (X - Wu04.li N / (Nat.totient (d * q) : ℝ)))
    have heq : w q * X = Wu04.li N / (Nat.totient d : ℝ) * (w q / (Nat.totient q : ℝ)) +
        w q * (X - Wu04.li N / (Nat.totient (d * q) : ℝ)) := by
      rw [htot]
      ring
    rw [heq]
    linarith
  calc _ = ∑ q ∈ M, (Wu04.li N / (Nat.totient d : ℝ) * (w q / (Nat.totient q : ℝ)) -
      |(#(A.filter (fun a => d * q ∣ a)) : ℝ) - Wu04.li N / (Nat.totient (d * q) : ℝ)|) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∑ q ∈ M, w q * (#(A.filter (fun a => d * q ∣ a)) : ℝ) := Finset.sum_le_sum h4
    _ = _ := h3.symm
    _ ≤ _ := h2

/-- The li density scale is bounded by Theta, with li nonnegative.
Proved from Task363.density_scale_bounded and Task363.li_ratio_tendsto. -/
theorem li_density_scale5 : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
    Wu04.li N * lowerDensity N ≤ K * Θ N ∧ 0 ≤ Wu04.li N := by
  obtain ⟨L, hL, J, hJ⟩ := Task363.density_scale_bounded
  have hev := (Task363.li_ratio_tendsto.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_lt_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  refine ⟨2 * L, by positivity, max 2 (max J T), ?_⟩
  intro N hEven hN
  have hN2 : 2 ≤ N := by omega
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hli0 : 0 ≤ Wu04.li N := by
    unfold Wu04.li
    apply intervalIntegral.integral_nonneg (by exact_mod_cast hN2)
    intro t ht
    exact inv_nonneg.mpr (log_nonneg (by linarith [ht.1]))
  have hr : Wu04.li N / ((N : ℝ) / log N) < 2 := hT N (by omega)
  have hd : 0 < (N : ℝ) / log N := by positivity
  have hli : Wu04.li N ≤ 2 * ((N : ℝ) / log N) := by
    rw [div_lt_iff₀ hd] at hr
    linarith
  have hV := (lowerDensity_pos hEven).le
  have hs := hJ N hEven (by omega)
  refine ⟨?_, hli0⟩
  calc Wu04.li N * lowerDensity N ≤ 2 * ((N : ℝ) / log N) * lowerDensity N :=
        mul_le_mul_of_nonneg_right hli hV
    _ = 2 * ((N : ℝ) / log N * lowerDensity N) := by ring
    _ ≤ 2 * (L * Θ N) := by linarith
    _ = 2 * L * Θ N := by ring

/-- The sixth sieve count is the sum of the sifted counts over the F5 pairs. -/
theorem sieveTerms_five_eq (N : ℕ) : sieveTerms N 5 =
    ∑ p ∈ lowerPairs5 N,
      (Wu41.S (primeSequence N) (p.1 * p.2) N ((N : ℝ) ^ kappa1) : ℝ) := by
  rw [← Nat.cast_sum]
  rfl

/-- Assembly of Task367.pair_linear_sieve_with_remainder from the two LEAFs,
with sieve constant C = 1. CONDITIONAL ON pair_lower_weights5 and
pair_sifted_ge_of_weights5. -/
theorem pair_linear_sieve_with_remainder_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain5 f B N - δ * Θ N * lowerTotientMass5 N -
          C * rawRemainder5 B N ≤ sieveTerms N 5 := by
  intro δ hδ
  obtain ⟨K, hK, M, hM⟩ := li_density_scale5
  refine ⟨1, zero_le_one, ?_⟩
  intro B hB
  obtain ⟨J, hJ⟩ := pair_lower_weights5 F f h (δ / K) (by positivity) B hB
  refine ⟨max M J, ?_⟩
  intro N hEven hN
  obtain ⟨hliV, hli0⟩ := hM N hEven (le_trans (le_max_left _ _) hN)
  have hpair : ∀ p ∈ lowerPairs5 N,
      Wu04.li N * lowerDensity N *
          (f (lowerLevel B N (p.1 * p.2)) / (Nat.totient (p.1 * p.2) : ℝ)) -
        δ / K * (Wu04.li N * lowerDensity N) * (1 / (Nat.totient (p.1 * p.2) : ℝ)) -
        ∑ q ∈ pairModuli5 B N p,
          |(#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℝ) -
            Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| ≤
        (Wu41.S (primeSequence N) (p.1 * p.2) N ((N : ℝ) ^ kappa1) : ℝ) := by
    intro p hp
    obtain ⟨w, hw, hs, hmain⟩ := hJ N hEven (le_trans (le_max_right _ _) hN) p hp
    have hBw := pair_sifted_ge_of_weights5 B N p w hw hs
    have hc : 0 ≤ Wu04.li N / (Nat.totient (p.1 * p.2) : ℝ) :=
      div_nonneg hli0 (Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hmain hc
    have heq : Wu04.li N / (Nat.totient (p.1 * p.2) : ℝ) *
        (lowerDensity N * (f (lowerLevel B N (p.1 * p.2)) - δ / K)) =
        Wu04.li N * lowerDensity N *
          (f (lowerLevel B N (p.1 * p.2)) / (Nat.totient (p.1 * p.2) : ℝ)) -
        δ / K * (Wu04.li N * lowerDensity N) *
          (1 / (Nat.totient (p.1 * p.2) : ℝ)) := by ring
    linarith
  have hsum := Finset.sum_le_sum hpair
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have hbudget : δ / K * (Wu04.li N * lowerDensity N) * lowerTotientMass5 N ≤
      δ * Θ N * lowerTotientMass5 N := by
    apply mul_le_mul_of_nonneg_right _ (lowerTotientMass5_nonneg N)
    calc δ / K * (Wu04.li N * lowerDensity N) ≤ δ / K * (K * Θ N) :=
          mul_le_mul_of_nonneg_left hliV (by positivity)
      _ = δ * Θ N := by field_simp
  rw [sieveTerms_five_eq]
  have hL : liMain5 f B N = Wu04.li N * lowerDensity N *
      ∑ p ∈ lowerPairs5 N,
        f (lowerLevel B N (p.1 * p.2)) / (Nat.totient (p.1 * p.2) : ℝ) := rfl
  have hT : lowerTotientMass5 N =
      ∑ p ∈ lowerPairs5 N, 1 / (Nat.totient (p.1 * p.2) : ℝ) := rfl
  have hR : rawRemainder5 B N = ∑ p ∈ lowerPairs5 N, ∑ q ∈ pairModuli5 B N p,
      |(#((primeSequence N).filter (fun a => p.1 * p.2 * q ∣ a)) : ℝ) -
        Wu04.li N / (Nat.totient (p.1 * p.2 * q) : ℝ)| := rfl
  rw [hL, hR, hT]
  rw [hT] at hbudget
  linarith

end LeanLab.ChenDoubleSieve.Task367
