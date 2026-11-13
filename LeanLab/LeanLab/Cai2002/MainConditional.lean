/-
P0044, Y. C. Cai, Chen's theorem with small primes, Acta Math. Sin. 18 (2002), 597 to 604.
The Theorem of pages 597 to 598, stated CONDITIONAL ON its two cited inputs, given as
explicit hypotheses, never as axioms:
- `h6 : LeanLab.ChenExplicit.Theorem6Stmt`, Bordignon, Johnston and Starichkova,
  Theorem 6, pages 4 to 5, https://arxiv.org/abs/2207.09452, the explicit linear sieve,
  the lab leaf `leaf306_theorem6` of Decomp306a.
- `hwu`, the Wu 1993 Lemma 4 statement spelled out, page 599 of Cai, with θ = 0.95, uniform in N
  and in the support, https://doi.org/10.1093/qmath/44.1.109, the statement of the lab
  leaf `leaf337_wu_uniform` of Decomp337b, copied verbatim into a Prop.
The proof is the proof of `main_theorem_wire337` with each lemma on the path from it to
the two leaves copied with the hypotheses added and the leaf constants replaced by them.
No existing statement is changed and nothing is left open here. Every other lemma is used as is.
AI wrote the Lean code. Binary Goldbach is OPEN; this is a Chen type theorem.
-/
import LeanLab.Cai2002.Decomp118Wire

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002



/-- The statement of `leaf337_wu_uniform`, Decomp337b, spelled out instead of being named by
a definition: Wu 1993 Lemma 4, page 599 of Cai, with θ = 0.95, for every product support of
positive integers below N^(2/3), with constants uniform in N and in the support. CITED. This
faithfulness check is a type check on the open leaf; it is not part of the conditional
theorem. -/
theorem wuUniformStmt_of_leaf :
    (∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) := fun A hA => leaf337_wu_uniform A hA

/-- Conditional copy of `cai_upper_q_finite306`, from `Decomp118.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem cai_upper_q_finite306_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ 1 / 100000) :
    ∃ w : ℝ, 3 ≤ w ∧ ∀ N : ℕ, Even N → w < z1 N →
      ∀ q : ℕ, ∀ D : ℝ, z1 N ≤ D →
      let A : Finset ℕ := (caiSequence118 N).filter (fun a => q ∣ a)
      let Q : Finset ℕ := LeanLab.ChenExplicit.primesBelowIn
        {p : ℕ | p.Prime ∧ p.Coprime N} w
      let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
        {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), p
      let s : ℝ := log D / log (z1 N)
      (Asift N 0.95 q).card ≤
        (sieveUpper306 s + ε * 106 * exp 2 * LeanLab.ChenExplicit.hSieve s) * (A.card : ℝ) *
          (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
            {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), (1 - caiDensity118 p)) +
        (∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ p ∈ Q, (p : ℝ)) * D),
          |(((A.filter (fun n : ℕ => d ∣ n)).card : ℝ) -
            (A.card : ℝ) * caiDensity118 d)|) := by
  classical
  obtain ⟨w, hw, hd⟩ := cai_dimension306 ε hε
  refine ⟨w, hw, fun N he hwz q D hD => ?_⟩
  have hA : 0 ∉ (caiSequence118 N).filter (fun a => q ∣ a) := by
    intro h
    exact zero_not_mem_caiSequence118 N (Finset.mem_filter.mp h).1
  have h := theorem6_cardinality306 h6
    ((caiSequence118 N).filter (fun a => q ∣ a)) hA
    {p : ℕ | p.Prime ∧ p.Coprime N} (fun p hp => hp.1)
    (z1 N) (by linarith) caiDensity118 caiDensity118_multiplicative
    (fun p hp => caiDensity118_prime N p he hp.1 hp.2)
    (LeanLab.ChenExplicit.primesBelowIn {p : ℕ | p.Prime ∧ p.Coprime N} w)
    (fun p hp => by
      simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter] at hp
      exact hp.2) ε hε hεmax (hd N he hwz) D
  have hu := h.1 hD
  dsimp only at hu ⊢
  rw [cai_sifted_q_card306 N q] at hu
  exact hu


/-- Conditional copy of `leaf118_sieve_lower`, from `Decomp118.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf118_sieve_lower_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      12.9897 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) ≤
        (Ssift N 0.95 : ℝ) := by
  -- CONDITIONAL ON the single cited finite linear sieve input.
  exact cai_lower_asymptotic306 h6


/-- Conditional copy of `leaf337_one_sieve`, from `Decomp337a.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_one_sieve_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤ (sieveOnePrimeSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  intro δ hδ
  obtain ⟨ε, hε, hεmax, hmainε⟩ := leaf337_one_main_term (δ / 3) (by positivity)
  obtain ⟨w, hw, hupper⟩ := (cai_upper_q_finite306_cond h6 hwu) ε hε hεmax
  obtain ⟨M, hM0, hM⟩ := upper_phi_bound337 ε hε.le
  have hk0 : 0 ≤ ∏ p ∈ oddSievePrimes306 w, (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
  have hk : 0 < 1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ) := by linarith
  obtain ⟨B, hB, nR, hR⟩ := sieve_one_recenter_small337 (δ / 3) (by positivity)
  obtain ⟨nM, hmain⟩ := hmainε B (1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ)) hk
  obtain ⟨nP, hP⟩ := upper_q_param_range337 B (1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ)) hk
  obtain ⟨nD, hD⟩ := sieve_one_mass_small337 (δ / 3 / (M + 1)) (by positivity)
  obtain ⟨nz, hz⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop w))
  refine ⟨max (max (max nR nM) (max nP nD)) (max nz 2), fun N he hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hNR, hNM⟩, hNP, hND⟩, hNz, hN2⟩ := hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hz1 : 1 < z1 N := by
    unfold z1
    exact one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
  obtain ⟨hV0, hV1⟩ := caiV337_bounds N he
  have hwz : w < z1 N := by
    have := hz N hNz
    simpa only [Function.comp_def, z1] using this
  let Qw : Finset ℕ := LeanLab.ChenExplicit.primesBelowIn {p : ℕ | p.Prime ∧ p.Coprime N} w
  let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
    {p : ℕ | p.Prime ∧ p.Coprime N} (z1 N), p
  let kk : ℝ := 1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ)
  let f : ℕ × ℕ → ℝ := fun b =>
    |((((caiSequence118 N).filter (fun a => b.1 ∣ a)).filter (fun a => b.2 ∣ a)).card : ℝ) -
      (((caiSequence118 N).filter (fun a => b.1 ∣ a)).card : ℝ) * caiDensity118 b.2|
  let Rq : ℕ → ℝ := fun q => ∑ d ∈ PP.divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ p ∈ Qw, (p : ℝ)) * upperLevel337 N B kk q), f (q, d)
  have hQw : (∏ p ∈ Qw, (p : ℝ)) ≤ kk := by
    have := sieve_exceptional_product306 w {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => cai_primes_odd306 N p he hp.1 hp.2)
    dsimp only [kk, Qw]
    linarith
  have hper : ∀ q ∈ Q1 N, ((Asift N 0.95 q).card : ℝ) ≤
      upperPhi337 ε (upperParam337 N B kk q) *
          (((caiSequence118 N).card : ℝ) * caiDensity118 q) * caiV337 N +
        M * caiRemainder337 N q + Rq q := by
    intro q hq
    have hqprime : q.Prime := (Finset.mem_filter.mp hq).2.1
    have hqp : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hrange := hP N hNP q hq
    have hDpos : 0 < upperLevel337 N B kk q := by
      unfold upperLevel337
      exact div_pos (div_pos (rpow_pos_of_pos hNp _) (rpow_pos_of_pos hLp _)) (mul_pos hk hqp)
    have hlev : z1 N ≤ upperLevel337 N B kk q := by
      have h1 : 1 ≤ upperParam337 N B kk q := by linarith [hrange.1]
      unfold upperParam337 at h1
      have hlz : 0 < log (z1 N) := log_pos hz1
      rw [le_div_iff₀ hlz, one_mul] at h1
      exact (log_le_log_iff (by linarith) hDpos).mp h1
    have hu := hupper N he hwz q (upperLevel337 N B kk q) hlev
    obtain ⟨hφ0, hφM⟩ := hM _ hrange
    have hr : (((caiSequence118 N).filter (fun a => q ∣ a)).card : ℝ) ≤
        ((caiSequence118 N).card : ℝ) * caiDensity118 q + caiRemainder337 N q := by
      unfold caiRemainder337
      have := le_abs_self ((((caiSequence118 N).filter (fun a => q ∣ a)).card : ℝ) -
        ((caiSequence118 N).card : ℝ) * caiDensity118 q)
      linarith
    have hφV : upperPhi337 ε (upperParam337 N B kk q) * caiV337 N ≤ M := by nlinarith
    have hrem0 : 0 ≤ caiRemainder337 N q := abs_nonneg _
    change ((Asift N 0.95 q).card : ℝ) ≤ upperPhi337 ε (upperParam337 N B kk q) *
      (((caiSequence118 N).filter (fun a => q ∣ a)).card : ℝ) * caiV337 N + Rq q at hu
    nlinarith [mul_le_mul_of_nonneg_left hr (mul_nonneg hφ0 hV0.le),
      mul_le_mul_of_nonneg_right hφV hrem0]
  have hsum : (S1 N 0.95 : ℝ) ≤ ∑ q ∈ Q1 N,
      (upperPhi337 ε (upperParam337 N B kk q) *
          (((caiSequence118 N).card : ℝ) * caiDensity118 q) * caiV337 N +
        M * caiRemainder337 N q + Rq q) := by
    unfold S1
    push_cast
    exact Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- the recentered remainder
  let T : Finset (ℕ × ℕ) := ((Q1 N) ×ˢ PP.divisors).filter
    (fun b : ℕ × ℕ => (b.2 : ℝ) < (∏ p ∈ Qw, (p : ℝ)) * upperLevel337 N B kk b.1)
  have hT : ∑ q ∈ Q1 N, Rq q = ∑ b ∈ T, f b := by
    simp only [T, Rq, Finset.sum_filter, Finset.sum_product]
  have hcN : N.Coprime PP := Nat.coprime_prod_right_iff.mpr (fun p hp => by
    simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter] at hp
    exact hp.2.2.symm)
  have hRT := hR N hNR (z1 N) T (by
    intro b hb
    obtain ⟨hbprod, hblt⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hbprod
    obtain ⟨_, hprime, hqlo, _, hcop⟩ :=
      (show b.1 < N + 1 ∧ b.1.Prime ∧ z1 N ≤ (b.1 : ℝ) ∧ (b.1 : ℝ) < z2 N ∧
          b.1.Coprime N from by simpa only [Q1, mem_filter, mem_range] using hb1)
    have hd0 := Nat.pos_of_mem_divisors hb2
    have hdvd := (Nat.mem_divisors.mp hb2).1
    refine ⟨hprime, hqlo, hd0, ?_, ?_, ?_⟩
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpPP := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
      obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpPP
      simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter,
        Finset.mem_range] at hr
      have hreq : p = r := (Nat.prime_dvd_prime_iff_eq hpp hr.2.1).mp hpr
      have hrlt : r < ⌈z1 N⌉₊ := hr.1
      rw [hreq]
      exact Nat.lt_ceil.mp hrlt
    · apply Nat.le_floor
      push_cast
      apply level_cut337 N hN2 B kk hB.le hk b.1 hprime.pos
      have hDpos : 0 < upperLevel337 N B kk b.1 := by
        unfold upperLevel337
        exact div_pos (div_pos (rpow_pos_of_pos hNp _) (rpow_pos_of_pos hLp _))
          (mul_pos hk (by exact_mod_cast hprime.pos))
      nlinarith [mul_le_mul_of_nonneg_right hQw hDpos.le]
    · exact Nat.Coprime.mul_right hcop.symm (hcN.coprime_dvd_right hdvd))
  have hRsum : ∑ q ∈ Q1 N, Rq q ≤ δ / 3 * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    rw [hT]
    exact hRT
  have hmainN := hmain N he hNM
  have hDN := hD N hND
  have hfrac : M * (δ / 3 / (M + 1)) ≤ δ / 3 := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  have hMY : M * ∑ q ∈ Q1 N, caiRemainder337 N q ≤
      δ / 3 * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    calc M * ∑ q ∈ Q1 N, caiRemainder337 N q ≤
          M * (δ / 3 / (M + 1) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) :=
        mul_le_mul_of_nonneg_left hDN hM0
      _ = (M * (δ / 3 / (M + 1))) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac hK.le
  nlinarith [hsum, hmainN, hRsum, hMY]


/-- Conditional copy of `sieve_one_supply337`, from `Decomp337a.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem sieve_one_supply337_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤
        18.7347 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  apply sieve_upper_of_limit337 (fun N => (S1 N 0.95 : ℝ)) sieveOnePrimeSum337
    sieveOneCoefficient337 18.7347
  · have h : sieveOneCoefficient337 ≤ 18.73465 := eq47_margin118
    linarith
  · exact leaf337_one_prime_sum
  · exact (leaf337_one_sieve_cond h6 hwu)


/-- Conditional copy of `leaf337_two_wu_uniform`, from `Decomp337b.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_two_wu_uniform_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), sw2Wu337 N d) ≤
        K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A := by
  obtain ⟨B, hB, K, hK, N0, h⟩ := hwu A hA
  refine ⟨B, hB, K, hK, max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right ..).trans hN
  apply h N ((le_max_left ..).trans hN) (switchedE118 N)
  intro e he
  obtain ⟨b, hb, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, hp1, hp2, hq1, hq2, _⟩ := (mem_switchedPairs118_iff N b.1 b.2 hN2).mp hb
  have hr := (switched_product_range118 (N : ℝ) b.1 b.2
    (by exact_mod_cast (show 1 < N by omega)) hp1 hp2 hq1 hq2).2
  exact ⟨Nat.mul_pos hx.pos hy.pos, by exact_mod_cast hr⟩


set_option maxHeartbeats 1600000 in
/-- Conditional copy of `leaf337_two_main_term`, from `Decomp337b.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_two_main_term_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100000 ∧ ∀ B k : ℝ, 0 < B → 0 < k →
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        upperPhi337 ε (sw2Param337 N B k) * sw2X337 N * sw2V337 N B ≤
          (sieveTwoPairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  obtain ⟨nP, hPb⟩ := leaf337_two_pair_sum 1 one_pos
  set Pa : ℝ := |sieveTwoCoefficient337 + 1| + 1 with hPa
  have hPa0 : 0 < Pa := by positivity
  set η : ℝ := min (1 / 2) (δ / (15 * Pa)) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηδ : 15 * η * Pa ≤ δ := by
    have h := min_le_right (1 / 2 : ℝ) (δ / (15 * Pa))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hγ : 0 < exp eulerMascheroniConstant := exp_pos _
  set ε : ℝ := min (1 / 100000) (η * exp eulerMascheroniConstant / 106) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 100000 := min_le_left _ _
  have hε2 : ε ≤ η * exp eulerMascheroniConstant / 106 := min_le_right _ _
  refine ⟨ε, hε0, hε1, fun B k hB hk => ?_⟩
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      upperPhi337 ε (sw2Param337 N B k) * sw2X337 N * sw2V337 N B ≤
        (sieveTwoPairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2V_upper337 B hB η hη0 (by linarith), sw2X_upper337 η hη0,
      sw2_level_bounds337 B hB, hlogN.eventually_ge_atTop (16 * (|log k| + 1) / η + 8),
      eventually_ge_atTop nP, eventually_ge_atTop (3 : ℕ)] with N hV hX hLb hlN hNP hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hLp : 0 < log (N : ℝ) := log_pos hN1
    have hC : 0 < C N := by
      unfold C
      exact mul_pos LeanLab.ChenExplicit.twinC_pos
        (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor N))
    set L : ℝ := sw2Level337 N B with hLdef
    have hL1 : 1 < L := lt_of_lt_of_le (one_lt_rpow hN1 (by norm_num)) hLb.1
    have hlogL : log N / 4 ≤ log L := by
      have := log_le_log (rpow_pos_of_pos hNp _) hLb.1
      rw [log_rpow hNp] at this
      linarith
    have hlogLp : 0 < log L := log_pos hL1
    have hsmall : 4 * |log k| ≤ η * log L := by
      have h1 := (div_le_iff₀ hη0).mp (show 16 * (|log k| + 1) / η ≤ log N - 8 by linarith)
      have h2 : η * (log N / 4) ≤ η * log L := mul_le_mul_of_nonneg_left hlogL hη0.le
      nlinarith [abs_nonneg (log k)]
    have hs := sw2_param_eq337 N B k hk hL1
    set s : ℝ := sw2Param337 N B k with hsdef
    have hs_lo : 2 - η / 2 ≤ s := by
      rw [hs]
      have : 2 * log k / log L ≤ η / 2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      linarith
    have hs_hi : s ≤ 2 + η / 2 := by
      rw [hs]
      have : -(η / 2) ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      linarith
    have hs0 : 0 < s := by linarith
    have hs3 : s ≤ 3 := by linarith
    have hF : sieveUpper306 s = 2 * exp eulerMascheroniConstant / s :=
      linear_sieve_formulas306.1 s hs0 hs3
    have hFle : sieveUpper306 s ≤ (1 + η) * exp eulerMascheroniConstant := by
      rw [hF, div_le_iff₀ hs0]
      have : 2 ≤ (1 + η) * s := by nlinarith
      nlinarith
    obtain ⟨hh0, hh1⟩ := hSieve_bounds337 s
    have he2 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
    have hεh : ε * 106 * exp 2 * LeanLab.ChenExplicit.hSieve s ≤ η * exp eulerMascheroniConstant := by
      have h := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ ε * 106 * exp 2 by positivity)
      have : ε * 106 * exp 2 * exp (-2) = ε * 106 := by rw [mul_assoc, he2, mul_one]
      linarith
    have hφ : upperPhi337 ε s ≤ (1 + η) ^ 2 * exp eulerMascheroniConstant := by
      unfold upperPhi337
      nlinarith [mul_pos hη0 hγ]
    have hφ0 : 0 ≤ upperPhi337 ε s := by
      unfold upperPhi337
      have := sieveUpper_pos306 s hs0
      positivity
    obtain ⟨hV0, _⟩ := sw2V_bounds337 N B he
    have hVb := hV he
    -- the pair sum
    set Sp : ℝ := ∑ b ∈ switchedPairs118 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ))) with hSdef
    have hS0 : 0 ≤ Sp := by
      apply Finset.sum_nonneg
      intro b hb
      obtain ⟨hx, hy, hp1, hp2, hq1, hq2, _⟩ := (mem_switchedPairs118_iff N b.1 b.2 hN2).mp hb
      have hr := (switched_product_range118 (N : ℝ) b.1 b.2 hN1 hp1 hp2 hq1 hq2).2
      have hbp : (0 : ℝ) < ((b.1 * b.2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hx.pos hy.pos
      have hle : ((b.1 * b.2 : ℕ) : ℝ) ≤ N := by
        push_cast
        refine hr.le.trans ?_
        simpa using rpow_le_rpow_of_exponent_le hN1.le (by norm_num : (2 / 3 : ℝ) ≤ 1)
      have hl : 0 ≤ log ((N : ℝ) / (b.1 * b.2 : ℕ)) :=
        log_nonneg ((one_le_div hbp).mpr hle)
      positivity
    have hP2 : sieveTwoPairSum337 N = 8 / (2 * (0.95 : ℝ) - 1) * log N * Sp := rfl
    have hP20 : 0 ≤ sieveTwoPairSum337 N := by rw [hP2]; positivity
    have hP2a : sieveTwoPairSum337 N ≤ Pa := by
      have := hPb N hNP
      linarith [le_abs_self (sieveTwoCoefficient337 + 1)]
    set Xb : ℝ := (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * Sp) with hXb
    have hXb0 : 0 ≤ Xb := by positivity
    set Vb : ℝ := (1 + η) * (2 * exp (-eulerMascheroniConstant) * C N / (0.225 * log N))
      with hVbdef
    have step1 : upperPhi337 ε s * sw2X337 N * sw2V337 N B ≤ upperPhi337 ε s * Xb * sw2V337 N B := by
      apply mul_le_mul_of_nonneg_right _ hV0.le
      exact mul_le_mul_of_nonneg_left hX hφ0
    have step2 : upperPhi337 ε s * Xb * sw2V337 N B ≤
        ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hφ hXb0) hVb hV0.le (by positivity)
    have hid : ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb =
        (1 + η) ^ 4 * (sieveTwoPairSum337 N * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) := by
      rw [hXb, hVbdef, hP2, exp_neg]
      field_simp
      ring
    have hpow : (1 + η) ^ 4 ≤ 1 + 15 * η := by
      have q2 : η ^ 2 ≤ η := by nlinarith
      have q3 : η ^ 3 ≤ η := by
        have : η ^ 3 = η ^ 2 * η := by ring
        nlinarith [pow_pos hη0 2]
      have q4 : η ^ 4 ≤ η := by
        have : η ^ 4 = η ^ 3 * η := by ring
        nlinarith [pow_pos hη0 3]
      have : (1 + η) ^ 4 = 1 + 4 * η + 6 * η ^ 2 + 4 * η ^ 3 + η ^ 4 := by ring
      linarith
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    have hfin : (1 + η) ^ 4 * sieveTwoPairSum337 N ≤ sieveTwoPairSum337 N + δ := by
      nlinarith [mul_le_mul_of_nonneg_right hpow hP20, mul_le_mul_of_nonneg_left hP2a hη0.le]
    calc upperPhi337 ε s * sw2X337 N * sw2V337 N B ≤ _ := step1.trans step2
      _ = _ := hid
      _ = ((1 + η) ^ 4 * sieveTwoPairSum337 N) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfin hK.le
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩


set_option maxHeartbeats 1600000 in
/-- Conditional copy of `leaf337_two_switching`, from `Decomp337b.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_two_switching_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedE118 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveTwoPairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  intro δ hδ
  obtain ⟨ε, hε, hεmax, hmainε⟩ := (leaf337_two_main_term_cond h6 hwu) (δ / 4) (by positivity)
  obtain ⟨w, hw, hupper⟩ := switched_upper_finite306 h6 ε hε hεmax
  obtain ⟨M, hM0, hM⟩ := upper_phi_bound337 ε hε.le
  have hk0 : 0 ≤ ∏ p ∈ oddSievePrimes306 w, (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
  set k : ℝ := 1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ) with hkdef
  have hk : 0 < k := by rw [hkdef]; linarith
  obtain ⟨B, hB, Kw, hKw, nW, hW⟩ := (leaf337_two_wu_uniform_cond h6 hwu) 4 (by norm_num)
  obtain ⟨nM, hmain⟩ := hmainε B k hB hk
  obtain ⟨C4, hC4, hC4sum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  obtain ⟨nR, hR2⟩ := sieve_two_R2_small337 (δ / 4) (by positivity)
  obtain ⟨nS, hS⟩ := switched_small_value_loss337 (δ / 4) (by positivity)
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (0.25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  set H : ℝ := Kw * (1 + M + 2 * C4) with hH
  have htw := LeanLab.ChenExplicit.twinC_pos
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      (((switchedClosedIndex337 N (switchedE118 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveTwoPairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2_level_bounds337 B hB,
      hpow.eventually_ge_atTop (max 2 (max (w ^ 2 + 1) (exp (40 * |log k| + 40)))),
      hlogN.eventually_ge_atTop (max 1 (H / (δ / 4 * LeanLab.ChenExplicit.twinC))),
      eventually_ge_atTop nW, eventually_ge_atTop nM, eventually_ge_atTop nR,
      eventually_ge_atTop nS, eventually_ge_atTop (3 : ℕ)]
      with N hLb hpN hlN hNW hNM hNR hNS hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlN1 : 1 ≤ log (N : ℝ) := (le_max_left ..).trans hlN
    have hlNH : H / (δ / 4 * LeanLab.ChenExplicit.twinC) ≤ log (N : ℝ) :=
      (le_max_right ..).trans hlN
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    set K0 : ℝ := C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 with hK0
    set L : ℝ := sw2Level337 N B with hLdef
    have hL2 : 2 ≤ L := le_trans (le_max_left ..) (hpN.trans hLb.1)
    have hLw : w ^ 2 + 1 ≤ L := le_trans ((le_max_left ..).trans (le_max_right ..))
      (hpN.trans hLb.1)
    have hLe : exp (40 * |log k| + 40) ≤ L := le_trans ((le_max_right ..).trans
      (le_max_right ..)) (hpN.trans hLb.1)
    have hlogL : 40 * |log k| + 40 ≤ log L := by
      have := log_le_log (exp_pos _) hLe
      rwa [log_exp] at this
    have hlogLp : 0 < log L := by linarith [abs_nonneg (log k)]
    -- the parameter
    have hs := sw2_param_eq337 N B k hk (by linarith)
    have hsr : sw2Param337 N B k ∈ Set.Icc (1.8 : ℝ) 4.3 := by
      rw [hs]
      have h1 : 2 * log k / log L ≤ 0.2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      have h2 : -0.2 ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      constructor <;> linarith
    obtain ⟨hφ0, hφM⟩ := hM _ hsr
    set z : ℝ := sw2Cut337 N B with hzdef
    have hzw : w < z := by
      rw [hzdef, sw2Cut337, ← hLdef]
      apply Real.lt_sqrt (by linarith) |>.mpr
      linarith
    have hz1 : 1 < z := by linarith
    have hDpos : 0 < L / k := div_pos (by linarith) hk
    have hzD : z ≤ L / k := by
      have h1 : 1 ≤ sw2Param337 N B k := by linarith [hsr.1]
      unfold sw2Param337 at h1
      rw [← hzdef, ← hLdef] at h1
      have hlz : 0 < log z := log_pos hz1
      rw [le_div_iff₀ hlz, one_mul] at h1
      exact (log_le_log_iff (by linarith) hDpos).mp h1
    have hz225 : z ≤ (N : ℝ) ^ (0.225 : ℝ) := by
      rw [hzdef, sw2Cut337, ← hLdef]
      calc Real.sqrt L ≤ Real.sqrt ((N : ℝ) ^ (0.45 : ℝ)) := Real.sqrt_le_sqrt hLb.2
        _ = (N : ℝ) ^ (0.225 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← rpow_mul hNp.le]; norm_num
    have hLN : L ≤ N := by
      refine hLb.2.trans ?_
      simpa using rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N) (by norm_num : (0.45 : ℝ) ≤ 1)
    have hfl : ⌊L⌋₊ ≤ N := by
      have : (⌊L⌋₊ : ℝ) ≤ N := (Nat.floor_le (by linarith)).trans hLN
      exact_mod_cast this
    have hfl1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by norm_num; linarith)
    -- finite losses
    set E := switchedE118 N with hEdef
    set T := switchedIndex306 N E with hTdef
    set PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} z, p with hPP
    have h0 := switched_closed_selection337 N hN2 E Nat.Prime
    have h1 := switched_prime_sift337 N hN2 E {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.1) z
    dsimp only at h1
    have hloss := hS N hNS E (switchedE_card337 N hN2) z hz225
    have hfin : (((switchedClosedIndex337 N E).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
        ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
          (E.card * (⌈z⌉₊ + 1) : ℝ) := by
      have hh : ((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card ≤
          (T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card + E.card * ⌈z⌉₊ + E.card :=
        h0.trans (Nat.add_le_add_right h1 _)
      have hh' : (((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
          ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
            (E.card : ℝ) * (⌈z⌉₊ : ℝ) + (E.card : ℝ) := by exact_mod_cast hh
      linarith
    -- Theorem 6
    have h6 := hupper N he E z hzw (L / k) hzD
    dsimp only at h6
    set Qw : Finset ℕ := LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} w with hQw
    set R : ℕ → ℝ := fun d => |(((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
      (T.card : ℝ) * caiDensity118 d)| with hRdef
    change ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) ≤
      upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B +
        ∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ p ∈ Qw, (p : ℝ)) * (L / k)), R d
      at h6
    have hQk : (∏ p ∈ Qw, (p : ℝ)) ≤ k := by
      have := sieve_exceptional_product306 w {p : ℕ | p.Prime ∧ p.Coprime N}
        (fun p hp => cai_primes_odd306 N p he hp.1 hp.2)
      rw [hkdef]; linarith
    have hcut : (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ L := by
      calc (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ k * (L / k) :=
            mul_le_mul_of_nonneg_right hQk hDpos.le
        _ = L := by field_simp
    have hdiv := sieve_divisor_remainder306 N {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.2) z Qw (L / k) L hcut R (fun _ => abs_nonneg _)
    set U := (Icc 1 ⌊L⌋₊).filter (fun d => N.Coprime d) with hU
    -- remainder pieces
    let nc : ℕ → ℝ := fun d => |∑ e ∈ E.filter (fun e => ¬ e.Coprime d),
      switchedLiTerm337 N e / (d.totient : ℝ)|
    have hwu1 : |(T.card : ℝ) - sw2X337 N| ≤ sw2Wu337 N 1 := by
      have h := switched_remainder_split337 N 1 (Nat.coprime_one_right N) E
      have hT1 : T.filter (fun b => 1 ∣ N - b.1 * b.2) = T :=
        Finset.filter_true_of_mem (fun _ _ => one_dvd _)
      have hE1 : E.filter (fun e => ¬ e.Coprime 1) = ∅ :=
        Finset.filter_false_of_mem (fun e _ => by simp)
      rw [hT1, hE1, Finset.sum_empty, abs_zero, add_zero] at h
      simpa only [sw2Wu337, sw2X337, Nat.totient_one, Nat.cast_one, div_one] using h
    have hRd : ∀ d ∈ U, R d ≤ sw2Wu337 N d + nc d + caiDensity118 d * sw2Wu337 N 1 := by
      intro d hd
      have hc : N.Coprime d := (Finset.mem_filter.mp hd).2
      have h := switched_remainder_split337 N d hc E
      have hg : caiDensity118 d = 1 / (d.totient : ℝ) := rfl
      have hg0 : 0 ≤ caiDensity118 d := by rw [hg]; positivity
      have htri : R d ≤ abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) +
          caiDensity118 d * abs ((T.card : ℝ) - sw2X337 N) := by
        have heq : (((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
            (T.card : ℝ) * caiDensity118 d) =
            ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
              (∑ e ∈ E, switchedLiTerm337 N e) / d.totient) +
            caiDensity118 d * (sw2X337 N - (T.card : ℝ))) := by
          rw [hg]; unfold sw2X337; ring
        change abs _ ≤ _
        rw [heq]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hg0, abs_sub_comm (sw2X337 N)]
      have hmul := mul_le_mul_of_nonneg_left hwu1 hg0
      have h' : abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) ≤ sw2Wu337 N d + nc d := h
      linarith
    have hsumR : (∑ d ∈ U, R d) ≤ (∑ d ∈ U, sw2Wu337 N d) + (∑ d ∈ U, nc d) +
        sw2Wu337 N 1 * ∑ d ∈ U, caiDensity118 d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have := hRd d hd
      linarith
    have hWsum := hW N hNW
    have hnc : (∑ d ∈ U, nc d) ≤ δ / 4 * K0 := by
      refine le_trans ?_ (hR2 N hNR ⌊L⌋₊ hfl)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)
    have hg : (∑ d ∈ U, caiDensity118 d) ≤ C4 * (1 + log N) := by
      have h0 : (∑ d ∈ U, caiDensity118 d) = ∑ d ∈ U, (1 : ℝ) / d.totient := rfl
      have h1 : (∑ d ∈ U, caiDensity118 d) ≤ ∑ d ∈ Icc 1 ⌊L⌋₊, (1 : ℝ) / d.totient := by
        rw [h0]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)
      refine h1.trans ((hC4sum ⌊L⌋₊).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hC4.le
      have : log (⌊L⌋₊ : ℝ) ≤ log N :=
        log_le_log (by exact_mod_cast (show 0 < ⌊L⌋₊ by omega)) (by exact_mod_cast hfl)
      linarith
    have hwu1U : sw2Wu337 N 1 ≤ ∑ d ∈ U, sw2Wu337 N d :=
      Finset.single_le_sum (f := fun d => sw2Wu337 N d) (fun _ _ => abs_nonneg _)
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hfl1⟩, Nat.coprime_one_right N⟩)
    have hwu10 : 0 ≤ sw2Wu337 N 1 := abs_nonneg _
    -- main term
    obtain ⟨hV0, hV1⟩ := sw2V_bounds337 N B he
    have hmainN := hmain N he hNM
    have hTX : (T.card : ℝ) ≤ sw2X337 N + sw2Wu337 N 1 := by
      linarith [le_abs_self ((T.card : ℝ) - sw2X337 N)]
    have hφV : upperPhi337 ε (sw2Param337 N B k) * sw2V337 N B ≤ M := by nlinarith
    have hmain' : upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B ≤
        upperPhi337 ε (sw2Param337 N B k) * sw2X337 N * sw2V337 N B + M * sw2Wu337 N 1 := by
      have h := mul_le_mul_of_nonneg_left hTX (mul_nonneg hφ0 hV0.le)
      nlinarith [mul_le_mul_of_nonneg_right hφV hwu10]
    -- the Wu error total
    set Wsum : ℝ := Kw * (N : ℝ) ^ (0.95 : ℝ) / log N ^ (4 : ℝ) with hWs
    have hWerr : Wsum * (1 + M + C4 * (1 + log N)) ≤ δ / 4 * K0 := by
      have hlp : 0 < log (N : ℝ) := by linarith
      have hW0 : 0 ≤ Wsum := by positivity
      have hfac : 1 + M + C4 * (1 + log N) ≤ (1 + M + 2 * C4) * log N := by nlinarith
      have hHl : H ≤ δ / 4 * LeanLab.ChenExplicit.twinC * log N := by
        have := (div_le_iff₀ (by positivity)).mp hlNH
        linarith
      have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
        unfold C
        exact le_mul_of_one_le_right LeanLab.ChenExplicit.twinC_pos.le
          (LeanLab.ChenExplicit.one_le_oddFactor N)
      calc Wsum * (1 + M + C4 * (1 + log N)) ≤ Wsum * ((1 + M + 2 * C4) * log N) :=
            mul_le_mul_of_nonneg_left hfac hW0
        _ = H * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) := by
            rw [hWs, hH, rpow_ofNat]; field_simp
        _ ≤ (δ / 4 * LeanLab.ChenExplicit.twinC * log N) * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) :=
            mul_le_mul_of_nonneg_right hHl (by positivity)
        _ = δ / 4 * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
            field_simp
        _ ≤ δ / 4 * K0 := by
            rw [hK0]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hC (rpow_pos_of_pos hNp _).le
    have hWsumU : (∑ d ∈ U, sw2Wu337 N d) ≤ Wsum := hWsum
    have hgw : sw2Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * (C4 * (1 + log N)) := by
      have hg0 : 0 ≤ ∑ d ∈ U, caiDensity118 d :=
        Finset.sum_nonneg (fun d _ => by
          change 0 ≤ 1 / (d.totient : ℝ); positivity)
      calc sw2Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * ∑ d ∈ U, caiDensity118 d :=
            mul_le_mul_of_nonneg_right (hwu1U.trans hWsumU) hg0
        _ ≤ Wsum * (C4 * (1 + log N)) :=
            mul_le_mul_of_nonneg_left hg (by rw [hWs]; positivity)
    have hMw : M * sw2Wu337 N 1 ≤ M * Wsum :=
      mul_le_mul_of_nonneg_left (hwu1U.trans hWsumU) hM0
    have hRem := hdiv.trans hsumR
    rw [← hK0] at hmainN hloss
    have : Wsum * (1 + M + C4 * (1 + log N)) =
        Wsum + M * Wsum + Wsum * (C4 * (1 + log N)) := by ring
    linarith [hfin, h6, hRem, hmain', hmainN, hloss, hnc, hWerr, hgw, hMw, hWsumU]
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩


/-- Conditional copy of `sieve_two_supply337`, from `Decomp337b.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem sieve_two_supply337_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S2 N 0.95 : ℝ) ≤
        6.8086 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, h0⟩ := (leaf337_two_switching_cond h6 hwu) 0.00002 (by norm_num)
  obtain ⟨N1, h1⟩ := leaf337_two_pair_sum 0.00002 (by norm_num)
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0N : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1N : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  apply (Nat.cast_le.mpr (sieve_two_closed337 N h2)).trans
  apply (h0 N he h0N).trans
  apply mul_le_mul_of_nonneg_right _ (leaf118_scale_pos N h2).le
  have hc : sieveTwoCoefficient337 ≤ 6.8085 := eq414_margin118
  have := h1 N h1N
  linarith


/-- Conditional copy of `leaf337_three_wu_uniform`, from `Decomp337c.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_three_wu_uniform_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), sw3Wu337 N d) ≤
        K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A := by
  obtain ⟨B, hB, K, hK, N0, h⟩ := hwu A hA
  refine ⟨B, hB, K, hK, max N0 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right ..).trans hN
  apply h N ((le_max_left ..).trans hN) (switchedThreeE306 N)
  intro e he
  exact switchedThreeE_range337 N e hN2 he


set_option maxHeartbeats 1600000 in
/-- Conditional copy of `leaf337_three_main_term`, from `Decomp337c.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_three_main_term_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100000 ∧ ∀ B k : ℝ, 0 < B → 0 < k →
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B ≤
          (sieveThreePairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  obtain ⟨nP, hPb⟩ := leaf337_three_pair_sum 1 one_pos
  set Pa : ℝ := |sieveThreeCoefficient337 + 1| + 1 with hPa
  have hPa0 : 0 < Pa := by positivity
  set η : ℝ := min (1 / 2) (δ / (15 * Pa)) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηδ : 15 * η * Pa ≤ δ := by
    have h := min_le_right (1 / 2 : ℝ) (δ / (15 * Pa))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hγ : 0 < exp eulerMascheroniConstant := exp_pos _
  set ε : ℝ := min (1 / 100000) (η * exp eulerMascheroniConstant / 106) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 100000 := min_le_left _ _
  have hε2 : ε ≤ η * exp eulerMascheroniConstant / 106 := min_le_right _ _
  refine ⟨ε, hε0, hε1, fun B k hB hk => ?_⟩
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B ≤
        (sieveThreePairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2V_upper337 B hB η hη0 (by linarith), sw3X_upper337 η hη0,
      sw2_level_bounds337 B hB, hlogN.eventually_ge_atTop (16 * (|log k| + 1) / η + 8),
      eventually_ge_atTop nP, eventually_ge_atTop (3 : ℕ)] with N hV hX hLb hlN hNP hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hLp : 0 < log (N : ℝ) := log_pos hN1
    have hC : 0 < C N := by
      unfold C
      exact mul_pos LeanLab.ChenExplicit.twinC_pos
        (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor N))
    set L : ℝ := sw2Level337 N B with hLdef
    have hL1 : 1 < L := lt_of_lt_of_le (one_lt_rpow hN1 (by norm_num)) hLb.1
    have hlogL : log N / 4 ≤ log L := by
      have := log_le_log (rpow_pos_of_pos hNp _) hLb.1
      rw [log_rpow hNp] at this
      linarith
    have hlogLp : 0 < log L := log_pos hL1
    have hsmall : 4 * |log k| ≤ η * log L := by
      have h1 := (div_le_iff₀ hη0).mp (show 16 * (|log k| + 1) / η ≤ log N - 8 by linarith)
      have h2 : η * (log N / 4) ≤ η * log L := mul_le_mul_of_nonneg_left hlogL hη0.le
      nlinarith [abs_nonneg (log k)]
    have hs := sw2_param_eq337 N B k hk hL1
    set s : ℝ := sw2Param337 N B k with hsdef
    have hs_lo : 2 - η / 2 ≤ s := by
      rw [hs]
      have : 2 * log k / log L ≤ η / 2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      linarith
    have hs_hi : s ≤ 2 + η / 2 := by
      rw [hs]
      have : -(η / 2) ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      linarith
    have hs0 : 0 < s := by linarith
    have hs3 : s ≤ 3 := by linarith
    have hF : sieveUpper306 s = 2 * exp eulerMascheroniConstant / s :=
      linear_sieve_formulas306.1 s hs0 hs3
    have hFle : sieveUpper306 s ≤ (1 + η) * exp eulerMascheroniConstant := by
      rw [hF, div_le_iff₀ hs0]
      have : 2 ≤ (1 + η) * s := by nlinarith
      nlinarith
    obtain ⟨hh0, hh1⟩ := hSieve_bounds337 s
    have he2 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
    have hεh : ε * 106 * exp 2 * LeanLab.ChenExplicit.hSieve s ≤ η * exp eulerMascheroniConstant := by
      have h := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ ε * 106 * exp 2 by positivity)
      have : ε * 106 * exp 2 * exp (-2) = ε * 106 := by rw [mul_assoc, he2, mul_one]
      linarith
    have hφ : upperPhi337 ε s ≤ (1 + η) ^ 2 * exp eulerMascheroniConstant := by
      unfold upperPhi337
      nlinarith [mul_pos hη0 hγ]
    have hφ0 : 0 ≤ upperPhi337 ε s := by
      unfold upperPhi337
      have := sieveUpper_pos306 s hs0
      positivity
    obtain ⟨hV0, _⟩ := sw2V_bounds337 N B he
    have hVb := hV he
    -- the pair sum
    set Sp : ℝ := ∑ b ∈ switchedThreePairs306 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ))) with hSdef
    have hS0 : 0 ≤ Sp := by
      apply Finset.sum_nonneg
      intro b hb
      have hE : b.1 * b.2 ∈ switchedThreeE306 N := mem_image_of_mem _ hb
      have hr3 := switchedThreeE_range337 N (b.1 * b.2) hN2 hE
      have hbp : (0 : ℝ) < ((b.1 * b.2 : ℕ) : ℝ) := by exact_mod_cast hr3.1
      have hle : ((b.1 * b.2 : ℕ) : ℝ) ≤ N := by
        refine hr3.2.le.trans ?_
        simpa using rpow_le_rpow_of_exponent_le hN1.le (by norm_num : (2 / 3 : ℝ) ≤ 1)
      have hl : 0 ≤ log ((N : ℝ) / (b.1 * b.2 : ℕ)) :=
        log_nonneg ((one_le_div hbp).mpr hle)
      positivity
    have hP2 : sieveThreePairSum337 N = 8 / (2 * (0.95 : ℝ) - 1) * log N * Sp := rfl
    have hP20 : 0 ≤ sieveThreePairSum337 N := by rw [hP2]; positivity
    have hP2a : sieveThreePairSum337 N ≤ Pa := by
      have := hPb N hNP
      linarith [le_abs_self (sieveThreeCoefficient337 + 1)]
    set Xb : ℝ := (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * Sp) with hXb
    have hXb0 : 0 ≤ Xb := by positivity
    set Vb : ℝ := (1 + η) * (2 * exp (-eulerMascheroniConstant) * C N / (0.225 * log N))
      with hVbdef
    have step1 : upperPhi337 ε s * sw3X337 N * sw2V337 N B ≤ upperPhi337 ε s * Xb * sw2V337 N B := by
      apply mul_le_mul_of_nonneg_right _ hV0.le
      exact mul_le_mul_of_nonneg_left hX hφ0
    have step2 : upperPhi337 ε s * Xb * sw2V337 N B ≤
        ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hφ hXb0) hVb hV0.le (by positivity)
    have hid : ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb =
        (1 + η) ^ 4 * (sieveThreePairSum337 N * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) := by
      rw [hXb, hVbdef, hP2, exp_neg]
      field_simp
      ring
    have hpow : (1 + η) ^ 4 ≤ 1 + 15 * η := by
      have q2 : η ^ 2 ≤ η := by nlinarith
      have q3 : η ^ 3 ≤ η := by
        have : η ^ 3 = η ^ 2 * η := by ring
        nlinarith [pow_pos hη0 2]
      have q4 : η ^ 4 ≤ η := by
        have : η ^ 4 = η ^ 3 * η := by ring
        nlinarith [pow_pos hη0 3]
      have : (1 + η) ^ 4 = 1 + 4 * η + 6 * η ^ 2 + 4 * η ^ 3 + η ^ 4 := by ring
      linarith
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    have hfin : (1 + η) ^ 4 * sieveThreePairSum337 N ≤ sieveThreePairSum337 N + δ := by
      nlinarith [mul_le_mul_of_nonneg_right hpow hP20, mul_le_mul_of_nonneg_left hP2a hη0.le]
    calc upperPhi337 ε s * sw3X337 N * sw2V337 N B ≤ _ := step1.trans step2
      _ = _ := hid
      _ = ((1 + η) ^ 4 * sieveThreePairSum337 N) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfin hK.le
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩


set_option maxHeartbeats 1600000 in
/-- Conditional copy of `leaf337_three_switching`, from `Decomp337c.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem leaf337_three_switching_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveThreePairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  intro δ hδ
  obtain ⟨ε, hε, hεmax, hmainε⟩ := (leaf337_three_main_term_cond h6 hwu) (δ / 4) (by positivity)
  obtain ⟨w, hw, hupper⟩ := switched_upper_finite306 h6 ε hε hεmax
  obtain ⟨M, hM0, hM⟩ := upper_phi_bound337 ε hε.le
  have hk0 : 0 ≤ ∏ p ∈ oddSievePrimes306 w, (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
  set k : ℝ := 1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ) with hkdef
  have hk : 0 < k := by rw [hkdef]; linarith
  obtain ⟨B, hB, Kw, hKw, nW, hW⟩ := (leaf337_three_wu_uniform_cond h6 hwu) 4 (by norm_num)
  obtain ⟨nM, hmain⟩ := hmainε B k hB hk
  obtain ⟨C4, hC4, hC4sum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  obtain ⟨nR, hR2⟩ := sieve_three_R2_small337 (δ / 4) (by positivity)
  obtain ⟨nS, hS⟩ := switched_small_value_loss337 (δ / 4) (by positivity)
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (0.25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  set H : ℝ := Kw * (1 + M + 2 * C4) with hH
  have htw := LeanLab.ChenExplicit.twinC_pos
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveThreePairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2_level_bounds337 B hB,
      hpow.eventually_ge_atTop (max 2 (max (w ^ 2 + 1) (exp (40 * |log k| + 40)))),
      hlogN.eventually_ge_atTop (max 1 (H / (δ / 4 * LeanLab.ChenExplicit.twinC))),
      eventually_ge_atTop nW, eventually_ge_atTop nM, eventually_ge_atTop nR,
      eventually_ge_atTop nS, eventually_ge_atTop (3 : ℕ)]
      with N hLb hpN hlN hNW hNM hNR hNS hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlN1 : 1 ≤ log (N : ℝ) := (le_max_left ..).trans hlN
    have hlNH : H / (δ / 4 * LeanLab.ChenExplicit.twinC) ≤ log (N : ℝ) :=
      (le_max_right ..).trans hlN
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    set K0 : ℝ := C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 with hK0
    set L : ℝ := sw2Level337 N B with hLdef
    have hL2 : 2 ≤ L := le_trans (le_max_left ..) (hpN.trans hLb.1)
    have hLw : w ^ 2 + 1 ≤ L := le_trans ((le_max_left ..).trans (le_max_right ..))
      (hpN.trans hLb.1)
    have hLe : exp (40 * |log k| + 40) ≤ L := le_trans ((le_max_right ..).trans
      (le_max_right ..)) (hpN.trans hLb.1)
    have hlogL : 40 * |log k| + 40 ≤ log L := by
      have := log_le_log (exp_pos _) hLe
      rwa [log_exp] at this
    have hlogLp : 0 < log L := by linarith [abs_nonneg (log k)]
    -- the parameter
    have hs := sw2_param_eq337 N B k hk (by linarith)
    have hsr : sw2Param337 N B k ∈ Set.Icc (1.8 : ℝ) 4.3 := by
      rw [hs]
      have h1 : 2 * log k / log L ≤ 0.2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      have h2 : -0.2 ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      constructor <;> linarith
    obtain ⟨hφ0, hφM⟩ := hM _ hsr
    set z : ℝ := sw2Cut337 N B with hzdef
    have hzw : w < z := by
      rw [hzdef, sw2Cut337, ← hLdef]
      apply Real.lt_sqrt (by linarith) |>.mpr
      linarith
    have hz1 : 1 < z := by linarith
    have hDpos : 0 < L / k := div_pos (by linarith) hk
    have hzD : z ≤ L / k := by
      have h1 : 1 ≤ sw2Param337 N B k := by linarith [hsr.1]
      unfold sw2Param337 at h1
      rw [← hzdef, ← hLdef] at h1
      have hlz : 0 < log z := log_pos hz1
      rw [le_div_iff₀ hlz, one_mul] at h1
      exact (log_le_log_iff (by linarith) hDpos).mp h1
    have hz225 : z ≤ (N : ℝ) ^ (0.225 : ℝ) := by
      rw [hzdef, sw2Cut337, ← hLdef]
      calc Real.sqrt L ≤ Real.sqrt ((N : ℝ) ^ (0.45 : ℝ)) := Real.sqrt_le_sqrt hLb.2
        _ = (N : ℝ) ^ (0.225 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← rpow_mul hNp.le]; norm_num
    have hLN : L ≤ N := by
      refine hLb.2.trans ?_
      simpa using rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N) (by norm_num : (0.45 : ℝ) ≤ 1)
    have hfl : ⌊L⌋₊ ≤ N := by
      have : (⌊L⌋₊ : ℝ) ≤ N := (Nat.floor_le (by linarith)).trans hLN
      exact_mod_cast this
    have hfl1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by norm_num; linarith)
    -- finite losses
    set E := switchedThreeE306 N with hEdef
    set T := switchedIndex306 N E with hTdef
    set PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} z, p with hPP
    have h0 := switched_closed_selection337 N hN2 E Nat.Prime
    have h1 := switched_prime_sift337 N hN2 E {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.1) z
    dsimp only at h1
    have hloss := hS N hNS E (switchedThreeE_card337 N hN2) z hz225
    have hfin : (((switchedClosedIndex337 N E).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
        ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
          (E.card * (⌈z⌉₊ + 1) : ℝ) := by
      have hh : ((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card ≤
          (T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card + E.card * ⌈z⌉₊ + E.card :=
        h0.trans (Nat.add_le_add_right h1 _)
      have hh' : (((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
          ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
            (E.card : ℝ) * (⌈z⌉₊ : ℝ) + (E.card : ℝ) := by exact_mod_cast hh
      linarith
    -- Theorem 6
    have h6 := hupper N he E z hzw (L / k) hzD
    dsimp only at h6
    set Qw : Finset ℕ := LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} w with hQw
    set R : ℕ → ℝ := fun d => |(((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
      (T.card : ℝ) * caiDensity118 d)| with hRdef
    change ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) ≤
      upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B +
        ∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ p ∈ Qw, (p : ℝ)) * (L / k)), R d
      at h6
    have hQk : (∏ p ∈ Qw, (p : ℝ)) ≤ k := by
      have := sieve_exceptional_product306 w {p : ℕ | p.Prime ∧ p.Coprime N}
        (fun p hp => cai_primes_odd306 N p he hp.1 hp.2)
      rw [hkdef]; linarith
    have hcut : (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ L := by
      calc (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ k * (L / k) :=
            mul_le_mul_of_nonneg_right hQk hDpos.le
        _ = L := by field_simp
    have hdiv := sieve_divisor_remainder306 N {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.2) z Qw (L / k) L hcut R (fun _ => abs_nonneg _)
    set U := (Icc 1 ⌊L⌋₊).filter (fun d => N.Coprime d) with hU
    -- remainder pieces
    let nc : ℕ → ℝ := fun d => |∑ e ∈ E.filter (fun e => ¬ e.Coprime d),
      switchedLiTerm337 N e / (d.totient : ℝ)|
    have hwu1 : |(T.card : ℝ) - sw3X337 N| ≤ sw3Wu337 N 1 := by
      have h := switched_remainder_split337 N 1 (Nat.coprime_one_right N) E
      have hT1 : T.filter (fun b => 1 ∣ N - b.1 * b.2) = T :=
        Finset.filter_true_of_mem (fun _ _ => one_dvd _)
      have hE1 : E.filter (fun e => ¬ e.Coprime 1) = ∅ :=
        Finset.filter_false_of_mem (fun e _ => by simp)
      rw [hT1, hE1, Finset.sum_empty, abs_zero, add_zero] at h
      simpa only [sw3Wu337, sw3X337, Nat.totient_one, Nat.cast_one, div_one] using h
    have hRd : ∀ d ∈ U, R d ≤ sw3Wu337 N d + nc d + caiDensity118 d * sw3Wu337 N 1 := by
      intro d hd
      have hc : N.Coprime d := (Finset.mem_filter.mp hd).2
      have h := switched_remainder_split337 N d hc E
      have hg : caiDensity118 d = 1 / (d.totient : ℝ) := rfl
      have hg0 : 0 ≤ caiDensity118 d := by rw [hg]; positivity
      have htri : R d ≤ abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) +
          caiDensity118 d * abs ((T.card : ℝ) - sw3X337 N) := by
        have heq : (((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
            (T.card : ℝ) * caiDensity118 d) =
            ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
              (∑ e ∈ E, switchedLiTerm337 N e) / d.totient) +
            caiDensity118 d * (sw3X337 N - (T.card : ℝ))) := by
          rw [hg]; unfold sw3X337; ring
        change abs _ ≤ _
        rw [heq]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hg0, abs_sub_comm (sw3X337 N)]
      have hmul := mul_le_mul_of_nonneg_left hwu1 hg0
      have h' : abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) ≤ sw3Wu337 N d + nc d := h
      linarith
    have hsumR : (∑ d ∈ U, R d) ≤ (∑ d ∈ U, sw3Wu337 N d) + (∑ d ∈ U, nc d) +
        sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have := hRd d hd
      linarith
    have hWsum := hW N hNW
    have hnc : (∑ d ∈ U, nc d) ≤ δ / 4 * K0 := by
      refine le_trans ?_ (hR2 N hNR ⌊L⌋₊ hfl)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)
    have hg : (∑ d ∈ U, caiDensity118 d) ≤ C4 * (1 + log N) := by
      have h0 : (∑ d ∈ U, caiDensity118 d) = ∑ d ∈ U, (1 : ℝ) / d.totient := rfl
      have h1 : (∑ d ∈ U, caiDensity118 d) ≤ ∑ d ∈ Icc 1 ⌊L⌋₊, (1 : ℝ) / d.totient := by
        rw [h0]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)
      refine h1.trans ((hC4sum ⌊L⌋₊).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hC4.le
      have : log (⌊L⌋₊ : ℝ) ≤ log N :=
        log_le_log (by exact_mod_cast (show 0 < ⌊L⌋₊ by omega)) (by exact_mod_cast hfl)
      linarith
    have hwu1U : sw3Wu337 N 1 ≤ ∑ d ∈ U, sw3Wu337 N d :=
      Finset.single_le_sum (f := fun d => sw3Wu337 N d) (fun _ _ => abs_nonneg _)
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hfl1⟩, Nat.coprime_one_right N⟩)
    have hwu10 : 0 ≤ sw3Wu337 N 1 := abs_nonneg _
    -- main term
    obtain ⟨hV0, hV1⟩ := sw2V_bounds337 N B he
    have hmainN := hmain N he hNM
    have hTX : (T.card : ℝ) ≤ sw3X337 N + sw3Wu337 N 1 := by
      linarith [le_abs_self ((T.card : ℝ) - sw3X337 N)]
    have hφV : upperPhi337 ε (sw2Param337 N B k) * sw2V337 N B ≤ M := by nlinarith
    have hmain' : upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B ≤
        upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B + M * sw3Wu337 N 1 := by
      have h := mul_le_mul_of_nonneg_left hTX (mul_nonneg hφ0 hV0.le)
      nlinarith [mul_le_mul_of_nonneg_right hφV hwu10]
    -- the Wu error total
    set Wsum : ℝ := Kw * (N : ℝ) ^ (0.95 : ℝ) / log N ^ (4 : ℝ) with hWs
    have hWerr : Wsum * (1 + M + C4 * (1 + log N)) ≤ δ / 4 * K0 := by
      have hlp : 0 < log (N : ℝ) := by linarith
      have hW0 : 0 ≤ Wsum := by positivity
      have hfac : 1 + M + C4 * (1 + log N) ≤ (1 + M + 2 * C4) * log N := by nlinarith
      have hHl : H ≤ δ / 4 * LeanLab.ChenExplicit.twinC * log N := by
        have := (div_le_iff₀ (by positivity)).mp hlNH
        linarith
      have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
        unfold C
        exact le_mul_of_one_le_right LeanLab.ChenExplicit.twinC_pos.le
          (LeanLab.ChenExplicit.one_le_oddFactor N)
      calc Wsum * (1 + M + C4 * (1 + log N)) ≤ Wsum * ((1 + M + 2 * C4) * log N) :=
            mul_le_mul_of_nonneg_left hfac hW0
        _ = H * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) := by
            rw [hWs, hH, rpow_ofNat]; field_simp
        _ ≤ (δ / 4 * LeanLab.ChenExplicit.twinC * log N) * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) :=
            mul_le_mul_of_nonneg_right hHl (by positivity)
        _ = δ / 4 * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
            field_simp
        _ ≤ δ / 4 * K0 := by
            rw [hK0]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hC (rpow_pos_of_pos hNp _).le
    have hWsumU : (∑ d ∈ U, sw3Wu337 N d) ≤ Wsum := hWsum
    have hgw : sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * (C4 * (1 + log N)) := by
      have hg0 : 0 ≤ ∑ d ∈ U, caiDensity118 d :=
        Finset.sum_nonneg (fun d _ => by
          change 0 ≤ 1 / (d.totient : ℝ); positivity)
      calc sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * ∑ d ∈ U, caiDensity118 d :=
            mul_le_mul_of_nonneg_right (hwu1U.trans hWsumU) hg0
        _ ≤ Wsum * (C4 * (1 + log N)) :=
            mul_le_mul_of_nonneg_left hg (by rw [hWs]; positivity)
    have hMw : M * sw3Wu337 N 1 ≤ M * Wsum :=
      mul_le_mul_of_nonneg_left (hwu1U.trans hWsumU) hM0
    have hRem := hdiv.trans hsumR
    rw [← hK0] at hmainN hloss
    have : Wsum * (1 + M + C4 * (1 + log N)) =
        Wsum + M * Wsum + Wsum * (C4 * (1 + log N)) := by ring
    linarith [hfin, h6, hRem, hmain', hmainN, hloss, hnc, hWerr, hgw, hMw, hWsumU]
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩


/-- Conditional copy of `sieve_three_supply337`, from `Decomp337c.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem sieve_three_supply337_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, h0⟩ := (leaf337_three_switching_cond h6 hwu) 0.00001 (by norm_num)
  obtain ⟨N1, h1⟩ := leaf337_three_pair_sum 0.00001 (by norm_num)
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0N : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1N : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  apply (Nat.cast_le.mpr (sieve_three_closed337 N h2)).trans
  apply (h0 N he h0N).trans
  apply mul_le_mul_of_nonneg_right _ (leaf118_scale_pos N h2).le
  have hc : sieveThreeCoefficient337 ≤ 0.15635 := eq415_margin118
  have := h1 N h1N
  linarith


/-- Conditional copy of `main_theorem_wire337`, from `Decomp118Wire.lean`, with the two cited inputs as
hypotheses `h6` and `hwu`. The proof is the original proof with the cited constants
replaced by the hypotheses. -/
theorem main_theorem_wire337_cond
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) : MainTheorem := by
  obtain ⟨n0, h0⟩ := leaf118_loss
  obtain ⟨n1, h1⟩ := (leaf118_sieve_lower_cond h6 hwu)
  obtain ⟨n2, h2⟩ := (sieve_one_supply337_cond h6 hwu)
  obtain ⟨n3, h3⟩ := (sieve_two_supply337_cond h6 hwu)
  obtain ⟨n4, h4⟩ := (sieve_three_supply337_cond h6 hwu)
  refine ⟨max 177147 (max n0 (max n1 (max n2 (max n3 n4)))), ?_⟩
  intro N he hN
  have hcut : 177147 ≤ N := (le_max_left ..).trans hN
  have hrest := (le_max_right ..).trans hN
  have hn0 : n0 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn1 : n1 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn2 : n2 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn3 : n3 ≤ N := (le_max_left ..).trans hrest
  have hn4 : n4 ≤ N := (le_max_right ..).trans hrest
  have hp := leaf118_scale_pos N (by omega)
  have hw := leaf118_weighted N hcut
  have hl := h0 N hn0
  have hs := h1 N he hn1
  have hs1 := h2 N he hn2
  have hs2 := h3 N he hn3
  have hs3 := h4 N he hn4
  have htarget :
      0.01 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) < (S N 0.95 : ℝ) := by
    linarith
  simpa only [mul_div_assoc, mul_assoc] using htarget

/-- P0044, the Theorem of pages 597 to 598, CONDITIONAL ON the two cited inputs:
BJS Theorem 6 as `h6` and Wu 1993 Lemma 4 in the uniform form as `hwu`.
`MainTheorem` is the lab statement of Statements.lean, unchanged. -/
theorem cai2002_main_theorem_conditional
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hwu :
    ∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) : MainTheorem :=
  main_theorem_wire337_cond h6 hwu


end LeanLab.Cai2002
