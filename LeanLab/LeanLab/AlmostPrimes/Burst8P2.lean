/-
ROUTE BURST session 8, 2026-11-12, part 2 of the AlmostPrimes split.

Paper P0019: D. R. Johnston, V. V. Starichkova, Some explicit results on the sum of a prime and an
almost prime, arXiv 2208.01229 v3. Second paper, reference [19] of P0019: S. Hathi,
D. R. Johnston, On the sum of a prime and a square-free number with divisibility conditions,
arXiv 2109.11883 v2.

AI wrote this Lean code. Binary Goldbach is OPEN.

This file splits two sorry leaves of `Burst4Split` further along the papers' own proofs, and
proves the top theorem again from the finer leaves.

* `leaf_hathi_johnston` from [19]: Theorem 1.5 at k = 30030 is Theorem 5.2 of [19], p. 11.
  Its proof has two ranges. For n ≥ 4 · 10^18, Lemma 5.1 of [19], p. 10, with C = 0.2 gives
  R_k(n) > 0, cited leaf `hj_large_R_pos`. For n < 4 · 10^18 it uses the Goldbach
  verification, here the existing cited leaf `leaf_goldbach_4e18`; the elementary step that a
  Goldbach pair for n ≥ 40 has a prime part above 13 is PROVED as `hj_small`.
* `leaf_theorem42_positive`: Theorem 4.2 of P0019, pp. 11 and 12, evaluated on p. 13, has the
  form S(A, P(z)) > M |A| U_N / log N · B with M B ≥ 5 in both cases. That bound is the cited
  deep leaf `theorem42_bracket`, taking as hypothesis the conditions (4.3) at the parameters
  of p. 13. The conditions are PROVED here for every N ≥ X₂, and U_N > 0 is PROVED, so
  positivity follows. Lemma 3.1, |A| > N / log N, is PROVED for N ≥ X₂ CONDITIONAL ON
  Rosser and Schoenfeld 1962, and with it the display S > 5 U_N N / log² N of p. 13.
* QUESTION, recorded and proved in Lean as `loglog_x1_X2_lt`: Theorem 4.2 also assumes
  log log x₁(X₂) ≥ Y₀ = 7.9, which fails at X₂ = exp(exp 7.9), where it equals
  log(e^{7.9} − 39.5) < 7.9. The leaf `theorem42_bracket` is therefore the paper's claim on
  p. 13, not an instance of Theorem 4.2 as printed.
-/
import Mathlib
import LeanLab.AlmostPrimes.Burst4Split

namespace LeanLab.AlmostPrimes.Burst8P2

open LeanLab LeanLab.AlmostPrimes LeanLab.AlmostPrimes.Burst4Split Finset

/-! ### Part 1. Hathi and Johnston, Theorem 1.5 at k = 30030 -/

open Classical in
/-- R_k(n) of [19], Section 2, p. 3: ∑_{p ≤ n, (n − p, k) = 1} μ²(n − p) log p, with
μ²(m) = 1 exactly when m is square-free; μ²(0) = 0. -/
noncomputable def hjR (k n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ Nat.Coprime (n - p) k),
    (if Squarefree (n - p) then (1 : ℝ) else 0) * Real.log p

/-- PROVED. [19], p. 3: R_k(n) counts representations n = p + η with η square-free and
coprime to k, so R_k(n) > 0 gives one. -/
theorem hj_rep_of_R_pos (k n : ℕ) (h : 0 < hjR k n) :
    ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η k ∧ n = p + η := by
  classical
  unfold hjR at h
  by_contra hne
  push Not at hne
  have : ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ Nat.Coprime (n - p) k),
      (if Squarefree (n - p) then (1 : ℝ) else 0) * Real.log p ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpn, hpr, hcop⟩ := hp
    by_cases hsq : Squarefree (n - p)
    · exact absurd (by omega : n = p + (n - p)) (hne p (n - p) hpr hsq hcop)
    · simp [hsq]
  linarith

/-- LEAF: cited. [19] Lemma 5.1, p. 10, and the proof of Theorem 5.2, p. 11, at the even
square-free k = 30030 = 2 · 3 · 5 · 7 · 11 · 13 ≤ 2 · 10^5 with C = 0.2: the right side of
(5.2) is positive, so R_k(n) > 0 for every even n ≥ 4 · 10^18. -/
theorem hj_large_R_pos : ∀ n : ℕ, Even n → 4 * 10 ^ 18 ≤ n → 0 < hjR 30030 n := by
  -- BLOCKED 2026-11-13 FREE-ms-leanstral task378 hj_large_R_pos: Friedlander-Iwaniec type sieve bound; 500-1000 lines, not in Mathlib
  intro n hE hle
  sorry

/-- A prime not dividing 30030 is coprime to it. -/
theorem coprime_30030_of_prime {q : ℕ} (hq : q.Prime) (h : 13 < q) : Nat.Coprime q 30030 := by
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  have h1 : 30030 = 2 * (3 * (5 * (7 * (11 * 13)))) := by norm_num
  rw [h1] at hd
  rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | hd
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | hd
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | hd
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | hd
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | h2
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)

/-- PROVED from the cited Goldbach leaf. Proof of Theorem 5.2 of [19], p. 11, small range: for
even 40 ≤ n ≤ 4 · 10^18, n = q₁ + q₂ with both prime; one of them exceeds 13, so it does not
divide k = 30030 and is a square-free η coprime to k. -/
theorem hj_small (n : ℕ) (hE : Even n) (h40 : 40 ≤ n) (hn : n ≤ 4 * 10 ^ 18) :
    ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η 30030 ∧ n = p + η := by
  obtain ⟨p, q, hp, hq, hpq⟩ := leaf_goldbach_4e18 n hE (by omega) hn
  by_cases hq13 : 13 < q
  · exact ⟨p, q, hp, hq.squarefree, coprime_30030_of_prime hq hq13, hpq.symm⟩
  · exact ⟨q, p, hq, hp.squarefree, coprime_30030_of_prime hp (by omega), by omega⟩

/-- The leaf `Burst4Split.leaf_hathi_johnston`, same statement, PROVED from the two finer
leaves `hj_large_R_pos` and `leaf_goldbach_4e18`. [19] Theorem 1.5 at k = 30030. -/
theorem leaf_hathi_johnston_p2 : ∀ N : ℕ, Even N → 40 ≤ N →
    ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η 30030 ∧ N = p + η := by
  intro N hE h40
  by_cases hs : N ≤ 4 * 10 ^ 18
  · exact hj_small N hE h40 hs
  · exact hj_rep_of_R_pos 30030 N (hj_large_R_pos N hE (by omega))

/-! ### Part 2. The constant U_N, Section 2, p. 4 of P0019 -/

/-- The factor of the twin prime product at n: 1 − 1/(n − 1)² for primes n > 2, else 1,
written as 1 + f(n). -/
noncomputable def twinTerm (n : ℕ) : ℝ :=
  if n.Prime ∧ 2 < n then -(1 / ((n : ℝ) - 1) ^ 2) else 0

/-- ∏_{p > 2} (1 − 1/(p − 1)²), Section 2, p. 4. -/
noncomputable def twinProd : ℝ := ∏' n : ℕ, (1 + twinTerm n)

/-- U_N = 2 e^{−γ} ∏_{p>2} (1 − 1/(p − 1)²) ∏_{p > 2, p ∣ N} (p − 1)/(p − 2), Section 2,
p. 4 of P0019. -/
noncomputable def UN (N : ℕ) : ℝ :=
  2 * Real.exp (-Real.eulerMascheroniConstant) * twinProd *
    ∏ p ∈ N.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))

theorem twinTerm_bound (n : ℕ) : |twinTerm n| ≤ 4 * (1 / (n : ℝ) ^ 2) := by
  unfold twinTerm
  split_ifs with h
  · have hn : (3 : ℝ) ≤ n := by exact_mod_cast h.2
    have h1 : 0 < (n : ℝ) - 1 := by linarith
    have h2 : (n : ℝ) ^ 2 ≤ 4 * ((n : ℝ) - 1) ^ 2 := by nlinarith
    rw [abs_neg, abs_of_pos (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = 4 * (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / 4) := by
          field_simp
      _ ≤ 4 * (1 / (n : ℝ) ^ 2) * ((n : ℝ) - 1) ^ 2 := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · simp

theorem twinTerm_summable : Summable twinTerm := by
  refine Summable.of_norm_bounded ?_ (fun n => twinTerm_bound n)
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left 4

theorem one_add_twinTerm_pos (n : ℕ) : 0 < 1 + twinTerm n := by
  unfold twinTerm
  split_ifs with h
  · have hn : (3 : ℝ) ≤ n := by exact_mod_cast h.2
    have h1 : 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    linarith
  · norm_num

/-- PROVED. The twin prime product ∏_{p>2} (1 − 1/(p − 1)²) is positive. -/
theorem twinProd_pos : 0 < twinProd := by
  unfold twinProd
  rw [← Real.rexp_tsum_eq_tprod one_add_twinTerm_pos
    (Real.summable_log_one_add_of_summable twinTerm_summable)]
  exact Real.exp_pos _

/-- PROVED. U_N > 0, Section 2, p. 4. -/
theorem UN_pos (N : ℕ) : 0 < UN N := by
  unfold UN
  have hprod : 0 < ∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_pos
    intro p hp
    rw [mem_filter] at hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    apply div_pos <;> linarith
  have := twinProd_pos
  positivity

/-! ### Part 3. Theorem 4.2 of P0019 at the parameters of p. 13 -/

/-- x₁(N) = N / log⁵ N, Section 2, p. 2. -/
noncomputable def x1 (x : ℝ) : ℝ := x / Real.log x ^ 5

/-- L₀ = log X₂ = e^{7.9}. -/
noncomputable def L0 : ℝ := Real.exp 7.9

theorem log_X2 : Real.log X2v3 = L0 := by
  unfold X2v3 L0; rw [Real.log_exp]

theorem L0_ge : (2000 : ℝ) ≤ L0 := by
  unfold L0
  have h1 := Real.exp_one_gt_d9
  have h7 : Real.exp 7.9 = Real.exp 1 ^ 7 * Real.exp 0.9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h9 : (1.9 : ℝ) ≤ Real.exp 0.9 := by
    have := Real.add_one_le_exp (0.9 : ℝ); linarith
  have hp : (2.718 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 7
  rw [h7]
  nlinarith [Real.exp_pos 0.9]

/-- QUESTION, PROVED. Theorem 4.2, p. 11, assumes log log x₁(X₂) ≥ Y₀, and the proof of
Theorem 1.3, p. 13, takes Y₀ = 7.9 by (4.6) and X₂ = exp(exp 7.9). But
log log x₁(X₂) = log(e^{7.9} − 39.5) < 7.9, so that hypothesis fails at the printed X₂. -/
theorem loglog_x1_X2_lt : Real.log (Real.log (x1 X2v3)) < 7.9 := by
  have hX : 0 < X2v3 := Real.exp_pos _
  have hL := L0_ge
  have hlx : Real.log (x1 X2v3) = L0 - 39.5 := by
    unfold x1
    rw [Real.log_div hX.ne' (by rw [log_X2]; positivity), Real.log_pow, log_X2]
    unfold L0; rw [Real.log_exp]; norm_num
  rw [hlx]
  have : Real.log (L0 - 39.5) < Real.log L0 :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold L0 at this ⊢; rw [Real.log_exp] at this; exact this

/-- The conditions (4.3) of Theorem 4.2, p. 11, that depend on N, at the parameters of the
proof of Theorem 1.3, p. 13: α₁ = 7, ξ(z₀, M) ≤ 801, u₀ = 400, α = 0.25, M = 40, δ = 1.3,
z = N^{1/40}, K_δ(x₁) = log^δ x₁ by (2.1). -/
def Conditions43 (N : ℕ) : Prop :=
  Real.log (N : ℝ) ^ 7 ≤ x1 N ^ ((1 : ℝ) / 2) / Real.log (x1 N) ^ 7 ∧
  (10 : ℝ) ^ 9 ≤ Real.log (N : ℝ) ^ 7 ∧
  0 ≤ 1 - 801 / Real.log (N : ℝ) ^ 2 ∧
  Real.exp (400 * (1 + 9e-7 / Real.log 400)) ≤
    (N : ℝ) ^ (0.25 : ℝ) / (Real.log (x1 N) ^ 7 * Real.log (N : ℝ) ^ (2.5 : ℝ)) ∧
  ((N : ℝ) ^ ((1 : ℝ) / 40)) ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 0.25) / Real.log (N : ℝ) ^ 14 ∧
  (3022 : ℝ) ≤ Real.log (x1 N) ^ (1.3 : ℝ)

/-- The parameter conditions of (4.3) not depending on N: X₂ ≥ 4 · 10^18 and ε ≤ 1/74 with
ε = ε(400, 10^{12}) = 5.543 · 10^{-4} from (3.8). -/
def ParamConditions43 : Prop := (4 : ℝ) * 10 ^ 18 ≤ X2v3 ∧ (5.543e-4 : ℝ) ≤ 1 / 74

/-- LEAF: cited and deep. P0019, Theorem 4.2, p. 11 and 12, as evaluated in the proof of
Theorem 1.3, p. 13, with (Y₀, α₁, α₂, C) = (7.9, 7, 2, 3.98), u₀ = 400, δ = 1.3, α = 0.25,
M = 40, ε = 5.543 · 10^{-4}, C₁(ε) = 113, C₂(ε) = 114, ξ ≤ 801 and ε₁(X₂, δ) = 1/11.
In both cases Theorem 4.2 has the form S(A, P(z)) > M |A| U_N / log N · B with a bracket B;
the paper's values S > 38 U_N N / log² N for k₁ < K_δ(x₁) and S > 5 U_N N / log² N for
k₁ ≥ K_δ(x₁), obtained with |A| > N / log N after first verifying S > 0, mean M B ≥ 38 and
M B ≥ 5. This leaf states the smaller one, S(A, P(z)) > 5 |A| U_N / log N, for every even
N ≥ X₂ with z = N^{1/40}, under the conditions (4.3) that this file proves. See
`loglog_x1_X2_lt` for the condition on Y₀. -/
theorem theorem42_bracket (hpar : ParamConditions43)
    (hcond : ∀ N : ℕ, Even N → X2v3 ≤ (N : ℝ) → Conditions43 N) :
    ∀ N : ℕ, Even N → X2v3 ≤ (N : ℝ) →
      5 * ((setA N).card : ℝ) * UN N / Real.log (N : ℝ) <
        ((siftedSet N ((N : ℝ) ^ ((1 : ℝ) / 40))).card : ℝ) := by
  intro N hE hX
  sorry

/-- PROVED. X₂ ≥ 4 · 10^18 and ε ≤ 1/74. -/
theorem paramConditions43 : ParamConditions43 := by
  refine ⟨?_, by norm_num⟩
  unfold X2v3
  have h1 := Real.exp_one_gt_d9
  have hL : (64 : ℝ) ≤ Real.exp 7.9 := by
    have := L0_ge; unfold L0 at this; linarith
  calc (4 : ℝ) * 10 ^ 18 ≤ 2 ^ 64 := by norm_num
    _ ≤ Real.exp 1 ^ 64 := pow_le_pow_left₀ (by norm_num) (by linarith) 64
    _ = Real.exp 64 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (Real.exp 7.9) := Real.exp_le_exp.mpr hL

/-- For L ≥ L₀: log L ≤ 6.9 + L/2000. -/
theorem log_le_of_ge_L0 {L : ℝ} (hL : L0 ≤ L) : Real.log L ≤ 6.9 + L / 2000 := by
  have h0 := L0_ge
  have hpos : 0 < L0 := by linarith
  have hsplit : Real.log L = Real.log L0 + Real.log (L / L0) := by
    rw [Real.log_div (by linarith) hpos.ne']; ring
  have hl0 : Real.log L0 = 7.9 := by unfold L0; rw [Real.log_exp]
  have hq : Real.log (L / L0) ≤ L / L0 - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) hpos)
  have hq2 : L / L0 ≤ L / 2000 := div_le_div_of_nonneg_left (by linarith) (by norm_num) h0
  linarith

/-- The facts used for the conditions: with L = log N ≥ L₀, N = e^L and
log x₁(N) = L − 5 log L. -/
theorem log_x1_eq {N : ℝ} (hN : 0 < N) (hL : 0 < Real.log N) :
    Real.log (x1 N) = Real.log N - 5 * Real.log (Real.log N) := by
  unfold x1
  rw [Real.log_div hN.ne' (by positivity), Real.log_pow]; push_cast; ring

theorem rpow_eq_exp {N : ℝ} (hN : 0 < N) (r : ℝ) : N ^ r = Real.exp (r * Real.log N) := by
  rw [Real.rpow_def_of_pos hN, mul_comm]

theorem pow_eq_exp {L : ℝ} (hL : 0 < L) (k : ℕ) : L ^ k = Real.exp (k * Real.log L) := by
  rw [← Real.rpow_natCast, rpow_eq_exp hL]

/-- PROVED. The conditions (4.3) hold for every N ≥ X₂ = exp(exp 7.9). -/
theorem conditions43 (N : ℕ) (hX : X2v3 ≤ (N : ℝ)) : Conditions43 N := by
  have hX0 : 0 < X2v3 := Real.exp_pos _
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hX0 hX
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : L0 ≤ L := by rw [← log_X2]; exact Real.log_le_log hX0 hX
  have h2000 := L0_ge
  have hL : 2000 ≤ L := le_trans h2000 hL0
  have hLpos : 0 < L := by linarith
  have hlogL := log_le_of_ge_L0 hL0
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set Lx := Real.log (x1 N) with hLxdef
  have hLx : Lx = L - 5 * Real.log L := log_x1_eq hN hLpos
  have hLx_lo : 0.9975 * L - 34.5 ≤ Lx := by rw [hLx]; linarith
  have hLx_hi : Lx ≤ L := by rw [hLx]; linarith
  have hLxpos : 0 < Lx := by linarith
  have hx1 : 0 < x1 N := by unfold x1; positivity
  have hNexp : (N : ℝ) = Real.exp L := (Real.exp_log hN).symm
  have hx1exp : x1 N = Real.exp Lx := (Real.exp_log hx1).symm
  -- L^7 Lx^7 ≤ L^14 = exp(14 log L)
  have hLx7 : Lx ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ hLxpos.le hLx_hi 7
  have hL7pos : 0 < Lx ^ 7 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- √x₁ / log⁷ x₁ ≥ log⁷ N
    rw [le_div_iff₀ hL7pos, rpow_eq_exp hx1, ← hLxdef]
    calc L ^ 7 * Lx ^ 7 ≤ L ^ 7 * L ^ 7 :=
          mul_le_mul_of_nonneg_left hLx7 (by positivity)
      _ = L ^ 14 := by ring
      _ = Real.exp (14 * Real.log L) := by rw [pow_eq_exp hLpos]; norm_num
      _ ≤ Real.exp (1 / 2 * Lx) := Real.exp_le_exp.mpr (by linarith)
  · calc (10 : ℝ) ^ 9 ≤ 2000 ^ 7 := by norm_num
      _ ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
  · rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  · -- N^{1/4} / (log⁷ x₁ log^{2.5} N) ≥ exp(400 (1 + 9e-7 / log 400))
    have hl400 : 1 ≤ Real.log 400 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    have hu : 400 * (1 + 9e-7 / Real.log 400) ≤ 401 := by
      have : 9e-7 / Real.log 400 ≤ 9e-7 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hL25 : L ^ (2.5 : ℝ) = Real.exp (2.5 * Real.log L) := rpow_eq_exp hLpos _
    rw [le_div_iff₀ (by positivity), rpow_eq_exp hN, ← hLdef, hL25]
    calc Real.exp (400 * (1 + 9e-7 / Real.log 400)) * (Lx ^ 7 * Real.exp (2.5 * Real.log L))
        ≤ Real.exp 401 * (L ^ 7 * Real.exp (2.5 * Real.log L)) := by
          apply mul_le_mul (Real.exp_le_exp.mpr hu)
            (mul_le_mul_of_nonneg_right hLx7 (Real.exp_pos _).le) (by positivity)
            (Real.exp_pos _).le
      _ = Real.exp (401 + 9.5 * Real.log L) := by
          rw [pow_eq_exp hLpos, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
      _ ≤ Real.exp (0.25 * L) := Real.exp_le_exp.mpr (by linarith)
  · -- N^{1/2 − α} / log^{14} N ≥ z²
    rw [le_div_iff₀ (by positivity), rpow_eq_exp hN, rpow_eq_exp hN, ← hLdef,
      pow_eq_exp hLpos, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  · -- K_δ(x₁) = log^{1.3} x₁ ≥ 3022
    have h1 : (1024 : ℝ) ≤ Lx := by linarith
    have h2 : (1024 : ℝ) ^ (1.3 : ℝ) ≤ Lx ^ (1.3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
    have h3 : (1024 : ℝ) ^ (1.3 : ℝ) = 2 ^ (13 : ℕ) := by
      rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h3] at h2
    linarith

/-- The leaf `Burst4Split.leaf_theorem42_positive`, same statement, PROVED from the deep cited
leaf `theorem42_bracket` with the proved conditions (4.3) and U_N > 0. -/
theorem leaf_theorem42_positive_p2 : ∀ N : ℕ, Even N → X2v3 ≤ (N : ℝ) →
    0 < (siftedSet N ((N : ℝ) ^ ((1 : ℝ) / 40))).card := by
  intro N hE hX
  have h := theorem42_bracket paramConditions43 (fun N _ hX => conditions43 N hX) N hE hX
  have hpos : 0 ≤ 5 * ((setA N).card : ℝ) * UN N / Real.log (N : ℝ) := by
    have := UN_pos N
    have hL : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    positivity
  exact_mod_cast hpos.trans_lt h

/-! ### Part 3b. Lemma 3.1 of P0019 for N ≥ X₂ and the display on p. 13 -/

/-- Rosser and Schoenfeld 1962, reference [32] of P0019, used in the proof of Lemma 3.1, p. 6:
π(x) > x / (log x − 1/2) for x ≥ 67, at natural x. The same statement as the lab's cited
`ChenExplicit.Yamada.RS62` and `RieselVaughan1983.RS33`. Taken as a hypothesis, CITED. -/
def RS62Body : Prop :=
  ∀ n : ℕ, 67 ≤ n → (n : ℝ) / (Real.log n - 1 / 2) < (Nat.primeCounting n : ℝ)

/-- PROVED. ω(N) ≤ log N / log 2, since 2^{ω(N)} ≤ N. Used in place of Robin's bound [31]. -/
theorem card_primeFactors_le_log (N : ℕ) (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 := by
  have h0 : N ≠ 0 := by omega
  have hlen : N.primeFactors.card ≤ N.primeFactorsList.length := by
    rw [← Nat.toFinset_factors]; exact List.toFinset_card_le _
  have hfac : ∀ q ∈ N.primeFactorsList, (2 : ℝ) ≤ (q : ℝ) := by
    intro q hq; exact_mod_cast (Nat.prime_of_mem_primeFactorsList hq).two_le
  have hprod := pow_length_le_prod 2 (by norm_num) _ hfac
  rw [Nat.prod_primeFactorsList h0] at hprod
  have h2 : (2 : ℝ) ^ N.primeFactors.card ≤ N :=
    le_trans (pow_le_pow_right₀ (by norm_num) hlen) hprod
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at this
  exact this

/-- PROVED. |A| = π(N) − ω(N) ≥ π(N) − log N / log 2, proof of Lemma 3.1, p. 6. -/
theorem card_setA_ge (N : ℕ) (hN : 1 ≤ N) :
    (Nat.primeCounting N : ℝ) - Real.log N / Real.log 2 ≤ ((setA N).card : ℝ) := by
  classical
  set F := (range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N) with hF
  have hA : (setA N).card = F.card := by
    unfold setA
    apply card_image_of_injOn
    intro a ha b hb hab
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    omega
  have hsub : (range (N + 1)).filter Nat.Prime ⊆ F ∪ N.primeFactors := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_union]
    by_cases hd : p ∣ N
    · right; exact Nat.mem_primeFactors.mpr ⟨hp.2, hd, by omega⟩
    · left; rw [hF, mem_filter]; exact ⟨hp.1, hp.2, hd⟩
  have hpi : Nat.primeCounting N = ((range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']; rfl
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  have hω := card_primeFactors_le_log N hN
  rw [hA]
  have : (Nat.primeCounting N : ℝ) ≤ (F.card : ℝ) + (N.primeFactors.card : ℝ) := by
    rw [hpi]; exact_mod_cast hle
  linarith

/-- PROVED, CONDITIONAL ON `RS62Body`. Lemma 3.1, p. 6, for N ≥ X₂: |A| > N / log N. -/
theorem lemma31_large (hRS : RS62Body) (N : ℕ) (hX : X2v3 ≤ (N : ℝ)) :
    (N : ℝ) / Real.log N < ((setA N).card : ℝ) := by
  have hX0 : 0 < X2v3 := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hX0 hX
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : L0 ≤ L := by rw [← log_X2]; exact Real.log_le_log hX0 hX
  have hL : 2000 ≤ L := le_trans L0_ge hL0
  have hNexp : (N : ℝ) = Real.exp L := (Real.exp_log hNpos).symm
  have hN67 : 67 ≤ N := by
    have : (67 : ℝ) ≤ N := by
      rw [hNexp]
      have := Real.add_one_le_exp L
      linarith
    exact_mod_cast this
  have hpi := hRS N hN67
  have hA := card_setA_ge N (by omega)
  -- N ≥ L⁴/24 ≥ 4 L³
  have h4 : 4 * L ^ 3 ≤ (N : ℝ) := by
    have := Real.pow_div_factorial_le_exp L (by linarith) 4
    rw [← hNexp] at this
    have hf : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at this
    have : 4 * L ^ 3 ≤ L ^ 4 / 24 := by
      rw [le_div_iff₀ (by norm_num)]
      have : 0 ≤ L ^ 3 := by positivity
      nlinarith
    linarith
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hD : L / Real.log 2 ≤ 2 * L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hLp : 0 < L := by linarith
  have hL1 : L - 1 / 2 ≠ 0 := by intro h; linarith
  have hAeq : (N : ℝ) / (L - 1 / 2) - N / L = N / (2 * L * (L - 1 / 2)) := by
    rw [div_sub_div _ _ hL1 hLp.ne', div_eq_div_iff (mul_ne_zero hL1 hLp.ne')
      (mul_ne_zero (mul_ne_zero two_ne_zero hLp.ne') hL1)]
    ring
  rw [← hLdef] at hpi hA
  have hB : (N : ℝ) / (2 * L ^ 2) ≤ N / (2 * L * (L - 1 / 2)) := by
    apply div_le_div_of_nonneg_left hNpos.le (by nlinarith) (by nlinarith)
  have hC : 2 * L ≤ (N : ℝ) / (2 * L ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- PROVED, CONDITIONAL ON `theorem42_bracket` and `RS62Body`. The display on p. 13 of P0019:
S(A, P(z)) > 5 U_N N / log² N for every even N ≥ X₂, z = N^{1/40}. -/
theorem theorem42_display (hRS : RS62Body) :
    ∀ N : ℕ, Even N → X2v3 ≤ (N : ℝ) →
      5 * UN N * N / Real.log (N : ℝ) ^ 2 <
        ((siftedSet N ((N : ℝ) ^ ((1 : ℝ) / 40))).card : ℝ) := by
  intro N hE hX
  have h := theorem42_bracket paramConditions43 (fun N _ hX => conditions43 N hX) N hE hX
  have h31 := lemma31_large hRS N hX
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hX
  have hL : 0 < Real.log (N : ℝ) := by
    have : (2000 : ℝ) ≤ Real.log N := by
      have hX0 : 0 < X2v3 := Real.exp_pos _
      have := Real.log_le_log hX0 hX
      rw [log_X2] at this; linarith [L0_ge]
    linarith
  have hU := UN_pos N
  have : 5 * UN N * N / Real.log (N : ℝ) ^ 2 =
      5 * ((N : ℝ) / Real.log N) * UN N / Real.log N := by
    field_simp
  rw [this]
  refine lt_of_le_of_lt ?_ h
  apply div_le_div_of_nonneg_right _ hL.le
  have := mul_le_mul_of_nonneg_right h31.le hU.le
  nlinarith

/-! ### Part 3c. The numerical values on p. 13 of P0019 for h -/

/-- h(s) of Section 2, p. 4: e^{−2} on [1, 2], e^{−s} on [2, 3], 3 s^{−1} e^{−s} for s ≥ 3. -/
noncomputable def hfun (s : ℝ) : ℝ :=
  if s ≤ 2 then Real.exp (-2) else if s ≤ 3 then Real.exp (-s) else 3 / s * Real.exp (-s)

/-- c_{α, X₂, K} of Section 2, p. 4, at K = M = 40, α = 0.25, α₁ = 7, X₂ = exp(exp 7.9). -/
noncomputable def cAlpha : ℝ :=
  40 * (1 / 2 - 0.25 - 2 * 7 * Real.log (Real.log X2v3) / Real.log X2v3)

theorem exp79_ge : (2660 : ℝ) ≤ Real.exp 7.9 := by
  have h1 := Real.exp_one_gt_d9
  have h7 : Real.exp 7.9 = Real.exp 1 ^ 7 * Real.exp 0.9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h9 : (2.4265 : ℝ) ≤ Real.exp 0.9 := by
    have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.9) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hp : (2.71828 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 7
  rw [h7]
  calc (2660 : ℝ) ≤ 2.71828 ^ 7 * 2.4265 := by norm_num
    _ ≤ Real.exp 1 ^ 7 * Real.exp 0.9 := mul_le_mul hp h9 (by norm_num) (by positivity)

/-- PROVED. 8.23 ≤ c_{α, X₂, K} ≤ 10, as used on p. 13. -/
theorem cAlpha_bounds : (8.23 : ℝ) ≤ cAlpha ∧ cAlpha ≤ 10 := by
  have hlx : Real.log X2v3 = Real.exp 7.9 := log_X2
  have hll : Real.log (Real.log X2v3) = 7.9 := by rw [hlx, Real.log_exp]
  have he := exp79_ge
  unfold cAlpha
  rw [hll, hlx]
  have hpos : 0 < Real.exp 7.9 := Real.exp_pos _
  have h1 : 2 * 7 * (7.9 : ℝ) / Real.exp 7.9 ≤ 2 * 7 * 7.9 / 2660 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
  have h2 : 0 ≤ 2 * 7 * (7.9 : ℝ) / Real.exp 7.9 := by positivity
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- PROVED. h(M(1/2 − α)) = h(10) ≤ 1.4 · 10^{-5}, as stated on p. 13. -/
theorem h10_le : hfun 10 ≤ 1.4e-5 := by
  unfold hfun
  norm_num
  have h1 := Real.exp_one_gt_d9
  have he : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.7182818283 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
    pow_le_pow_left₀ (by norm_num) h1.le 10
  rw [Real.exp_neg, ← div_eq_mul_inv, he]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- QUESTION, PROVED. For 3 ≤ s ≤ 10, h(s) ≥ h(10) > 10^{-5}. Since c_{α, X₂, K} ≤ 10 by
`cAlpha_bounds`, the value h(c_{α X₂}) ≤ 10^{-5} printed on p. 13 does not hold; the true
value is about 8.4 · 10^{-5}. The effect on case (b) of Theorem 4.2 is of size 10^{-4}
against the margin M B ≥ 5 of `theorem42_bracket`, so it looks harmless. -/
theorem hfun_gt_of_le_ten {s : ℝ} (h3 : 3 ≤ s) (h10 : s ≤ 10) : 1e-5 < hfun s := by
  unfold hfun
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by linarith))]
  by_cases hs3 : s ≤ 3
  · have : s = 3 := le_antisymm hs3 h3
    subst this
    rw [if_pos le_rfl]
    have h1 := Real.exp_one_lt_d9
    have he : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg, he]
    have hp : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
    have : 0 < Real.exp 1 ^ 3 := by positivity
    rw [lt_inv_comm₀ (by norm_num) this]
    nlinarith
  · rw [if_neg hs3]
    have h1 := Real.exp_one_lt_d9
    have he : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hp : Real.exp 1 ^ 10 ≤ (2.7182818286 : ℝ) ^ 10 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 10
    have hes : Real.exp s ≤ Real.exp 10 := Real.exp_le_exp.mpr h10
    have hpos : 0 < Real.exp s := Real.exp_pos s
    rw [Real.exp_neg, ← div_eq_mul_inv, div_div, lt_div_iff₀ (by positivity)]
    nlinarith

theorem h_cAlpha_gt : 1e-5 < hfun cAlpha :=
  hfun_gt_of_le_ten (by linarith [cAlpha_bounds.1]) cAlpha_bounds.2

/-! ### Part 4. The top theorem again, from the finer leaves -/

/-- Lemma 3.5, p. 9, at X₂ = exp(exp 7.9), K = 395, using the split Hathi and Johnston leaf. -/
theorem lemma35_p2 (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) (hX : (N : ℝ) < X2v3) :
    PrimePlusAlmostPrime 395 N := by
  by_cases hs : N ≤ 4 * 10 ^ 18
  · obtain ⟨p, q, hp, hq, hpq⟩ := leaf_goldbach_4e18 N hE h4 hs
    refine ⟨p, q, hp, hq.pos, hpq.symm, ?_⟩
    simp [bigOmega, Nat.primeFactorsList_prime hq]
  · push Not at hs
    obtain ⟨p, η, hp, hsq, hcop, hpη⟩ := leaf_hathi_johnston_p2 N hE (by omega)
    have hη0 : 0 < η := by
      rcases Nat.eq_zero_or_pos η with h | h
      · exact absurd (h ▸ hsq) not_squarefree_zero
      · exact h
    have hlt : (η : ℝ) < X2v3 :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : η ≤ N)) hX
    exact ⟨p, η, hp, hη0, hpη, leaf_lemma35_count hsq hcop hlt⟩

/-- The sieve range from the split Theorem 4.2 leaf and the proved `leaf_sifted_omega`. -/
theorem sieve_range_p2 (N : ℕ) (hE : Even N) (hX : X2v3 ≤ (N : ℝ)) :
    PrimePlusAlmostPrime 39 N := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (leaf_theorem42_positive_p2 N hE hX)
  have hN : 1 ≤ N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hX
    exact_mod_cast this
  obtain ⟨p, hp, hNa, ha0, hO⟩ := leaf_sifted_omega N hN a ha
  exact ⟨p, a, hp, ha0, hNa, hO⟩

/-- Theorem 1.3 of P0019 v3, the statement of `LeanLab.AlmostPrimes.johnston_starichkova`,
from the finer leaves: `leaf_goldbach_4e18` cited, `hj_large_R_pos` cited, and
`theorem42_bracket` cited and deep. -/
theorem johnston_starichkova_p2 :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 395 N := by
  intro N hE h4
  by_cases hX : (N : ℝ) < X2v3
  · exact lemma35_p2 N hE h4 hX
  · push Not at hX
    obtain ⟨p, m, hp, hm, hN, hO⟩ := sieve_range_p2 N hE hX
    exact ⟨p, m, hp, hm, hN, hO.trans (by norm_num)⟩

theorem johnston_starichkova_p2_eq_type :
    @johnston_starichkova_p2 = @LeanLab.AlmostPrimes.johnston_starichkova := rfl

end LeanLab.AlmostPrimes.Burst8P2
