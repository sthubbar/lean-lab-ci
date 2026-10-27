/-
P0072 A. Togashi and S. Uchiyama 1964, J. Fac. Sci. Hokkaido Univ. Ser. I 18, pp. 60 to 68.
Lab copy papers/P0072.pdf and papers/P0072.txt. Unit U-1544, run 20261026T0808Z-17522, type
DECOMPOSE, track T1, file c of three.

This file c: from the per q bound to Lemma 5's summed form, pp. 64 to 65, and the final
assembly `upperSieveInput_of_leaves`: for every 0 < ε < 1/30 the hypothesis
`TogashiUchiyamaScale.UpperSieveInput Ttwin ε` holds, CONDITIONAL ON the leaves of files a, b
and c. Hence `TogashiUchiyamaScale.section5_of_two_sieve_inputs` now rests on Lemma 4,
`LowerSieveInput`, and on these leaves only.

Steps: for q ∈ Qset N put t_q = log N/log q ∈ [3, 6), a = 3(1 - 2ε - 1/t_q) ∈ (1, 3] and
w = N^{a/6}, so the sieve level is w² = N^{1-2ε}/q. Then
S(q) ≤ 2φ(N)/(q W_q) + R_q, W_q ≥ (1 - δ)((2a - 1)² - 2a² log a)/36 · C_N log² N, and
2φ(N)/(q · ((2a - 1)² - 2a² log a)/36 · C_N log² N) = A_N C_ε(t_q) φ(N)/(q log² N), p. 65.
Summing, Σ_q C_ε(t_q)/q ≤ I(ε) + o(1), "just as in [6, §5]", p. 65, and the remainders are
o(φ(N)/log² N) because B_N = 2^{ν(N)} = N^{o(1)}.

Leaves, all OPEN: `prime_sum_integral`, `two_pow_omega_le`, `Q_large`, `logpow_le_rpow`.
Assemblies, no sorry of their own: `remainder_small`, `Wq_relative`, `Sq_le_main`,
`upperSieveInput_of_leaves`, `togashiUchiyama_of_lemma4`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress
on it.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.Decomp1544b

open Finset Real Filter Topology
open scoped ArithmeticFunction.omega

noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp1544c
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5 LeanLab.AlmostPrimeSums.Decomp1544a
open LeanLab.AlmostPrimeSums.Decomp1544b LeanLab.AlmostPrimeSums.TogashiUchiyamaScale
open LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex

/-! ### Leaves -/

/-- LEAF. Unit U-1544. The prime sum to integral step on p. 65, "argue just as in [6, §5]":
for φ continuous on [3, 6] and η > 0, for all large N,
Σ_{N^{1/6} < q ≤ N^{1/3}} φ(log N/log q)/q ≤ ∫_3^6 φ(u)/u du + η.
Route: uniform continuity of φ, cut [3, 6] into short blocks, and on each block
Σ_{N^{1/u₂} < q ≤ N^{1/u₁}} 1/q = log(u₂/u₁) + O(1/log N) by `Decomp1528b.mertens2_block`. -/
theorem prime_sum_integral (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 3 6)) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ∑ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
          φ (log N / log q) / q ≤ (∫ u in (3 : ℝ)..6, φ u / u) + η := by
  sorry

/-- LEAF. Unit U-1544. B_N = 2^{ν(N)} = O(N^δ) for every δ > 0, used on p. 63 for
max_{d ≤ cN²} |R(d)| = O(N^ε) and on p. 65 for B_N N^{1-2ε} = o(φ(N)/log³ N). Route:
2^{ν(N)} ≤ τ(N) and the lab's PROVED `HeathBrown1985.card_divisors_le_rpow`. -/
theorem two_pow_omega_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (2 : ℝ) ^ ω N ≤ C * (N : ℝ) ^ δ := by
  sorry

/-- LEAF. Unit U-1544. C_N > c (log log N)^{-2}, p. 61, in the form used for the relative error
of W_q on p. 64: for every c > 0, eventually c (1 + log N) √(log N) ≤ Q(N) log² N, where
C_N = T Q(N)/8. True since Q(N) = ∏_{p ∣ N, p > 2} (1 - 2/p) ≫ (log log N)^{-2}. -/
theorem Q_large {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, c * (1 + log N) * √(log N) ≤ Q N * (log N) ^ 2 := by
  sorry

/-- LEAF. Unit U-1544. Powers of log N are o(N^α): for α > 0 and η > 0, eventually
(1 + log N)^{10} ≤ η N^α. Used for the remainders on p. 65. Route: Mathlib
`isLittleO_log_rpow_rpow_atTop`. -/
theorem logpow_le_rpow {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 + log N) ^ 10 ≤ η * (N : ℝ) ^ α := by
  have H0 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x) ^ (10 : ℝ)) (fun x : ℝ ↦ x ^ α) := by
    exact isLittleO_log_rpow_rpow_atTop 10 hα
  have H1 : (fun x : ℝ ↦ (log x) ^ (10 : ℝ)) =ᶠ[atTop] (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (rpow_natCast (log x) 10)
  have H2 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) (fun x : ℝ ↦ x ^ α) := by
    exact H0.congr' H1 (EventuallyEq.refl atTop _)
  have H3 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ 1 + log x) (fun x : ℝ ↦ log x) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hlog : 1 ≤ log x := by
      have := Real.log_le_log (Real.exp_pos 1) hx
      rw [Real.log_exp] at this
      exact this
    have hlog_pos : 0 ≤ log x := by linarith
    have h_pos : 0 ≤ 1 + log x := by linarith
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg h_pos, abs_of_nonneg hlog_pos]
    linarith
  have H4 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (1 + log x) ^ (10 : ℕ)) (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) := by
    exact H3.pow 10
  have H5 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 + log x) ^ (10 : ℕ)) (fun x : ℝ ↦ x ^ α) := by
    exact H4.trans_isLittleO H2
  have H6 := H5.bound hη
  have H7 := tendsto_natCast_atTop_atTop.eventually H6
  filter_upwards [H7, eventually_ge_atTop 1] with N hN hN1
  have hN_real_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hc : 0 ≤ (1 + log (N : ℝ)) ^ (10 : ℕ) := by positivity
  rw [norm_eq_abs, abs_of_nonneg hc, norm_eq_abs, abs_of_nonneg (rpow_nonneg hN_real_pos α)] at hN
  exact hN

/-! ### Assemblies -/

/-- The remainders of p. 65 are negligible: for ε, η > 0, eventually
2^{ν(N)+1} N^{1-2ε} (1 + log N)⁷ ≤ η φ(N)/log² N. Assembly, CONDITIONAL ON
`two_pow_omega_le` and `logpow_le_rpow`, with the lab's PROVED `S3Small.le_totient_mul_log`. -/
theorem remainder_small {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 7) ≤
      η * (N.totient : ℝ) / (log N) ^ 2 := by
  obtain ⟨C, hC, hω⟩ := two_pow_omega_le hε
  set c0 : ℝ := exp 1 * (1 + 1 / log 2) with hc0
  have hc0p : 0 < c0 := by
    have : 0 < log (2 : ℝ) := log_pos (by norm_num); positivity
  have h2Cc : 0 < 2 * C * c0 := mul_pos (mul_pos two_pos hC) hc0p
  filter_upwards [logpow_le_rpow hε (div_pos hη h2Cc),
    eventually_ge_atTop 3] with N hlog hN3
  have hN1 : 1 ≤ N := by omega
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  set LN := log (N : ℝ) with hLN
  have hLN1 : 1 ≤ LN := by
    rw [hLN, ← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have htot := S3Small.le_totient_mul_log hN1 hLN1
  rw [← hc0, ← hLN] at htot
  have hφ0 : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr hN1
  have hωN := hω N hN1
  -- LHS ≤ 2 C N^{1-ε} (1+LN)^7
  have hsplit : (N : ℝ) ^ ε * (N : ℝ) ^ (1 - 2 * ε) = (N : ℝ) ^ (1 - ε) := by
    rw [← rpow_add hN0]; ring_nf
  have hP7 : 0 ≤ (1 + LN) ^ 7 := pow_nonneg (by linarith) 7
  have hL1 : (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 7) ≤
      2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) := by
    rw [pow_succ, ← hsplit]
    have := mul_le_mul_of_nonneg_right hωN
      (show 0 ≤ 2 * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 7) from
        mul_nonneg two_pos.le (mul_nonneg (rpow_nonneg hN0.le _) hP7))
    linarith
  -- RHS ≥ η N / (c0 LN³)
  have hR : η * (N : ℝ) / (c0 * LN ^ 3) ≤ η * (N.totient : ℝ) / LN ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hc0p (pow_pos (by linarith) 3)) (pow_pos (by linarith) 2)]
    have := mul_le_mul_of_nonneg_left htot (mul_nonneg hη.le (sq_nonneg LN))
    linarith
  refine hL1.trans (le_trans ?_ hR)
  rw [le_div_iff₀ (mul_pos hc0p (pow_pos (by linarith) 3))]
  have hL3 : LN ^ 3 ≤ (1 + LN) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hkey : 2 * C * c0 * (1 + LN) ^ 10 ≤ η * (N : ℝ) ^ ε := by
    have := mul_le_mul_of_nonneg_left hlog h2Cc.le
    rw [show 2 * C * c0 * (η / (2 * C * c0) * (N : ℝ) ^ ε) = η * (N : ℝ) ^ ε by
      field_simp] at this
    exact this
  have hNe : 0 < (N : ℝ) ^ (1 - ε) := rpow_pos_of_pos hN0 _
  have hA0 : 0 ≤ 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 :=
    mul_nonneg (mul_nonneg (mul_pos two_pos hC).le (mul_nonneg hNe.le hP7)) hc0p.le
  calc 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * (c0 * LN ^ 3)
      = 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 * LN ^ 3 := by ring
    _ ≤ 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 * (1 + LN) ^ 3 :=
        mul_le_mul_of_nonneg_left hL3 hA0
    _ = (N : ℝ) ^ (1 - ε) * (2 * C * c0 * (1 + LN) ^ 10) := by ring
    _ ≤ (N : ℝ) ^ (1 - ε) * (η * (N : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hkey hNe.le
    _ = η * ((N : ℝ) ^ (1 - ε) * (N : ℝ) ^ ε) := by ring
    _ = η * N := by rw [← rpow_add hN0, show 1 - ε + ε = (1 : ℝ) by ring, rpow_one]

/-- W_q with relative error, p. 64: for δ > 0, eventually for even N and 1 ≤ a ≤ 3,
W_q(N^{a/6}) ≥ (1 - δ) ((2a - 1)² - 2a² log a)/36 · C_N log² N. Assembly, CONDITIONAL ON
`Q_large` and the leaves of `Wq_lower`. -/
theorem Wq_relative {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ a : ℝ, 1 ≤ a → a ≤ 3 →
      (1 - δ) * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) ≤ Wq N ((N : ℝ) ^ (a / 6)) := by
  obtain ⟨Cw, hCw, hW⟩ := Wq_lower
  have hδ' : δ ≠ 0 := hδ.ne'
  filter_upwards [Q_large (c := 288 * Cw / δ) (div_pos (by linarith) hδ), eventually_ge_atTop 64]
    with N hQ hN64 hN a ha1 ha3
  have hWa := hW N hN hN64 a ha1 ha3
  have hqa : 1 ≤ TogashiUchiyama.q a := TogashiUchiyamaEpsilon.q_ge_one ⟨ha1, ha3⟩
  have hT := one_le_Ttwin
  have hQ0 := (Q_bounds N).1
  have hL : 0 ≤ (log N) ^ 2 := sq_nonneg _
  have hCK : Q N / 8 ≤ CK N := by
    simp only [CK, Cpaper]
    have : Q N ≤ Ttwin * Q N := by nlinarith
    linarith
  -- δ · (qa/36) CK L² ≥ δ/288 · Q L² ≥ Cw (1 + L) √L
  have h1 : Cw * (1 + log N) * √(log N) ≤ δ / 288 * (Q N * (log N) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hQ (show 0 ≤ δ / 288 by linarith)
    calc Cw * (1 + log N) * √(log N) = δ / 288 * (288 * Cw / δ * (1 + log N) * √(log N)) := by
          field_simp
      _ ≤ _ := this
  have h2 : δ / 288 * (Q N * (log N) ^ 2) ≤
      δ * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) := by
    have hA : Q N / 8 * (log N) ^ 2 ≤ TogashiUchiyama.q a * CK N * (log N) ^ 2 := by
      have : Q N / 8 ≤ TogashiUchiyama.q a * CK N := by
        have hCK0 : 0 ≤ CK N := CK_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hqa hCK0]
      exact mul_le_mul_of_nonneg_right this hL
    have := mul_le_mul_of_nonneg_left hA (show 0 ≤ δ / 36 by linarith)
    calc δ / 288 * (Q N * (log N) ^ 2) = δ / 36 * (Q N / 8 * (log N) ^ 2) := by ring
      _ ≤ δ / 36 * (TogashiUchiyama.q a * CK N * (log N) ^ 2) := this
      _ = _ := by ring
  linarith

/-- The per q bound of p. 65: for q ∈ Qset N, N even, N ≥ 64, given the relative W_q bound,
S(q) ≤ M C_ε(t_q)/(q(1 - δ)) + 2^{ν(N)+1} N^{1-2ε} (1 + log N)⁶/q, with
M = A_N φ(N)/log² N and t_q = log N/log q. Assembly from `Sq_le_selberg`,
CONDITIONAL ON its leaves. -/
theorem Sq_le_main {ε δ : ℝ} (hε0 : 0 < ε) (hε30 : ε < 1 / 30) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    {N q : ℕ} (hN : Even N) (hN64 : 64 ≤ N) (hq : q ∈ Qset N)
    (hW : ∀ a : ℝ, 1 ≤ a → a ≤ 3 →
      (1 - δ) * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) ≤ Wq N ((N : ℝ) ^ (a / 6))) :
    ((Sq N q).card : ℝ) ≤ M Ttwin N * Ceps ε (log N / log q) / q / (1 - δ) +
      (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 6) / q := by
  have hqm := mem_filter.mp hq
  obtain ⟨hqp, hq6, hq3, _⟩ := hqm.2
  have hNR : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  set LN := log (N : ℝ) with hLN
  have hLN0 : 0 < LN := log_pos (by linarith)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq : 0 < log (q : ℝ) := log_pos (by linarith)
  have h3 : 3 * log (q : ℝ) ≤ LN := by
    have : ((q ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hq3
    have := log_le_log (by exact_mod_cast pow_pos hqp.pos 3) this
    rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
  have h6 : LN < 6 * log (q : ℝ) := by
    have : (N : ℝ) < ((q ^ 6 : ℕ) : ℝ) := by exact_mod_cast hq6
    have := log_lt_log hN0 this
    rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
  set t := LN / log (q : ℝ) with ht
  have ht3 : 3 ≤ t := by rw [ht, le_div_iff₀ hlq]; linarith
  have ht6 : t ≤ 6 := by rw [ht, div_le_iff₀ hlq]; linarith
  have hεE : ε ∈ TogashiUchiyamaEpsilon.E := ⟨hε0.le, hε30.le⟩
  have hA := TogashiUchiyamaEpsilon.A_range hεE ⟨ht3, ht6⟩
  obtain ⟨a, ha⟩ : ∃ a, a = TogashiUchiyamaEpsilon.A ε t := ⟨_, rfl⟩
  have hA1' : 1 < 3 * (1 - 2 * ε - 1 / t) := hA.1
  have ha1 : 1 ≤ a := by rw [ha]; exact hA.1.le
  have ha3 : a ≤ 3 := by rw [ha]; exact hA.2
  have hinvt : 1 / t = log (q : ℝ) / LN := by rw [ht, one_div_div]
  -- the level
  set w := (N : ℝ) ^ (a / 6) with hw
  have hw1 : 1 ≤ w := one_le_rpow (by linarith) (by linarith)
  have hexp : a / 6 * ((2 : ℕ) : ℝ) = 1 - 2 * ε - log (q : ℝ) / LN := by
    rw [ha, TogashiUchiyamaEpsilon.A, hinvt]; push_cast; ring
  have hw2 : w ^ 2 = (N : ℝ) ^ (1 - 2 * ε) / q := by
    rw [hw, ← rpow_natCast, ← rpow_mul hN0.le, hexp, rpow_def_of_pos hN0, rpow_def_of_pos hN0,
      ← hLN, show LN * (1 - 2 * ε - log (q : ℝ) / LN) = LN * (1 - 2 * ε) - log (q : ℝ) by
        field_simp, exp_sub, exp_log hq0]
  have hlw2 : log (w ^ 2) ≤ LN := by
    rw [hw2, log_div (rpow_pos_of_pos hN0 _).ne' hq0.ne', log_rpow hN0, ← hLN]
    nlinarith
  have hlw20 : 0 ≤ log (w ^ 2) := log_nonneg (by nlinarith)
  have hS := Sq_le_selberg hN hN1 hq hw1
  -- the main term
  have hqa : 1 ≤ TogashiUchiyama.q a := TogashiUchiyamaEpsilon.q_ge_one ⟨ha1, ha3⟩
  have hT := one_le_Ttwin
  have hQ0 := (Q_bounds N).1
  have hCK0 : 0 < CK N := by
    simp only [CK, Cpaper]; have := mul_pos (by linarith : (0:ℝ) < Ttwin) hQ0; linarith
  set V := TogashiUchiyama.q a / 36 * CK N * LN ^ 2 with hV
  have hV0 : 0 < V := by
    rw [hV]
    exact mul_pos (mul_pos (div_pos (by linarith) (by norm_num)) hCK0) (pow_pos hLN0 2)
  have hWa := hW a ha1 ha3
  have hδ1 : 0 < 1 - δ := by linarith
  have hWpos : 0 < (1 - δ) * V := mul_pos hδ1 hV0
  have hφ0 : (0 : ℝ) ≤ N.totient := Nat.cast_nonneg _
  have hmain1 : 2 * (N.totient : ℝ) / (q * Wq N w) ≤ 2 * (N.totient : ℝ) / (q * ((1 - δ) * V)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hq0 hWpos)
      (mul_le_mul_of_nonneg_left hWa hq0.le)
  have hCeps : Ceps ε t = TogashiUchiyamaEpsilon.K / TogashiUchiyama.q a := by
    rw [ha]
    simp only [Ceps, D, TogashiUchiyamaEpsilon.K, TogashiUchiyamaEpsilon.A]
    rw [if_neg (not_le.mpr hA1')]
  have hid : 2 * (N.totient : ℝ) / (q * ((1 - δ) * V)) =
      M Ttwin N * Ceps ε t / q / (1 - δ) := by
    rw [hCeps]
    simp only [M, Apaper, hV, TogashiUchiyamaEpsilon.K]
    have : CK N = Cpaper Ttwin N := rfl
    rw [← this, ← hLN]
    have he : 0 < exp (2 * eulerMascheroniConstant) := exp_pos _
    have hqa0 : 0 < TogashiUchiyama.q a := by linarith
    field_simp
    ring
  -- the remainder
  have hp6 : (1 + log (w ^ 2)) ^ 6 ≤ (1 + LN) ^ 6 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 6
  have hrem : (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6) ≤
      (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 6) / q := by
    calc (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6)
        ≤ (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + LN) ^ 6) := by gcongr
      _ = _ := by rw [hw2]; ring
  rw [hid] at hmain1
  linarith

/-- **Section 3 summed upper sieve bound, `UpperSieveInput`**, pp. 63 to 65: for every
0 < ε < 1/30, eventually for even N,
Σ_{z<q≤z₁, (q, N) = 1} S(q) ≤ I(ε) A_N φ(N)/log² N + 3ε A_N φ(N)/log² N,
with T = `Ttwin` the true constant of p. 61. Assembly, CONDITIONAL ON the leaves of
Decomp1544a, Decomp1544b, Decomp1544c and the Decomp1528 leaves behind `mertens1_abs` and
`mertens2_block`. With `TogashiUchiyamaScale.section5_of_two_sieve_inputs` the main theorem of
P0072 is then CONDITIONAL ON Lemma 4 and these leaves only. -/
theorem upperSieveInput_of_leaves {ε : ℝ} (hε0 : 0 < ε) (hε30 : ε < 1 / 30) :
    UpperSieveInput Ttwin ε := by
  set I := TogashiUchiyamaEpsilon.I ε with hI
  set δ := min (1 / 2) (ε / (4 * (|I| + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε0 (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ * (4 * (|I| + 1)) ≤ ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / (4 * (|I| + 1)))
    rw [← hδdef] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hT := one_le_Ttwin
  have hTpos : 0 < Ttwin := by linarith
  have hεE : ε ∈ TogashiUchiyamaEpsilon.E := ⟨hε0.le, hε30.le⟩
  have hcont : ContinuousOn (Ceps ε) (Set.Icc 3 6) := by
    have h := (TogashiUchiyamaEpsilon.integrand_continuousOn hεE).mul continuousOn_id
    refine h.congr fun u hu => ?_
    have : u ≠ 0 := by linarith [hu.1]
    show Ceps ε u = Ceps ε u / u * u
    field_simp
  obtain ⟨Ch, hCh0, hCh⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Ioc 0 N, invW m ≤ 3 * (1 + log N) := by
    refine ⟨0, le_rfl, fun N hN => ?_⟩
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h := (abs_le.mp (harmonic_asymp hNR)).2
    rw [Nat.floor_natCast] at h
    have hγ := eulerMascheroniConstant_lt_two_thirds
    have h2 : 2 / (N : ℝ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have := log_nonneg hNR
    linarith
  filter_upwards [Wq_relative hδ0, prime_sum_integral (Ceps ε) hcont (show 0 < ε / 2 by linarith),
    remainder_small hε0 (div_pos (mul_pos hε0 (a_pos hTpos)) three_pos),
    eventually_ge_atTop 64] with N hWr hPS hR hN64 hN
  have hNR : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hM0 : 0 ≤ M Ttwin N := by
    have := M_lower hTpos N
    have : 0 ≤ a Ttwin * (N.totient : ℝ) / (log N) ^ 2 :=
      div_nonneg (mul_nonneg (a_pos hTpos).le (Nat.cast_nonneg _)) (sq_nonneg _)
    linarith
  have hδ1 : 0 < 1 - δ := by linarith
  -- per q
  have hper := fun q (hq : q ∈ Qset N) =>
    Sq_le_main hε0 hε30 hδ0 hδ2 hN hN64 hq (hWr hN)
  push_cast
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib]
  -- the C_ε sum
  set S := ∑ q ∈ Qset N, Ceps ε (log N / log q) / q with hSdef
  have hterm : ∀ q ∈ Qset N, M Ttwin N * Ceps ε (log N / log q) / q / (1 - δ) =
      M Ttwin N / (1 - δ) * (Ceps ε (log N / log q) / q) := by
    intro q _; field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  have hCpos : ∀ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
      0 ≤ Ceps ε (log N / log q) / q := by
    intro q hq
    obtain ⟨hqp, _, hq3⟩ := (mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
    have hlq : 0 < log (q : ℝ) := log_pos (by linarith)
    have h3 : 3 * log (q : ℝ) ≤ log N := by
      have : ((q ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hq3
      have := log_le_log (by exact_mod_cast pow_pos hqp.pos 3) this
      rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
    have ht : 1 / (1 - 2 * ε) < log N / log q := by
      have h1 : 1 / (1 - 2 * ε) < 3 := by rw [div_lt_iff₀ (by linarith)]; linarith
      have h2 : 3 ≤ log N / log q := by rw [le_div_iff₀ hlq]; linarith
      linarith
    have := Ceps_pos hε0.le (by linarith) ht
    exact div_nonneg this.le (Nat.cast_nonneg q)
  have hS0 : 0 ≤ S := sum_nonneg fun q hq => hCpos q (by
    simp only [Qset, mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩)
  have hSle : S ≤ I + ε / 2 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => hCpos q hq) hPS
    intro q hq
    simp only [Qset, mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩
  -- the remainder sum
  set R := (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 6) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hsub : ∑ q ∈ Qset N, ((q : ℝ))⁻¹ ≤ ∑ m ∈ Ioc 0 N, invW m := by
    simp only [invW_apply]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
    intro q hq
    simp only [Qset, mem_filter, mem_range] at hq
    exact mem_Ioc.mpr ⟨hq.2.1.pos, by omega⟩
  have hRsum : ∑ q ∈ Qset N, R / q ≤ R * (3 * (1 + log N)) := by
    calc ∑ q ∈ Qset N, R / q = R * ∑ q ∈ Qset N, ((q : ℝ))⁻¹ := by
          rw [mul_sum]; exact sum_congr rfl fun q _ => div_eq_mul_inv R q
      _ ≤ R * (3 * (1 + log N)) :=
          mul_le_mul_of_nonneg_left (hsub.trans (hCh N (by omega))) hR0
  have hRM : R * (3 * (1 + log N)) ≤ ε * M Ttwin N := by
    have h1 : R * (3 * (1 + log N)) =
        3 * ((2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 7)) := by
      rw [hRdef]; ring
    rw [h1]
    have h2 := M_lower hTpos N
    have h3 : 3 * (ε * a Ttwin / 3 * (N.totient : ℝ) / (log N) ^ 2) =
        ε * (a Ttwin * (N.totient : ℝ) / (log N) ^ 2) := by ring
    linarith [mul_le_mul_of_nonneg_left h2 hε0.le]
  -- combine
  have hfac : M Ttwin N / (1 - δ) * S ≤ M Ttwin N * (I + ε) := by
    have hinv : 1 / (1 - δ) ≤ 1 + 2 * δ := by
      rw [div_le_iff₀ hδ1]; nlinarith
    have hSI : S * (1 + 2 * δ) ≤ I + ε := by
      have hIabs : I ≤ |I| := le_abs_self I
      have hSb : S ≤ |I| + 1 := by linarith
      have h2δ : 2 * δ * S ≤ 2 * δ * (|I| + 1) :=
        mul_le_mul_of_nonneg_left hSb (by linarith)
      have : 2 * δ * S ≤ ε / 2 := by linarith
      linarith
    calc M Ttwin N / (1 - δ) * S = M Ttwin N * (S * (1 / (1 - δ))) := by ring
      _ ≤ M Ttwin N * (S * (1 + 2 * δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hS0) hM0
      _ ≤ M Ttwin N * (I + ε) := mul_le_mul_of_nonneg_left hSI hM0
  linarith [mul_nonneg hε0.le hM0]

/-- **P0072 main theorem from Lemma 4 alone, modulo the leaves.** There is ε, 0 < ε < 1/30,
such that if Lemma 4, `LowerSieveInput Ttwin ε`, holds then every large even N is n + (N - n)
with 1 < n < N - 1, (n, N) = 1, V(n) ≤ 3, V(N - n) ≤ 3. Assembly from
`TogashiUchiyamaScale.section5_of_two_sieve_inputs`, `TogashiUchiyamaEpsilon.exists_epsilon_interval`
and `upperSieveInput_of_leaves`; CONDITIONAL ON Lemma 4 and the leaves listed there. -/
theorem togashiUchiyama_of_lemma4 :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 30 ∧ (LowerSieveInput Ttwin ε →
      ∀ᶠ N : ℕ in atTop, Even N → ∃ n : ℕ,
        1 < n ∧ n < N - 1 ∧ n.Coprime N ∧ ArithmeticFunction.cardFactors n ≤ 3 ∧
          ArithmeticFunction.cardFactors (N - n) ≤ 3) := by
  obtain ⟨η, hη, hη30, hI⟩ := TogashiUchiyamaEpsilon.exists_epsilon_interval
  set ε : ℝ := min η (1 / 30000) with hεdef
  have hε : 0 < ε := lt_min hη (by norm_num)
  have hεη : ε ≤ η := min_le_left _ _
  have hεs : ε ≤ 1 / 30000 := min_le_right _ _
  have hε30 : ε < 1 / 30 := lt_of_le_of_lt hεη hη30
  refine ⟨ε, hε, hε30, fun hlow => ?_⟩
  have hT : 0 < Ttwin := lt_of_lt_of_le zero_lt_one one_le_Ttwin
  exact section5_of_two_sieve_inputs hT hε hεs (hI ε hε.le hεη) hlow
    (upperSieveInput_of_leaves hε hε30)

/-! ### Vacuity instances -/

/-- The hypotheses of `upperSieveInput_of_leaves` can hold: ε = 1/60. -/
theorem vacuity_c1 : (0 : ℝ) < 1 / 60 ∧ (1 / 60 : ℝ) < 1 / 30 := by norm_num

/-- The hypotheses of `Sq_le_main` can hold, apart from the W_q bound which `Wq_relative`
supplies eventually: N = 30030 is even, 30030 ≥ 64, and 17 ∈ Qset 30030; δ = 1/4. -/
theorem vacuity_c2 : Even 30030 ∧ 64 ≤ 30030 ∧ 17 ∈ Qset 30030 ∧ (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 2 := by
  refine ⟨by decide, by norm_num, ?_, by norm_num, by norm_num⟩
  simp only [Qset, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end LeanLab.AlmostPrimeSums.Decomp1544c
