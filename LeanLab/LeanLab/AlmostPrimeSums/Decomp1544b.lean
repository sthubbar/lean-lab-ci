/-
P0072 A. Togashi and S. Uchiyama 1964, J. Fac. Sci. Hokkaido Univ. Ser. I 18, pp. 60 to 68.
Lab copy papers/P0072.pdf and papers/P0072.txt. Unit U-1544, run 20261026T0808Z-17522, type
DECOMPOSE, track T1, file b of three.

This file b: the lower bound for W_q on p. 64 in the case a > 1, which is the only case that
occurs for q ∈ Qset N, since there 3 ≤ t_q < 6 and so a = 3(1 - 2ε - 1/t_q) ∈ [2 - 6ε, 2.5),
W_q ≥ ((2a - 1)² - 2a² log a)/36 · C_N log² N - O(log^{3/2} N),
together with Lemma 3 of p. 62, the Shapiro and Warga sum
Σ_{m ≤ x, (m, kN) = 1} μ²(m)/f₁(m) = C_{kN} log² x + error, which the paper attributes to
Shapiro and Warga 1950 Lemma 3 and which is split here into leaves along the route
μ²/f₁ = ρ_K * (τ(n)/n), Σ_{n ≤ y} τ(n)/n = ½ log² y + 2γ log y + O(1).
The error term of `lemma3` is C (1 + log x) √(log K), uniform in x ≥ 1; it is weaker than the
paper's O(log kN log log kN) for x ≤ N, and it is all the argument of p. 64 needs.

T = ∏_{p > 2} (p - 1)²/(p(p - 2)) is `Ttwin`, and C_K = T Q(K)/8 is
`TogashiUchiyamaScale.Cpaper Ttwin K`, as on p. 61.

CODEX task187 proves seven original leaves: `rhoK_mul_tauW`, `sum_log_div_asymp`,
`rhoK_hasSum`, `Wq_ge_union`, `Q_mul_prime`, `sum_logsq_div_primes`, `one_le_Ttwin`.
The existing `harmonic_asymp` was already proved. The only remaining OPEN leaf is
`rhoK_moment`, the bound uniform in K. Fixed K moments and bounded modulus moments are
proved helpers and do not discharge that uniform leaf.
Also used, from AlmostPrimes/Decomp1528a and Decomp1528b and not restated: the proved
`mertens1_abs` and the still conditional `mertens2_block`.
Assemblies, no sorry of their own: `Tsum_asymp`; `rhoK_partial`; `lemma3`, Lemma 3;
`prime_square_sum`, the prime sum on p. 64 with the three Mertens type estimates;
`Wq_lower`, the W_q display of p. 64 for 1 ≤ a ≤ 3.

Original decomposition by Claude, 2026-10-26. Proofs and helpers by OpenAI Codex task187,
2026-10-30. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.Decomp1544a
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale
import LeanLab.AlmostPrimes.Decomp1528b

open Finset Real Filter Topology
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp1544b
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5 LeanLab.AlmostPrimeSums.Decomp1544a
open LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

/-! ### Definitions -/

/-- μ²(m)/f₁(m) of p. 61 for the modulus K: ∏_{p ∣ m} 2/(p - 2) on squarefree m prime to K,
else 0. -/
def hK (K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≠ 0 ∧ Squarefree m ∧ m.Coprime K then ∏ p ∈ m.primeFactors, 2 / ((p : ℝ) - 2)
    else 0, by simp⟩

/-- The sum of Lemma 3: Σ_{m ≤ x, (m, K) = 1} μ²(m)/f₁(m). -/
def G (K : ℕ) (x : ℝ) : ℝ := ∑ m ∈ Ioc 0 ⌊x⌋₊, hK K m

/-- n ↦ 1/n. -/
def invW : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

/-- n ↦ μ(n)/n, the Dirichlet inverse of 1/n. -/
def muW : ArithmeticFunction ℝ := ⟨fun n => (μ n : ℝ) / n, by simp⟩

lemma invW_apply (n : ℕ) : invW n = (n : ℝ)⁻¹ := rfl

/-- τ(n)/n = Σ_{de = n} (1/d)(1/e). -/
def tauW : ArithmeticFunction ℝ := invW * invW

/-- ρ_K = (μ²/f₁) * (μ/·) * (μ/·), so that ρ_K * (τ/·) = μ²/f₁. -/
def rhoK (K : ℕ) : ArithmeticFunction ℝ := hK K * muW * muW

/-- T = ∏_{p > 2} (p - 1)²/(p(p - 2)), p. 61. -/
def Ttwin : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)))

/-- C_K = T Q(K)/8, p. 61. -/
def CK (K : ℕ) : ℝ := Cpaper Ttwin K

/-- The reciprocal f1 weights in Lemma 3, p. 62 are nonnegative. -/
lemma hK_nonneg (N m : ℕ) : 0 ≤ hK N m := by
  change 0 ≤ if m ≠ 0 ∧ Squarefree m ∧ m.Coprime N then ∏ p ∈ m.primeFactors, 2 / ((p : ℝ) - 2) else 0
  split_ifs
  · apply prod_nonneg
    intro p hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl


/-- Removing a prime factor gives the reciprocal f1 factorization on p. 64. -/
lemma hK_mul_prime {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (d : ℕ) :
    hK N (p * d) = (2 / ((p : ℝ) - 2)) * hK (p * N) d := by
  by_cases hd0 : d = 0
  · subst d; simp
  change (if p*d ≠ 0 ∧ Squarefree (p*d) ∧ (p*d).Coprime N then
    ∏ q ∈ (p*d).primeFactors, 2 / ((q : ℝ)-2) else 0) =
    2 / ((p : ℝ)-2) * (if d ≠ 0 ∧ Squarefree d ∧ d.Coprime (p*N) then
      ∏ q ∈ d.primeFactors, 2 / ((q : ℝ)-2) else 0)
  have hpNc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
  by_cases hds : Squarefree d
  · by_cases hpd : p ∣ d
    · have hns : ¬ Squarefree (p*d) := by
        rw [Nat.squarefree_mul_iff]
        simp [hp.coprime_iff_not_dvd, hpd]
      have hnc : ¬ d.Coprime (p*N) := by
        simp [Nat.coprime_mul_iff_right, Nat.coprime_comm, hp.coprime_iff_not_dvd, hpd]
      simp only [hns, hnc, and_false, false_and, ite_false, mul_zero]
    · have hpc : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpd
      have hms : Squarefree (p*d) := (Nat.squarefree_mul hpc).mpr ⟨hp.squarefree, hds⟩
      by_cases hdN : d.Coprime N
      · have hmc : (p*d).Coprime N := hpNc.mul_left hdN
        have hdc : d.Coprime (p*N) := hpc.symm.mul_right hdN
        rw [ite_eq_left ⟨mul_ne_zero hp.ne_zero hd0, hms, hmc⟩, ite_eq_left ⟨hd0, hds, hdc⟩]
        rw [Nat.primeFactors_mul hp.ne_zero hd0, hp.primeFactors, singleton_union,
          prod_insert (by simp [Nat.mem_primeFactors, hpd])]
      · have hmc : ¬ (p*d).Coprime N := fun h => hdN (Nat.coprime_mul_iff_left.mp h).2
        have hdc : ¬ d.Coprime (p*N) := fun h => hdN (Nat.coprime_mul_iff_right.mp h).2
        simp only [hmc, hdc, and_false, ite_false, mul_zero]
  · have hns : ¬ Squarefree (p*d) := fun h => hds h.of_mul_right
    simp only [hns, hds, false_and, and_false, false_and, ite_false, mul_zero]

/-! ### Lemma 3, p. 62, in leaves -/

/-- LEAF. Unit U-1544. ρ_K * (τ(n)/n) = μ²(m)/f₁(m) as arithmetic functions: (μ/·) * (1/·) is
the unit, since twisting by the completely multiplicative 1/n respects Dirichlet convolution
and μ * 1 = ε. Route for Lemma 3, p. 62. -/
theorem rhoK_mul_tauW (K : ℕ) : rhoK K * tauW = hK K := by
  have hi : muW * invW = 1 :=
    moebius_reciprocal_convolution muW invW (fun _ => rfl) (fun _ => rfl)
  unfold rhoK tauW
  calc hK K * muW * muW * (invW * invW) = hK K * (muW * invW) * (muW * invW) := by
        ac_rfl
       _ = hK K := by rw [hi]; simp

/-- LEAF. Unit U-1544. For y ≥ 1, |Σ_{m ≤ y} 1/m - log y - γ| ≤ 2/y, with γ Euler's constant.
Mathlib's `eulerMascheroniSeq` bounds give 0 ≤ H_n - log n - γ ≤ 1/n, and n = ⌊y⌋ ≥ y/2.
Route for Lemma 3, p. 62. -/
lemma invW_sum_eq_harmonic (n : ℕ) : ∑ m ∈ Ioc 0 n, invW m = harmonic n := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    rw [ih, harmonic_succ]
    dsimp [invW]
    change _ + ((n + 1 : ℕ) : ℝ)⁻¹ = _
    push_cast
    rfl

/-- LEAF. Unit U-1544. For y ≥ 1, |Σ_{m ≤ y} 1/m - log y - γ| ≤ 2/y, with γ Euler's constant.
Mathlib's `eulerMascheroniSeq` bounds give 0 ≤ H_n - log n - γ ≤ 1/n, and n = ⌊y⌋ ≥ y/2.
Route for Lemma 3, p. 62. -/
theorem harmonic_asymp {y : ℝ} (hy : 1 ≤ y) :
    |∑ m ∈ Ioc 0 ⌊y⌋₊, invW m - log y - eulerMascheroniConstant| ≤ 2 / y := by
  rw [invW_sum_eq_harmonic]
  set n := ⌊y⌋₊ with hn
  have hn_pos : 0 < n := Nat.floor_pos.mpr hy
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have h_le_y : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hy_lt : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
  have h_log_y_ge : log (n : ℝ) ≤ log y := log_le_log hn_pos_real h_le_y
  have hy_pos : 0 < y := by linarith
  have h_log_y_le : log y ≤ log ((n : ℝ) + 1) := log_le_log hy_pos hy_lt.le
  have hl1 : eulerMascheroniSeq n < eulerMascheroniConstant := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hl2 : eulerMascheroniConstant < eulerMascheroniSeq' n := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_seq : eulerMascheroniSeq n = harmonic n - log ((n : ℝ) + 1) := rfl
  have h_seq' : eulerMascheroniSeq' n = harmonic n - log (n : ℝ) := by
    dsimp [eulerMascheroniSeq']
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hn_pos.ne' h))]
  rw [abs_le]
  constructor
  · have h_diff : eulerMascheroniSeq' n - eulerMascheroniSeq n = log ((n : ℝ) + 1) - log (n : ℝ) := by
      rw [h_seq, h_seq']; ring
    have h_diff_le : log ((n : ℝ) + 1) - log (n : ℝ) ≤ 1 / (n : ℝ) := by
      have : log ((n : ℝ) + 1) - log (n : ℝ) = log (1 + 1 / (n : ℝ)) := by
        rw [← log_div (by positivity) hn_pos_real.ne']
        congr 1; rw [add_div, div_self hn_pos_real.ne']
      rw [this]
      have := log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
      linarith
    have h_gamma_diff : eulerMascheroniConstant - eulerMascheroniSeq n ≤ 1 / (n : ℝ) := by
      calc eulerMascheroniConstant - eulerMascheroniSeq n ≤ eulerMascheroniSeq' n - eulerMascheroniSeq n := by linarith
        _ = log ((n : ℝ) + 1) - log (n : ℝ) := h_diff
        _ ≤ 1 / (n : ℝ) := h_diff_le
    have h_lower : -(1 / (n : ℝ)) ≤ eulerMascheroniSeq n - eulerMascheroniConstant := by linarith
    calc -(2 / y) ≤ -(1 / (n : ℝ)) := by
          have h1 : y / 2 ≤ (n : ℝ) := by
            have : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
              have : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn_pos)
              linarith
            linarith
          have h2 : 1 / (n : ℝ) ≤ 2 / y := by
            have : 1 / (n : ℝ) = (2 / 2) / (n : ℝ) := by norm_num
            rw [this]
            have : (2 / 2 : ℝ) / (n : ℝ) = 2 / (2 * (n : ℝ)) := by ring
            rw [this]
            apply div_le_div_of_nonneg_left (by positivity) hy_pos
            linarith
          linarith
        _ ≤ eulerMascheroniSeq n - eulerMascheroniConstant := h_lower
        _ = harmonic n - log ((n : ℝ) + 1) - eulerMascheroniConstant := by rw [h_seq]
        _ ≤ harmonic n - log y - eulerMascheroniConstant := by linarith
  · have h_diff_le : log ((n : ℝ) + 1) - log (n : ℝ) ≤ 1 / (n : ℝ) := by
      have : log ((n : ℝ) + 1) - log (n : ℝ) = log (1 + 1 / (n : ℝ)) := by
        rw [← log_div (by positivity) hn_pos_real.ne']
        congr 1; rw [add_div, div_self hn_pos_real.ne']
      rw [this]
      have := log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
      linarith
    calc harmonic n - log y - eulerMascheroniConstant ≤ harmonic n - log (n : ℝ) - eulerMascheroniConstant := by linarith
      _ = eulerMascheroniSeq' n - eulerMascheroniConstant := by rw [h_seq']
      _ ≤ eulerMascheroniSeq' n - eulerMascheroniSeq n := by linarith
      _ = log ((n : ℝ) + 1) - log (n : ℝ) := by rw [h_seq, h_seq']; ring
      _ ≤ 1 / (n : ℝ) := h_diff_le
      _ ≤ 2 / y := by
        have h1 : y / 2 ≤ (n : ℝ) := by
          have : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
            have : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn_pos)
            linarith
          linarith
        have : 1 / (n : ℝ) = (2 / 2) / (n : ℝ) := by norm_num
        rw [this]
        have : (2 / 2 : ℝ) / (n : ℝ) = 2 / (2 * (n : ℝ)) := by ring
        rw [this]
        apply div_le_div_of_nonneg_left (by positivity) hy_pos
        linarith

/-- The logarithmic primitive used in the sum comparison for Lemma 3, p. 62. -/
lemma integral_log_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, log t / t) = (log b)^2 / 2 - (log a)^2 / 2 := by
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  apply integral_eq_sub_of_hasDerivAt
  · intro t ht
    convert ((Real.hasDerivAt_log (hpos t ht).ne').pow 2).div_const 2 using 1; ring
  · exact ((continuousOn_log.mono fun t ht => (hpos t ht).ne').div
      continuousOn_id (fun t ht => (hpos t ht).ne')).intervalIntegrable


/-- Integer cutoff comparison derived for the convolution route to Lemma 3, p. 62. -/
lemma sum_log_div_nat (n : ℕ) (hn : 3 ≤ n) :
    |∑ d ∈ Ioc 0 n, log d / d - (log n)^2 / 2| ≤ 10 := by
  have hanti : AntitoneOn (fun t : ℝ => log t / t) (Set.Ici 3) :=
    log_div_self_antitoneOn.mono (Set.Ici_subset_Ici.mpr (by have := exp_one_lt_d9; linarith))
  have hlow := AntitoneOn.integral_le_sum_Ico (f := fun t : ℝ => log t / t)
    (show 3 ≤ n + 1 by omega) (hanti.mono (by intro t ht; exact ht.1))
  have hupp := AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => log t / t)
    hn (hanti.mono (by intro t ht; exact ht.1))
  have hs1 : ∑ d ∈ Ioc 0 n, log (d : ℝ) / d =
      log 2 / 2 + ∑ d ∈ Ico 3 (n + 1), log (d : ℝ) / d := by
    rw [show Ioc 0 n = Ioc 0 2 ∪ Ico 3 (n+1) by ext d; simp; omega,
      sum_union (by apply disjoint_left.mpr; intro d h1 h2; simp at h1 h2; omega)]
    norm_num [sum_Ioc_succ_top]
  have hs2 : ∑ d ∈ Ioc 0 n, log (d : ℝ) / d =
      log 2 / 2 + log 3 / 3 + ∑ d ∈ Ico 3 n, log (d + 1 : ℝ) / (d+1) := by
    rw [show Ioc 0 n = Ioc 0 3 ∪ Ioc 3 n by ext d; simp; omega,
      sum_union (by apply disjoint_left.mpr; intro d h1 h2; simp at h1 h2; omega)]
    rw [← Ico_add_one_add_one_eq_Ioc 3 n, ← sum_Ico_add']
    norm_num [sum_Ioc_succ_top]
  rw [integral_log_div (by norm_num) (by exact_mod_cast (show 3 ≤ n+1 by omega))] at hlow
  rw [integral_log_div (by norm_num) (by exact_mod_cast hn)] at hupp
  simp only [Nat.cast_add, Nat.cast_one] at hlow hupp
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl0 : 0 ≤ log (n : ℝ) := log_nonneg (by linarith)
  have hl1 : log (n : ℝ) ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
  have hl2 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hl3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  have hl2b : log (2 : ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hl3b : log (3 : ℝ) ≤ 2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  rw [abs_le]
  constructor
  · rw [hs1]
    nlinarith
  · rw [hs2]
    nlinarith

/-- LEAF. Unit U-1544. Σ_{d ≤ x} log d/d = ½ log² x + O(1) for x ≥ 1, by comparison with
∫_1^x log t/t dt, the function log t/t being decreasing for t ≥ e. Route for Lemma 3, p. 62. -/
theorem sum_log_div_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ d ∈ Ioc 0 ⌊x⌋₊, log d / d - (log x) ^ 2 / 2| ≤ C := by
  refine ⟨20, by norm_num, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ log x := log_nonneg hx
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.floor_pos.mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hln : 0 ≤ log (n : ℝ) := log_nonneg hnR
  have hnlx : log (n : ℝ) ≤ log x := log_le_log (by linarith) hnx
  have hloggap : log x - log n ≤ 1 / n := by
    rw [← log_div hx0.ne' (by linarith)]
    have h := log_le_sub_one_of_pos (div_pos hx0 (by linarith : (0:ℝ)<n))
    have hr : x / n - 1 ≤ 1 / n := by
      rw [sub_le_iff_le_add, div_le_iff₀ (by linarith : (0:ℝ)<n)]
      field_simp
      nlinarith
    exact h.trans hr
  have hlxbound : log x ≤ (n : ℝ) := by
    have := log_le_sub_one_of_pos hx0
    linarith
  have hg : (log x)^2 / 2 - (log n)^2 / 2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hloggap (show 0 ≤ log x + log n by linarith)
    have hsum : log x + log n ≤ 2 * (n : ℝ) := by linarith
    have hm2 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / (n : ℝ) by positivity)
    have he : 1 / (n : ℝ) * (2 * n) = 2 := by field_simp
    nlinarith
  by_cases hn3 : 3 ≤ n
  · have h := sum_log_div_nat n hn3
    rw [abs_le] at h ⊢
    constructor <;> nlinarith
  · have hn2 : n = 1 ∨ n = 2 := by omega
    have hnn : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
    have hlx3 : log x ≤ log 3 := log_le_log hx0 (by linarith)
    have hl3 : log (3:ℝ) ≤ 2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
    have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
    have hl2b : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
    rcases hn2 with hn2 | hn2
    · rw [hn2]
      norm_num [sum_Ioc_succ_top]
      rw [abs_le]
      constructor <;> nlinarith
    · rw [hn2]
      norm_num [sum_Ioc_succ_top]
      rw [abs_le]
      constructor <;> nlinarith

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma hK_multiplicative (K : ℕ) : (hK K).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨by simp [hK], ?_⟩
  intro m n hm hn hmn
  have hs : Squarefree (m*n) ↔ Squarefree m ∧ Squarefree n := Nat.squarefree_mul hmn
  have hc : (m*n).Coprime K ↔ m.Coprime K ∧ n.Coprime K := Nat.coprime_mul_iff_left
  change (if m*n ≠ 0 ∧ Squarefree (m*n) ∧ (m*n).Coprime K then _ else _) =
    (if m ≠ 0 ∧ Squarefree m ∧ m.Coprime K then _ else _) *
    (if n ≠ 0 ∧ Squarefree n ∧ n.Coprime K then _ else _)
  rw [Nat.primeFactors_mul hm hn, prod_union (hmn.disjoint_primeFactors)]
  simp only [hs, hc]
  split_ifs <;> simp_all

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma invW_multiplicative : invW.IsMultiplicative := by
  refine ⟨by simp [invW], fun {m n} hmn => ?_⟩
  simp [invW, Nat.cast_mul]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma muW_multiplicative : muW.IsMultiplicative := by
  refine ⟨by simp [muW], fun {m n} hmn => ?_⟩
  change (μ (m*n) : ℝ) / (m*n : ℕ) = ((μ m : ℝ) / m) * ((μ n : ℝ) / n)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
  push_cast
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_multiplicative (K : ℕ) : (rhoK K).IsMultiplicative :=
  ((hK_multiplicative K).mul muW_multiplicative).mul muW_multiplicative

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma convolution_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f*g) (p^k) = ∑ i ∈ range (k+1), f (p^i) * g (p^(k-i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  have hi0 := mem_range.mp hi
  rw [Nat.pow_div (by omega : i ≤ k) hp.pos]

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma hK_one (K : ℕ) : hK K 1 = 1 := by simp [hK]

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma hK_prime_pow_zero (K : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    hK K (p^k) = 0 := by
  have hs : ¬ Squarefree (p^k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega : k ≠ 0)]
    omega
  simp [hK, hs]

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma muW_prime_pow_zero {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    muW (p^k) = 0 := by
  simp [muW, ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0),
    show k ≠ 1 by omega]

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma mul_muW_prime_pow (f : ArithmeticFunction ℝ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (f * muW) (p^k) = f (p^k) - f (p^(k-1)) / p := by
  rw [mul_comm, convolution_prime_pow muW f hp]
  have hsub : ({0,1} : Finset ℕ) ⊆ range (k+1) := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [mem_range] <;> omega
  rw [← sum_subset hsub (by
    intro i hi hnot
    have hi2 : 2 ≤ i := by simp only [mem_insert, mem_singleton, not_or] at hnot; omega
    rw [muW_prime_pow_zero hp hi2, zero_mul])]
  simp [muW, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime (K : ℕ) {p : ℕ} (hp : p.Prime) :
    rhoK K p = hK K p - 2 / p := by
  have h1 := mul_muW_prime_pow (hK K) hp (by norm_num : 1 ≤ 1)
  have h2 := mul_muW_prime_pow (hK K * muW) hp (by norm_num : 1 ≤ 1)
  norm_num only [pow_one, pow_zero, Nat.sub_self] at h1 h2
  rw [rhoK, h2, h1]
  simp only [ArithmeticFunction.mul_apply_one, hK_one]
  norm_num [muW]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_sq (K : ℕ) {p : ℕ} (hp : p.Prime) :
    rhoK K (p^2) = 1 / (p : ℝ)^2 - 2 * hK K p / p := by
  have h1 := mul_muW_prime_pow (hK K) hp (by norm_num : 1 ≤ 1)
  have h2 := mul_muW_prime_pow (hK K) hp (by norm_num : 1 ≤ 2)
  have h3 := mul_muW_prime_pow (hK K * muW) hp (by norm_num : 1 ≤ 2)
  norm_num only [pow_one, pow_zero, Nat.reduceSub] at h1 h2 h3
  rw [rhoK, h3, h2, h1, hK_prime_pow_zero K hp (by norm_num), hK_one]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_cube (K : ℕ) {p : ℕ} (hp : p.Prime) :
    rhoK K (p^3) = hK K p / (p : ℝ)^2 := by
  have h2 := mul_muW_prime_pow (hK K) hp (by norm_num : 1 ≤ 2)
  have h3 := mul_muW_prime_pow (hK K) hp (by norm_num : 1 ≤ 3)
  have h4 := mul_muW_prime_pow (hK K * muW) hp (by norm_num : 1 ≤ 3)
  norm_num only [pow_one, Nat.reduceSub] at h2 h3 h4
  rw [rhoK, h4, h3, h2, hK_prime_pow_zero K hp (by norm_num), hK_prime_pow_zero K hp (by norm_num)]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_pow_zero (K : ℕ) {p k : ℕ} (hp : p.Prime) (hk : 4 ≤ k) :
    rhoK K (p^k) = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 1 ≤ k-1 := by omega
  rw [rhoK, mul_muW_prime_pow _ hp hk1, mul_muW_prime_pow _ hp hk1,
    mul_muW_prime_pow _ hp hk2]
  rw [hK_prime_pow_zero K hp (by omega), hK_prime_pow_zero K hp (by omega),
    hK_prime_pow_zero K hp (by omega)]
  ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma hK_prime (K : ℕ) {p : ℕ} (hp : p.Prime) :
    hK K p = if p ∣ K then 0 else 2 / ((p : ℝ)-2) := by
  by_cases hpK : p ∣ K <;>
    simp [hK, hp.ne_zero, hp.squarefree, hp.primeFactors, hp.coprime_iff_not_dvd, hpK]

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_tail_bound {K p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpK : ¬p∣K) :
    |rhoK K p| + |rhoK K (p^2)| + |rhoK K (p^3)| ≤ 27 / (p : ℝ)^2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by positivity
  have hpm : 0 < (p : ℝ)-2 := by linarith
  rw [rhoK_prime K hp, rhoK_prime_sq K hp, rhoK_prime_cube K hp, hK_prime K hp, ite_eq_right hpK]
  have h1 : 2 / ((p:ℝ)-2) - 2/p = 4 / ((p:ℝ)*((p:ℝ)-2)) := by field_simp; ring
  rw [h1, abs_of_nonneg (by positivity)]
  have h2 : |1 / (p:ℝ)^2 - 2 * (2 / ((p:ℝ)-2)) / p| ≤
      1/(p:ℝ)^2 + 4/((p:ℝ)*((p:ℝ)-2)) := by
    have h := abs_sub (1/(p:ℝ)^2) (2*(2/((p:ℝ)-2))/p)
    rw [abs_of_nonneg (show 0 ≤ 1/(p:ℝ)^2 by positivity),
      abs_of_nonneg (show 0 ≤ 2*(2/((p:ℝ)-2))/p by positivity)] at h
    convert h using 1; field_simp; ring
  have h3 : |(2/((p:ℝ)-2))/(p:ℝ)^2| ≤ 2/(p:ℝ)^2 := by
    rw [abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hpm]
    linarith
  have h4 : 4/((p:ℝ)*((p:ℝ)-2)) ≤ 12/(p:ℝ)^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc _ ≤ 4/((p:ℝ)*((p:ℝ)-2)) + (1/(p:ℝ)^2 + 4/((p:ℝ)*((p:ℝ)-2))) + 2/(p:ℝ)^2 := by linarith
    _ = 2*(4/((p:ℝ)*((p:ℝ)-2))) + 3/(p:ℝ)^2 := by ring
    _ ≤ 2*(12/(p:ℝ)^2) + 3/(p:ℝ)^2 := by gcongr
    _ = 27/(p:ℝ)^2 := by ring

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_abs_summable {K : ℕ} (hK2 : 2 ≤ K) :
    Summable (fun p : Nat.Primes => |rhoK K p| + |rhoK K ((p:ℕ)^2)| + |rhoK K ((p:ℕ)^3)|) := by
  have hs : Summable (fun p : Nat.Primes => 27 / (p : ℝ)^2) := by
    have h := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
    convert h.mul_left 27 using 1
    ext p
    rw [Real.rpow_neg (by positivity), show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    ring
  apply hs.of_norm_bounded_eventually
  have he : ∀ᶠ p : Nat.Primes in cofinite, K < (p : ℕ) := by
    rw [Filter.eventually_cofinite]
    have hf := (Set.finite_Iic K).preimage (show Set.InjOn (fun p : Nat.Primes => (p:ℕ)) ((fun p : Nat.Primes => (p:ℕ)) ⁻¹' Set.Iic K) from Subtype.val_injective.injOn)
    convert hf using 1
    ext p
    simp
  filter_upwards [he] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply rhoK_prime_tail_bound p.property (lt_of_le_of_lt hK2 hp)
  intro hd
  have := Nat.le_of_dvd (by omega : 0 < K) hd
  omega

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma summable_of_prime_power_tail {f : ℕ → ℝ} (h0 : f 0 = 0) (hnn : ∀ n, 0 ≤ f n)
    (h1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hpow : ∀ {p k : ℕ}, p.Prime → 4 ≤ k → f (p^k) = 0)
    (hb : Summable (fun p : Nat.Primes => f p + f ((p:ℕ)^2) + f ((p:ℕ)^3))) :
    Summable f := by
  have hloc {p : ℕ} (hp : p.Prime) : HasSum (fun k : ℕ => f (p^k))
      (1 + f p + f (p^2) + f (p^3)) := by
    have hz : ∀ k ∉ range 4, f (p^k) = 0 := by
      intro k hk
      exact hpow hp (by simpa using hk)
    convert hasSum_sum_of_ne_finset_zero hz using 1
    · norm_num [sum_range_succ, h1]
    · infer_instance
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖f (p^k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnn _)] using (hloc hp).summable
  let C : ℝ := tsum (fun p : Nat.Primes => f p + f ((p:ℕ)^2) + f ((p:ℕ)^3))
  have hC (N : ℕ) : ∑ p ∈ N.primesBelow, (f p + f (p^2) + f (p^3)) ≤ C := by
    rw [← sum_subtype_of_mem (p := Nat.Prime) (fun p : ℕ => f p + f (p^2) + f (p^3))
      (fun p hp => Nat.prime_of_mem_primesBelow hp)]
    exact Summable.sum_le_tsum (L := SummationFilter.unconditional Nat.Primes) _ (fun p _ => by linarith [hnn p, hnn ((p:ℕ)^2), hnn ((p:ℕ)^3)]) hb
  refine summable_of_sum_range_le (c := Real.exp C) hnn fun N => ?_
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := f) h1 (fun h => hmul h) (fun hp => hnorm hp) N).2
  have H' := (hasSum_subtype_iff_indicator (f := f) (s := (N.smoothNumbers : Set ℕ))).mp H
  have e1 : ∑ n ∈ range N, f n = ∑ n ∈ range N, (N.smoothNumbers : Set ℕ).indicator f n := by
    apply sum_congr rfl
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | hpos
    · subst n; rw [Set.indicator_apply]; split_ifs <;> simp [h0]
    · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (mem_range.mp hn))]
  rw [e1]
  calc _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p^k) := by
        apply sum_le_hasSum _ _ H'
        intro i _
        by_cases hi : i ∈ (N.smoothNumbers : Set ℕ)
        · rw [Set.indicator_of_mem hi]; exact hnn i
        · rw [Set.indicator_of_notMem hi]
    _ = ∏ p ∈ N.primesBelow, (1 + (f p + f (p^2) + f (p^3))) := by
        apply prod_congr rfl
        intro p hp
        rw [(hloc (Nat.prime_of_mem_primesBelow hp)).tsum_eq]
        ring
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (f p + f (p^2) + f (p^3)) :=
        prod_le_prod₀ (fun p _ => by linarith [hnn p, hnn (p^2), hnn (p^3)])
          (fun p _ => by linarith [Real.add_one_le_exp (f p + f (p^2) + f (p^3))])
    _ = Real.exp (∑ p ∈ N.primesBelow, (f p + f (p^2) + f (p^3))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp C := Real.exp_le_exp.mpr (hC N)

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_summable {K : ℕ} (hK2 : 2 ≤ K) : Summable (fun n => |rhoK K n|) := by
  apply summable_of_prime_power_tail
  · simp
  · intro n; positivity
  · rw [(rhoK_multiplicative K).map_one]; norm_num
  · intro m n hmn
    rw [(rhoK_multiplicative K).map_mul_of_coprime hmn, abs_mul]
  · intro p k hp hk
    rw [rhoK_prime_pow_zero K hp hk, abs_zero]
  · exact rhoK_prime_abs_summable hK2

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_prime_hasSum (K : ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => rhoK K (p^k)) ((1 - 1/(p:ℝ))^2 * (1 + hK K p)) := by
  have hz : ∀ k ∉ range 4, rhoK K (p^k) = 0 := by
    intro k hk
    exact rhoK_prime_pow_zero K hp (by simpa using hk)
  convert hasSum_sum_of_ne_finset_zero hz using 1
  · norm_num [sum_range_succ, (rhoK_multiplicative K).map_one, rhoK_prime K hp,
      rhoK_prime_sq K hp, rhoK_prime_cube K hp]
    ring
  · infer_instance

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_weighted_summable {K : ℕ} (hK2 : 2 ≤ K) :
    Summable (fun n : ℕ => |rhoK K n| * (n:ℝ)^(1/4:ℝ)) := by
  let f : ℕ → ℝ := fun n => |rhoK K n| * (n:ℝ)^(1/4:ℝ)
  have hf0 : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; positivity
  apply summable_of_prime_power_tail (f := f)
  · simp [f]
  · exact hf0
  · simp [f, (rhoK_multiplicative K).map_one]
  · intro m n hmn
    dsimp [f]
    rw [(rhoK_multiplicative K).map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  · intro p k hp hk
    dsimp [f]
    rw [rhoK_prime_pow_zero K hp hk, abs_zero, zero_mul]
  · have hs : Summable (fun p : Nat.Primes => 27 * (p:ℝ)^(-5/4:ℝ)) :=
      ((Nat.Primes.summable_rpow (r := -5/4)).mpr (by norm_num)).mul_left 27
    apply hs.of_norm_bounded_eventually
    have he : ∀ᶠ p : Nat.Primes in cofinite, K < (p:ℕ) := by
      rw [Filter.eventually_cofinite]
      have hf := (Set.finite_Iic K).preimage
        (show Set.InjOn (fun p : Nat.Primes => (p:ℕ)) ((fun p : Nat.Primes => (p:ℕ)) ⁻¹' Set.Iic K) from Subtype.val_injective.injOn)
      convert hf using 1
      ext p
      simp
    filter_upwards [he] with p hp
    have hp2 : 2 < (p:ℕ) := lt_of_le_of_lt hK2 hp
    have hpK : ¬(p:ℕ)∣K := by
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < K) hd
      omega
    have hp0 : (0:ℝ) < p := by positivity
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
    have hpow (j : ℕ) (hj : j ≤ 3) : (((p:ℕ)^j:ℕ):ℝ)^(1/4:ℝ) ≤ (p:ℝ)^(3/4:ℝ) := by
      rw [Nat.cast_pow, ← rpow_natCast_mul (by positivity)]
      apply rpow_le_rpow_of_exponent_le hp1
      have hcast : (j:ℝ) ≤ 3 := by exact_mod_cast hj
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hf0 p, hf0 ((p:ℕ)^2), hf0 ((p:ℕ)^3)])]
    dsimp [f]
    calc _ ≤ |rhoK K p| * (p:ℝ)^(3/4:ℝ) + |rhoK K ((p:ℕ)^2)| * (p:ℝ)^(3/4:ℝ) +
          |rhoK K ((p:ℕ)^3)| * (p:ℝ)^(3/4:ℝ) := by
            gcongr
            · norm_num
            · exact hpow 2 (by norm_num)
            · exact hpow 3 (by norm_num)
      _ = (|rhoK K p| + |rhoK K ((p:ℕ)^2)| + |rhoK K ((p:ℕ)^3)|) * (p:ℝ)^(3/4:ℝ) := by ring
      _ ≤ (27 / (p:ℝ)^2) * (p:ℝ)^(3/4:ℝ) :=
        mul_le_mul_of_nonneg_right (rhoK_prime_tail_bound p.property hp2 hpK) (by positivity)
      _ = 27 * (p:ℝ)^(-5/4:ℝ) := by
        rw [div_eq_mul_inv, ← rpow_natCast, ← rpow_neg hp0.le,
          mul_assoc, ← rpow_add hp0]
        norm_num

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_fixed_moment {K : ℕ} (hK2 : 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d)^2 ≤ C := by
  have hw := rhoK_weighted_summable hK2
  refine ⟨81 * ∑' d : ℕ, |rhoK K d| * (d:ℝ)^(1/4:ℝ), ?_, fun n => ?_⟩
  · exact mul_nonneg (by norm_num) (tsum_nonneg fun d => by positivity)
  · calc _ ≤ ∑ d ∈ Ioc 0 n, 81 * (|rhoK K d| * (d:ℝ)^(1/4:ℝ)) := by
          apply sum_le_sum
          intro d hd
          have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
          have hl : log (d:ℝ) ≤ (d:ℝ)^(1/8:ℝ) / (1/8:ℝ) :=
            log_le_rpow_div (by positivity) (by norm_num)
          have hr : 1 ≤ (d:ℝ)^(1/8:ℝ) := one_le_rpow hd1 (by norm_num)
          have hl0 : 0 ≤ 1 + log (d:ℝ) := by linarith [log_nonneg hd1]
          have hsq : (1 + log (d:ℝ))^2 ≤ 81 * (d:ℝ)^(1/4:ℝ) := by
            have hp : ((d:ℝ)^(1/8:ℝ))^2 = (d:ℝ)^(1/4:ℝ) := by
              rw [← rpow_mul_natCast (by positivity)]
              norm_num
            rw [← hp]
            norm_num at hl
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hsq (abs_nonneg (rhoK K d))]
      _ = 81 * ∑ d ∈ Ioc 0 n, |rhoK K d| * (d:ℝ)^(1/4:ℝ) := by rw [mul_sum]
      _ ≤ 81 * ∑' d : ℕ, |rhoK K d| * (d:ℝ)^(1/4:ℝ) :=
        mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun d _ => by positivity)) (by norm_num)

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma rhoK_moment_bounded_modulus (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 2 ≤ K → K ≤ B → ∀ n : ℕ,
      ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d)^2 ≤ C * √(log K) := by
  induction B with
  | zero => exact ⟨1, by norm_num, fun K hK hB => by omega⟩
  | succ B ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    by_cases hB : 2 ≤ B+1
    · obtain ⟨D, hD0, hD⟩ := rhoK_fixed_moment hB
      have hlog : 0 < log (B+1:ℕ) := log_pos (by exact_mod_cast hB)
      have hs : 0 < √(log (B+1:ℕ)) := sqrt_pos.mpr hlog
      refine ⟨C + (D+1)/√(log (B+1:ℕ)), by positivity, fun K hK hKB n => ?_⟩
      by_cases hk : K ≤ B
      · have hb := hbound K hK hk n
        have hpos : 0 ≤ (D+1)/√(log (B+1:ℕ)) := by positivity
        have hroot := sqrt_nonneg (log (K:ℝ))
        nlinarith
      · have he : K = B+1 := by omega
        subst K
        have heq : (C + (D+1)/√(log (B+1:ℕ))) * √(log (B+1:ℕ)) =
            C * √(log (B+1:ℕ)) + D + 1 := by field_simp; ring
        rw [heq]
        have := hD n
        have := mul_pos hC hs
        linarith
    · exact ⟨C, hC, fun K hK hKB => by omega⟩

/-- Derived arithmetic helper for the convolution route to Lemma 3, p. 62. -/
lemma no_uniform_log_sqrt_bound :
    ¬ ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → log K ≤ C * √(log K) := by
  rintro ⟨C, hC⟩
  have ht : Tendsto (fun K : ℕ => √(log (K:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (|C|+1))
  let N := max K 2
  have hN : 2 ≤ N := le_max_right _ _
  have hs : |C| + 1 ≤ √(log (N:ℝ)) := hK N (le_max_left _ _)
  have hl : 0 ≤ log (N:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have he := sq_sqrt hl
  have hb := hC N hN
  have hc := le_abs_self C
  have hp : 0 < √(log (N:ℝ)) := by linarith [abs_nonneg C]
  have hmul : (√(log (N:ℝ)))^2 ≤ C * √(log (N:ℝ)) := by rwa [he]
  have hroot : √(log (N:ℝ)) ≤ C := by nlinarith
  linarith

/-- The product defining T on p. 61 converges. Its excess over one is bounded by 3/p squared. -/
theorem Ttwin_multipliable : Multipliable (fun p : Nat.Primes => if (p : ℕ) = 2 then (1 : ℝ) else
    ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  let u : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 0 else
    1 / ((p : ℝ) * ((p : ℝ) - 2))
  have hu0 : ∀ p, 0 ≤ u p := by
    intro p
    dsimp [u]
    split_ifs with h
    · exact le_rfl
    · have hp2 : 2 < (p : ℕ) := lt_of_le_of_ne p.property.two_le (Ne.symm h)
      have hpR : (2 : ℝ) < (p : ℕ) := by exact_mod_cast hp2
      positivity
  have hs : Summable (fun p : Nat.Primes => 3 / (p : ℝ)^2) := by
    have h := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
    convert h.mul_left 3 using 1
    ext p
    rw [Real.rpow_neg (by positivity), show (2 : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
    ring
  have hu : Summable u := hs.of_nonneg_of_le hu0 (by
    intro p
    dsimp [u]
    split_ifs with h
    · positivity
    · have hp2 : 2 < (p : ℕ) := lt_of_le_of_ne p.property.two_le (Ne.symm h)
      have hpR : (3 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp2
      have hpPos : 0 < (p : ℝ) - 2 := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith)
  convert Real.multipliable_one_add_of_summable hu using 1
  ext p
  dsimp [u]
  split_ifs with h
  · norm_num
  · have hp2 : 2 < (p : ℕ) := lt_of_le_of_ne p.property.two_le (Ne.symm h)
    have hpR : (2 : ℝ) < (p : ℕ) := by exact_mod_cast hp2
    field_simp
    ring


set_option backward.isDefEq.respectTransparency false in
/-- LEAF. Unit U-1544. Euler product: for even K ≥ 2, Σ_d ρ_K(d) converges to T Q(K)/4 = 2C_K.
The local factor at p is (p - 1)²/p², which is 1/4 at p = 2, at an odd p ∣ K, and
(p - 1)²/(p(p - 2)) at p ∤ K. Route: `EulerProduct.eulerProduct_hasProd` with
fixed K absolute summability from `rhoK_summable`. Route for Lemma 3, p. 62. -/
theorem rhoK_hasSum {K : ℕ} (hK : Even K) (hK2 : 2 ≤ K) :
    HasSum (fun d => rhoK K d) (Ttwin * Q K / 4) := by
  have hKn : K ≠ 0 := by omega
  let S := K.primeFactors.filter (2 < ·)
  let c : Nat.Primes → ℝ := fun p => if (p:ℕ) ∈ S then ((p:ℝ)-2)/p else 1
  have hc : HasProd c (Q K) := by
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Nat.Primes) (s := S.subtype Nat.Prime) (f := c) (fun p hp => by
      dsimp [c]
      rw [ite_eq_right (fun h => hp (mem_subtype.mpr h))])
    convert h using 1
    change Q K = ∏ p ∈ S.subtype Nat.Prime, c p
    rw [show (∏ p ∈ S.subtype Nat.Prime, c p) = ∏ p ∈ S.subtype Nat.Prime, ((p:ℝ)-2)/p by
      apply prod_congr rfl; intro p hp; exact ite_eq_left (mem_subtype.mp hp)]
    exact (prod_subtype_of_mem (fun p : ℕ => ((p:ℝ)-2)/p)
      (fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).symm
  let c2 : Nat.Primes → ℝ := fun p => if (p:ℕ) = 2 then 1/4 else 1
  have hc2 : HasProd c2 (1/4) := by
    convert hasProd_ite_eq (β := Nat.Primes) (⟨2, Nat.prime_two⟩ : Nat.Primes) (1/4 : ℝ) using 1
    funext p
    simp only [c2, ← Nat.Primes.coe_nat_inj]
  have hT : HasProd (fun p : Nat.Primes => if (p:ℕ)=2 then 1 else
      ((p:ℝ)-1)^2 / ((p:ℝ)*((p:ℝ)-2))) Ttwin := Ttwin_multipliable.hasProd
  have hprod := (hT.mul hc2).mul hc
  have hloc : (fun p : Nat.Primes => (if (p:ℕ)=2 then 1 else
      ((p:ℝ)-1)^2 / ((p:ℝ)*((p:ℝ)-2))) * c2 p * c p) =
      (fun p : Nat.Primes => ∑' k : ℕ, rhoK K ((p:ℕ)^k)) := by
    funext p
    rw [(rhoK_prime_hasSum K p.property).tsum_eq, hK_prime K p.property]
    dsimp [c, c2, S]
    by_cases hp2 : (p:ℕ) = 2
    · have hpK : (p:ℕ) ∣ K := hp2 ▸ even_iff_two_dvd.mp hK
      simp [hp2]
      norm_num
    · have hpR : (2:ℝ) < p := by
        have := p.property.two_le
        exact_mod_cast (show 2 < (p:ℕ) by omega)
      have hpN : (p:ℕ) ≠ 0 := p.property.ne_zero
      have hpNat : 2 < (p:ℕ) := by exact_mod_cast hpR
      simp only [mem_filter, Nat.mem_primeFactors_of_ne_zero hKn, p.property, true_and,
        hpNat, and_true, ite_eq_right hp2]
      by_cases hd : (p:ℕ) ∣ K <;> simp only [hd, ite_true, ite_false] <;> field_simp <;> ring
  rw [hloc] at hprod
  have hE := (rhoK_multiplicative K).eulerProduct_hasProd
    (by simpa only [Real.norm_eq_abs] using rhoK_summable hK2)
  have heq := hE.unique hprod
  have hs : Summable (fun d => rhoK K d) := (rhoK_summable hK2).of_abs
  convert hs.hasSum using 1
  rw [heq]
  ring

/-- LEAF. Unit U-1544. Moment bound, uniform in K: Σ_{d ≤ n} |ρ_K(d)| (1 + log d)² ≤ C √(log K)
for even K ≥ 2. ρ_K is multiplicative, supported on cube free times p³, with
|ρ_K(p)| ≤ 2/p at p ∣ K and ≤ 4/(p(p - 2)) at p ∤ K; the full sum is ≪ (log log K)⁴. Route for
Lemma 3, p. 62. -/
theorem rhoK_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, Even K → 2 ≤ K → ∀ n : ℕ,
      ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d) ^ 2 ≤ C * √(log K) := by
  sorry

/-- Σ_{n ≤ y} τ(n)/n = ½ log² y + 2γ log y + O(1) for y ≥ 1.
Unconditional assembly from `harmonic_asymp`, `sum_log_div_asymp`, with Mathlib
`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`. -/
theorem Tsum_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Ioc 0 ⌊y⌋₊, tauW n - (log y) ^ 2 / 2 - 2 * eulerMascheroniConstant * log y| ≤ C := by
  obtain ⟨Cb, hCb0, hCb⟩ := sum_log_div_asymp
  refine ⟨Cb + 6, by linarith, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set γ := eulerMascheroniConstant with hγ
  have hγ1 : γ < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 1 / 2 < γ := one_half_lt_eulerMascheroniConstant
  set X := ⌊x⌋₊ with hX
  have hXx : (X : ℝ) ≤ x := Nat.floor_le hx0.le
  have hlx : 0 ≤ log x := log_nonneg hx
  rw [tauW, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  -- per-d harmonic error
  have hH : ∀ d ∈ Ioc 0 X, |∑ m ∈ Ioc 0 (X / d), invW m - (log x - log d + γ)| ≤ 2 * d / x := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Ioc.mp hd).1
    have hdX : d ≤ X := (mem_Ioc.mp hd).2
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hdx : (d : ℝ) ≤ x := le_trans (by exact_mod_cast hdX) hXx
    have hy : 1 ≤ x / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have h := harmonic_asymp hy
    rw [Nat.floor_div_natCast, log_div hx0.ne' (by positivity)] at h
    rw [show 2 * (d : ℝ) / x = 2 / (x / d) by field_simp]
    convert h using 2; ring
  set E : ℕ → ℝ := fun d => ∑ m ∈ Ioc 0 (X / d), invW m - (log x - log d + γ) with hE
  have hsplit : ∑ d ∈ Ioc 0 X, invW d * ∑ m ∈ Ioc 0 (X / d), invW m =
      (log x + γ) * ∑ d ∈ Ioc 0 X, invW d - ∑ d ∈ Ioc 0 X, log d / d +
        ∑ d ∈ Ioc 0 X, invW d * E d := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    simp only [hE, invW_apply]
    ring
  rw [hsplit]
  have hH0 := harmonic_asymp hx
  have hHX : ∑ d ∈ Ioc 0 X, invW d = log x + γ + (∑ d ∈ Ioc 0 X, invW d - log x - γ) := by ring
  set e0 := ∑ d ∈ Ioc 0 X, invW d - log x - γ with he0
  have hF := hCb x hx
  set F := ∑ d ∈ Ioc 0 X, log d / d - (log x) ^ 2 / 2 with hFdef
  have hlogd : ∑ d ∈ Ioc 0 X, log d / d = (log x) ^ 2 / 2 + F := by rw [hFdef]; ring
  have hEsum : |∑ d ∈ Ioc 0 X, invW d * E d| ≤ 2 := by
    calc |∑ d ∈ Ioc 0 X, invW d * E d| ≤ ∑ d ∈ Ioc 0 X, |invW d * E d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 X, 2 / x := by
          refine sum_le_sum fun d hd => ?_
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
          rw [abs_mul]
          have hi : |invW d| = (d : ℝ)⁻¹ := by
            rw [invW_apply]; exact abs_of_pos (by positivity)
          rw [hi]
          calc (d : ℝ)⁻¹ * |E d| ≤ (d : ℝ)⁻¹ * (2 * d / x) :=
                mul_le_mul_of_nonneg_left (hH d hd) (by positivity)
            _ = 2 / x := by field_simp
      _ = X * (2 / x) := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp
      _ ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ hx0]; nlinarith
  have he0b : |(log x + γ) * e0| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    have hlx1 : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hx0; linarith
    calc (log x + γ) * |e0| ≤ (log x + γ) * (2 / x) := mul_le_mul_of_nonneg_left hH0 (by linarith)
      _ ≤ 2 := by rw [mul_div_assoc', div_le_iff₀ hx0]; nlinarith
  rw [hHX, hlogd]
  have hγsq : γ ^ 2 ≤ 1 := by nlinarith
  calc |(log x + γ) * (log x + γ + e0) - ((log x) ^ 2 / 2 + F) +
        ∑ d ∈ Ioc 0 X, invW d * E d - (log x) ^ 2 / 2 - 2 * γ * log x|
      = |γ ^ 2 + (log x + γ) * e0 - F + ∑ d ∈ Ioc 0 X, invW d * E d| := by ring_nf
    _ ≤ |γ ^ 2| + |(log x + γ) * e0| + |F| + |∑ d ∈ Ioc 0 X, invW d * E d| := by
        have := abs_add_le (γ ^ 2 + (log x + γ) * e0 - F) (∑ d ∈ Ioc 0 X, invW d * E d)
        have := abs_sub (γ ^ 2 + (log x + γ) * e0) F
        have := abs_add_le (γ ^ 2) ((log x + γ) * e0)
        linarith
    _ ≤ Cb + 6 := by rw [abs_of_nonneg (sq_nonneg γ)]; linarith

/-- The partial sums of ρ_K approach T Q(K)/4 at rate √(log K)/(1 + log x)².
Assembly, CONDITIONAL ON `rhoK_moment`. The Euler sum is proved independently. -/
theorem rhoK_partial :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, Even K → 2 ≤ K → ∀ x : ℝ, 1 ≤ x →
      |∑ d ∈ Ioc 0 ⌊x⌋₊, rhoK K d - Ttwin * Q K / 4| ≤ C * √(log K) / (1 + log x) ^ 2 := by
  obtain ⟨C, hC, hmom⟩ := rhoK_moment
  refine ⟨C, hC, fun K hK hK2 x hx => ?_⟩
  set f : ℕ → ℝ := fun d => rhoK K d with hf
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ log x := log_nonneg hx
  have hden : 0 < (1 + log x) ^ 2 := by positivity
  set X := ⌊x⌋₊ with hX
  have hT := (rhoK_hasSum hK hK2).tendsto_sum_nat
  have hrange : ∀ n, ∑ i ∈ range (n + 1), f i = ∑ i ∈ Ioc 0 n, f i := by
    intro n
    have : range (n + 1) = insert 0 (Ioc 0 n) := by
      ext i; simp only [mem_range, mem_insert, mem_Ioc]; omega
    rw [this, sum_insert (by simp)]
    simp [hf]
  have hT' : Tendsto (fun n => ∑ i ∈ Ioc 0 n, f i) atTop (𝓝 (Ttwin * Q K / 4)) := by
    have := hT.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact hrange n
  have hlim := (hT'.sub_const (∑ i ∈ Ioc 0 X, f i)).abs
  have hbound : ∀ n, X ≤ n → |∑ i ∈ Ioc 0 n, f i - ∑ i ∈ Ioc 0 X, f i| ≤
      C * √(log K) / (1 + log x) ^ 2 := by
    intro n hn
    rw [← sum_Ioc_consecutive f (Nat.zero_le X) hn, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [le_div_iff₀ hden, sum_mul]
    refine le_trans (sum_le_sum fun d hd => ?_) ((sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc_left (Nat.zero_le X)) (fun _ _ _ => by positivity)).trans (hmom K hK hK2 n))
    have hdX : X < d := (mem_Ioc.mp hd).1
    have hdx : x ≤ d := by
      have := Nat.lt_floor_add_one x
      have h2 : (X : ℝ) + 1 ≤ d := by exact_mod_cast hdX
      linarith
    have hl : log x ≤ log d := log_le_log hx0 hdx
    have hsq : (1 + log x) ^ 2 ≤ (1 + log d) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have := le_of_tendsto hlim (eventually_atTop.2 ⟨X, hbound⟩)
  rwa [abs_sub_comm] at this

/-- Derived fixed modulus consequence for the route to Lemma 3, p. 62. -/
theorem rhoK_partial_fixed_modulus {K : ℕ} (hK : Even K) (hK2 : 2 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ d ∈ Ioc 0 ⌊x⌋₊, rhoK K d - Ttwin * Q K / 4| ≤ C / (1 + log x)^2 := by
  obtain ⟨D, hD0, hD⟩ := rhoK_fixed_moment hK2
  let C := D + 1
  have hC : 0 < C := by dsimp [C]; linarith
  have hmom (n : ℕ) : ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d)^2 ≤ C :=
    (hD n).trans (by dsimp [C]; linarith)
  refine ⟨C, hC, fun x hx => ?_⟩
  set f : ℕ → ℝ := fun d => rhoK K d with hf
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ log x := log_nonneg hx
  have hden : 0 < (1 + log x) ^ 2 := by positivity
  set X := ⌊x⌋₊ with hX
  have hT := (rhoK_hasSum hK hK2).tendsto_sum_nat
  have hrange : ∀ n, ∑ i ∈ range (n + 1), f i = ∑ i ∈ Ioc 0 n, f i := by
    intro n
    have : range (n + 1) = insert 0 (Ioc 0 n) := by
      ext i; simp only [mem_range, mem_insert, mem_Ioc]; omega
    rw [this, sum_insert (by simp)]
    simp [hf]
  have hT' : Tendsto (fun n => ∑ i ∈ Ioc 0 n, f i) atTop (𝓝 (Ttwin * Q K / 4)) := by
    have := hT.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp]
    exact hrange n
  have hlim := (hT'.sub_const (∑ i ∈ Ioc 0 X, f i)).abs
  have hbound : ∀ n, X ≤ n → |∑ i ∈ Ioc 0 n, f i - ∑ i ∈ Ioc 0 X, f i| ≤
      C / (1 + log x) ^ 2 := by
    intro n hn
    rw [← sum_Ioc_consecutive f (Nat.zero_le X) hn, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [le_div_iff₀ hden, sum_mul]
    refine le_trans (sum_le_sum fun d hd => ?_) ((sum_le_sum_of_subset_of_nonneg
      (Ioc_subset_Ioc_left (Nat.zero_le X)) (fun _ _ _ => by positivity)).trans (hmom n))
    have hdX : X < d := (mem_Ioc.mp hd).1
    have hdx : x ≤ d := by
      have := Nat.lt_floor_add_one x
      have h2 : (X : ℝ) + 1 ≤ d := by exact_mod_cast hdX
      linarith
    have hl : log x ≤ log d := log_le_log hx0 hdx
    have hsq : (1 + log x) ^ 2 ≤ (1 + log d) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have := le_of_tendsto hlim (eventually_atTop.2 ⟨X, hbound⟩)
  rwa [abs_sub_comm] at this

/-- Derived fixed modulus consequence for the route to Lemma 3, p. 62. -/
theorem lemma3_fixed_modulus {K : ℕ} (hK : Even K) (hK2 : 2 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |G K x - CK K * (log x)^2| ≤ C * (1 + log x) := by
  obtain ⟨C1, hC1, hT⟩ := Tsum_asymp
  obtain ⟨D, hD0, hD⟩ := rhoK_fixed_moment hK2
  let CR := D + 1
  have hCR : 0 < CR := by dsimp [CR]; linarith
  have hmom (n : ℕ) : ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d)^2 ≤ CR :=
    (hD n).trans (by dsimp [CR]; linarith)
  obtain ⟨CP, hCP, hpart⟩ := rhoK_partial_fixed_modulus hK hK2
  refine ⟨(C1 + 3) * CR + CP + 1, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := log x with hL
  have hL0 : 0 ≤ L := log_nonneg hx
  have hK0 : 0 ≤ (1 : ℝ) := by norm_num
  set X := ⌊x⌋₊ with hX
  have hXx : (X : ℝ) ≤ x := Nat.floor_le hx0.le
  have hγ1 : eulerMascheroniConstant < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 1 / 2 < eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant
  have hG : G K x = ∑ d ∈ Ioc 0 X, rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m := by
    rw [G, ← rhoK_mul_tauW, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  -- per-d bound
  have hper : ∀ d ∈ Ioc 0 X, |∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2| ≤
      (C1 + 3) * (1 + L) * (1 + log d) ^ 2 := by
    intro d hd
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hdx : (d : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Ioc.mp hd).2) hXx
    have hy : 1 ≤ x / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have h := hT (x / d) hy
    rw [Nat.floor_div_natCast, log_div hx0.ne' (by positivity)] at h
    set l := log (d : ℝ) with hl
    have hl0 : 0 ≤ l := log_nonneg hdR
    have hlL : l ≤ L := log_le_log (by linarith) hdx
    set Tm := ∑ m ∈ Ioc 0 (X / d), tauW m
    have hkey : Tm - L ^ 2 / 2 = (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l)) +
        (l ^ 2 / 2 - L * l) + 2 * eulerMascheroniConstant * (L - l) := by ring
    rw [hkey]
    have h1 := abs_add_le (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l) +
        (l ^ 2 / 2 - L * l)) (2 * eulerMascheroniConstant * (L - l))
    have h2 := abs_add_le (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l))
        (l ^ 2 / 2 - L * l)
    have h3 : |l ^ 2 / 2 - L * l| ≤ l ^ 2 / 2 + L * l := by
      rw [abs_le]; constructor <;> nlinarith
    have h4 : |2 * eulerMascheroniConstant * (L - l)| ≤ 2 * L := by
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have hP : (1 : ℝ) ≤ (1 + L) * (1 + l) ^ 2 := by nlinarith
    have hP2 : C1 + l ^ 2 / 2 + L * l + 2 * L ≤ (C1 + 3) * ((1 + L) * (1 + l) ^ 2) := by
      nlinarith [mul_nonneg hL0 hl0, mul_nonneg (mul_nonneg hL0 hl0) hl0, sq_nonneg l,
        mul_nonneg hL0 (sq_nonneg l)]
    calc _ ≤ C1 + (l ^ 2 / 2 + L * l) + 2 * L := by linarith
      _ ≤ _ := by rw [mul_assoc]; linarith
  have hA : |G K x - L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d| ≤ (C1 + 3) * (1 + L) * (CR ) := by
    rw [hG, mul_sum, ← sum_sub_distrib]
    calc |∑ d ∈ Ioc 0 X, (rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2 * rhoK K d)|
        ≤ ∑ d ∈ Ioc 0 X, |rhoK K d| * ((C1 + 3) * (1 + L) * (1 + log d) ^ 2) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
          rw [show rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2 * rhoK K d =
            rhoK K d * (∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2) by ring, abs_mul]
          exact mul_le_mul_of_nonneg_left (hper d hd) (abs_nonneg _)
      _ = (C1 + 3) * (1 + L) * ∑ d ∈ Ioc 0 X, |rhoK K d| * (1 + log d) ^ 2 := by
          rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmom X) (by positivity)
  have hB : |L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d - CK K * L ^ 2| ≤ CP  := by
    have hp := hpart x hx
    have hCK : CK K * L ^ 2 = L ^ 2 / 2 * (Ttwin * Q K / 4) := by
      simp only [CK, Cpaper]; ring
    rw [hCK, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have hden : 0 < (1 + L) ^ 2 := by positivity
    have hLL : L ^ 2 / 2 ≤ (1 + L) ^ 2 := by nlinarith
    calc L ^ 2 / 2 * |∑ d ∈ Ioc 0 X, rhoK K d - Ttwin * Q K / 4|
        ≤ (1 + L) ^ 2 * (CP  / (1 + L) ^ 2) :=
          mul_le_mul hLL hp (abs_nonneg _) hden.le
      _ = CP  := by field_simp
  have htri := abs_sub_le (G K x) (L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d) (CK K * L ^ 2)
  have h1L : 1 ≤ 1 + L := by linarith
  calc |G K x - CK K * L ^ 2| ≤ (C1 + 3) * (1 + L) * (CR ) + CP  := by
        linarith
    _ ≤ ((C1 + 3) * CR + CP + 1) * (1 + L)  := by
        nlinarith [mul_nonneg (mul_nonneg hC1 hCR.le) hK0, mul_nonneg hCP.le hK0,
          mul_nonneg (mul_nonneg hCR.le hK0) hL0, mul_nonneg (mul_nonneg hCP.le hK0) hL0,
          mul_nonneg hK0 hL0]

/-- **Lemma 3**, p. 62, in the form used on p. 64: there is C with
|Σ_{m ≤ x, (m, K) = 1} μ²(m)/f₁(m) - C_K log² x| ≤ C (1 + log x) √(log K)
for every even K ≥ 2 and x ≥ 1. Assembly, CONDITIONAL ON the remaining uniform `rhoK_moment` leaf. -/
theorem lemma3 :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, Even K → 2 ≤ K → ∀ x : ℝ, 1 ≤ x →
      |G K x - CK K * (log x) ^ 2| ≤ C * (1 + log x) * √(log K) := by
  obtain ⟨C1, hC1, hT⟩ := Tsum_asymp
  obtain ⟨CR, hCR, hmom⟩ := rhoK_moment
  obtain ⟨CP, hCP, hpart⟩ := rhoK_partial
  refine ⟨(C1 + 3) * CR + CP + 1, by positivity, fun K hK hK2 x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set L := log x with hL
  have hL0 : 0 ≤ L := log_nonneg hx
  have hK0 : 0 ≤ √(log K) := sqrt_nonneg _
  set X := ⌊x⌋₊ with hX
  have hXx : (X : ℝ) ≤ x := Nat.floor_le hx0.le
  have hγ1 : eulerMascheroniConstant < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  have hγ0 : 1 / 2 < eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant
  have hG : G K x = ∑ d ∈ Ioc 0 X, rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m := by
    rw [G, ← rhoK_mul_tauW, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  -- per-d bound
  have hper : ∀ d ∈ Ioc 0 X, |∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2| ≤
      (C1 + 3) * (1 + L) * (1 + log d) ^ 2 := by
    intro d hd
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hdx : (d : ℝ) ≤ x := le_trans (by exact_mod_cast (mem_Ioc.mp hd).2) hXx
    have hy : 1 ≤ x / d := by rw [le_div_iff₀ (by linarith)]; linarith
    have h := hT (x / d) hy
    rw [Nat.floor_div_natCast, log_div hx0.ne' (by positivity)] at h
    set l := log (d : ℝ) with hl
    have hl0 : 0 ≤ l := log_nonneg hdR
    have hlL : l ≤ L := log_le_log (by linarith) hdx
    set Tm := ∑ m ∈ Ioc 0 (X / d), tauW m
    have hkey : Tm - L ^ 2 / 2 = (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l)) +
        (l ^ 2 / 2 - L * l) + 2 * eulerMascheroniConstant * (L - l) := by ring
    rw [hkey]
    have h1 := abs_add_le (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l) +
        (l ^ 2 / 2 - L * l)) (2 * eulerMascheroniConstant * (L - l))
    have h2 := abs_add_le (Tm - (L - l) ^ 2 / 2 - 2 * eulerMascheroniConstant * (L - l))
        (l ^ 2 / 2 - L * l)
    have h3 : |l ^ 2 / 2 - L * l| ≤ l ^ 2 / 2 + L * l := by
      rw [abs_le]; constructor <;> nlinarith
    have h4 : |2 * eulerMascheroniConstant * (L - l)| ≤ 2 * L := by
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have hP : (1 : ℝ) ≤ (1 + L) * (1 + l) ^ 2 := by nlinarith
    have hP2 : C1 + l ^ 2 / 2 + L * l + 2 * L ≤ (C1 + 3) * ((1 + L) * (1 + l) ^ 2) := by
      nlinarith [mul_nonneg hL0 hl0, mul_nonneg (mul_nonneg hL0 hl0) hl0, sq_nonneg l,
        mul_nonneg hL0 (sq_nonneg l)]
    calc _ ≤ C1 + (l ^ 2 / 2 + L * l) + 2 * L := by linarith
      _ ≤ _ := by rw [mul_assoc]; linarith
  have hA : |G K x - L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d| ≤ (C1 + 3) * (1 + L) * (CR * √(log K)) := by
    rw [hG, mul_sum, ← sum_sub_distrib]
    calc |∑ d ∈ Ioc 0 X, (rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2 * rhoK K d)|
        ≤ ∑ d ∈ Ioc 0 X, |rhoK K d| * ((C1 + 3) * (1 + L) * (1 + log d) ^ 2) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
          rw [show rhoK K d * ∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2 * rhoK K d =
            rhoK K d * (∑ m ∈ Ioc 0 (X / d), tauW m - L ^ 2 / 2) by ring, abs_mul]
          exact mul_le_mul_of_nonneg_left (hper d hd) (abs_nonneg _)
      _ = (C1 + 3) * (1 + L) * ∑ d ∈ Ioc 0 X, |rhoK K d| * (1 + log d) ^ 2 := by
          rw [mul_sum]; refine sum_congr rfl fun d _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmom K hK hK2 X) (by positivity)
  have hB : |L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d - CK K * L ^ 2| ≤ CP * √(log K) := by
    have hp := hpart K hK hK2 x hx
    have hCK : CK K * L ^ 2 = L ^ 2 / 2 * (Ttwin * Q K / 4) := by
      simp only [CK, Cpaper]; ring
    rw [hCK, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have hden : 0 < (1 + L) ^ 2 := by positivity
    have hLL : L ^ 2 / 2 ≤ (1 + L) ^ 2 := by nlinarith
    calc L ^ 2 / 2 * |∑ d ∈ Ioc 0 X, rhoK K d - Ttwin * Q K / 4|
        ≤ (1 + L) ^ 2 * (CP * √(log K) / (1 + L) ^ 2) :=
          mul_le_mul hLL hp (abs_nonneg _) hden.le
      _ = CP * √(log K) := by field_simp
  have htri := abs_sub_le (G K x) (L ^ 2 / 2 * ∑ d ∈ Ioc 0 X, rhoK K d) (CK K * L ^ 2)
  have h1L : 1 ≤ 1 + L := by linarith
  calc |G K x - CK K * L ^ 2| ≤ (C1 + 3) * (1 + L) * (CR * √(log K)) + CP * √(log K) := by
        linarith
    _ ≤ ((C1 + 3) * CR + CP + 1) * (1 + L) * √(log K) := by
        nlinarith [mul_nonneg (mul_nonneg hC1 hCR.le) hK0, mul_nonneg hCP.le hK0,
          mul_nonneg (mul_nonneg hCR.le hK0) hL0, mul_nonneg (mul_nonneg hCP.le hK0) hL0,
          mul_nonneg hK0 hL0]

/-! ### The prime sums of p. 64 -/

/-- LEAF. Unit U-1544. Σ_{p ≤ x} log² p/p = ½ log² x + O(log x), the third of the well-known
inequalities on p. 64; by partial summation from `Decomp1528a.mertens1_abs`. -/
theorem sum_logsq_div_primes :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, (log p) ^ 2 / p - (log x) ^ 2 / 2| ≤ C * (1 + log x) := by
  let c : ℕ → ℝ := fun k => if k.Prime then log k / k else 0
  have hc (n : ℕ) : ∑ k ∈ Icc 0 n, c k = ∑ p ∈ Nat.primesLE n, log p / p := by
    dsimp [c]
    rw [← sum_filter]
    apply sum_congr
    · ext k; simp [Nat.mem_primesLE]
    · intro k _; rfl
  have hw (n : ℕ) : ∑ k ∈ Icc 0 n, log k * c k =
      ∑ p ∈ Nat.primesLE n, (log p)^2 / p := by
    dsimp [c]
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    apply sum_congr
    · ext k; simp [Nat.mem_primesLE]
    · intro k _; ring
  refine ⟨4, by norm_num, fun x hx => ?_⟩
  have hpos : ∀ t ∈ Set.Icc 1 x, 0 < t := by intro t ht; linarith [ht.1]
  have hi : IntegrableOn (deriv log) (Set.Icc 1 x) := by
    simp only [deriv_log']
    exact (continuousOn_inv₀.mono fun t ht => (hpos t ht).ne').integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul₀ c (by simp [c]) x
    (fun t ht => differentiableAt_log (hpos t ht).ne') hi
  rw [hw, hc] at hab
  simp_rw [deriv_log, hc] at hab
  have hA : IntervalIntegrable (fun t : ℝ => t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) volume 1 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    have h := integrableOn_mul_sum_Icc (m := 0) c (by norm_num : (0:ℝ) ≤ 1) hi
    simp only [deriv_log'] at h
    simpa only [hc] using h
  have hL : IntervalIntegrable (fun t : ℝ => log t / t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact (continuousOn_log.mono fun t ht => (hpos t ht).ne').div continuousOn_id
      (fun t ht => (hpos t ht).ne')
  have hB : IntervalIntegrable (fun t : ℝ => 2 / t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')
  have herr : |∫ t in 1..x, (t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p - log t / t)| ≤ 2 * log x := by
    calc |∫ t in 1..x, (t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p - log t / t)|
        = ‖∫ t in 1..x, (t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p - log t / t)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t in 1..x, 2 / t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hx _ hB
        filter_upwards [] with t ht
        have ht1 : 1 ≤ t := ht.1.le
        have hm := LeanLab.AlmostPrimes.Decomp1528a.mertens1_abs ht1
        rw [Real.norm_eq_abs, show t⁻¹ * (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) - log t / t =
          (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p - log t) / t by ring, abs_div, abs_of_pos (by linarith : 0<t)]
        exact div_le_div_of_nonneg_right hm (by linarith)
      _ = 2 * log x := by
        rw [show (fun t : ℝ => 2/t) = (fun t => 2*t⁻¹) by funext t; ring,
          intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num : (0:ℝ) < 1) (by linarith)]
        simp
  have hint : (∫ t in 1..x, (t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p - log t / t)) =
      (∫ t in 1..x, t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) - (log x)^2/2 := by
    rw [integral_sub hA hL, integral_log_div (by norm_num) hx]
    simp
  have hm := LeanLab.AlmostPrimes.Decomp1528a.mertens1_abs hx
  have hl : 0 ≤ log x := log_nonneg hx
  have hmul : |log x * (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x)| ≤ 2 * log x := by
    rw [abs_mul, abs_of_nonneg hl]
    nlinarith
  rw [hint] at herr
  rw [hab]
  have hkey : log x * (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p) -
      (∫ t in Set.Ioc 1 x, t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) - (log x)^2/2 =
      log x * (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x) -
      ((∫ t in 1..x, t⁻¹ * ∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) - (log x)^2/2) := by
    rw [integral_of_le hx]
    ring
  rw [hkey]
  exact (abs_sub _ _).trans (by linarith)

/-- Block sums over primes: Σ_{m < p ≤ n} = Σ_{p ≤ n} - Σ_{p ≤ m}. -/
lemma sum_block_eq (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ p ∈ (Ioc m n).filter Nat.Prime, f p =
      ∑ p ∈ Nat.primesLE n, f p - ∑ p ∈ Nat.primesLE m, f p := by
  have hsub : Nat.primesLE m ⊆ Nat.primesLE n := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [eq_sub_iff_add_eq, ← sum_union]
  · congr 1
    ext p
    simp only [Nat.primesLE, Nat.primesBelow, mem_union, mem_filter, mem_Ioc, mem_range]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h3⟩) <;> exact ⟨by omega, h3⟩
    · rintro ⟨h1, h3⟩
      by_cases h : m < p
      · exact Or.inl ⟨⟨h, by omega⟩, h3⟩
      · exact Or.inr ⟨by omega, h3⟩
  · rw [disjoint_left]
    intro p hp hp'
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_Ioc, mem_range] at hp hp'
    omega

/-- The prime sum on p. 64: for z ≥ 2 and 1 ≤ a ≤ 3,
Σ_{z < p ≤ z^a} (a log z - log p)²/p = log² z (a² log a - 3a²/2 + 2a - 1/2) + O(log z),
the main term being log² z ∫_1^a (a - w)²/w dw. Assembly, CONDITIONAL ON
`Decomp1528b.mertens2_block`. The other two prime sum inputs are proved. -/
theorem prime_square_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z a : ℝ, 2 ≤ z → 1 ≤ a → a ≤ 3 →
      |∑ p ∈ (Ioc ⌊z⌋₊ ⌊z ^ a⌋₊).filter Nat.Prime, (a * log z - log p) ^ 2 / p -
        (log z) ^ 2 * (a ^ 2 * log a - 3 * a ^ 2 / 2 + 2 * a - 1 / 2)| ≤ C * log z := by
  obtain ⟨C3, hC3, h3⟩ := sum_logsq_div_primes
  refine ⟨70 + 12 * C3, by positivity, fun z a hz ha1 ha3 => ?_⟩
  have hz0 : 0 < z := by linarith
  set L := log z with hL
  have hL0 : 0 < L := log_pos (by linarith)
  have hL2 : log 2 ≤ L := log_le_log (by norm_num) hz
  have hlog2 : (0.69 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hw : z ≤ z ^ a := by
    calc z = z ^ (1 : ℝ) := (rpow_one z).symm
      _ ≤ z ^ a := rpow_le_rpow_of_exponent_le (by linarith) ha1
  have hwz : log (z ^ a) = a * L := log_rpow hz0 a
  have hw1 : 1 ≤ z ^ a := by linarith
  have hfl : ⌊z⌋₊ ≤ ⌊z ^ a⌋₊ := Nat.floor_le_floor hw
  set B := (Ioc ⌊z⌋₊ ⌊z ^ a⌋₊).filter Nat.Prime with hB
  have hexp : ∑ p ∈ B, (a * L - log p) ^ 2 / p =
      (a * L) ^ 2 * ∑ p ∈ B, (1 : ℝ) / p - 2 * (a * L) * ∑ p ∈ B, log p / p +
        ∑ p ∈ B, (log p) ^ 2 / p := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => by ring
  rw [hexp]
  -- the three block sums
  have hm2 := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hz hw
  rw [hwz, log_mul (by linarith) hL0.ne', ← hL] at hm2
  have hm2' : |∑ p ∈ B, (1 : ℝ) / p - log a| ≤ 4 / L := by
    convert hm2 using 3; ring
  have hm1w := LeanLab.AlmostPrimes.Decomp1528a.mertens1_abs hw1
  have hm1z := LeanLab.AlmostPrimes.Decomp1528a.mertens1_abs (show (1 : ℝ) ≤ z by linarith)
  rw [hwz] at hm1w
  rw [← hL] at hm1z
  have hb1 : ∑ p ∈ B, log p / p = ∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, log p / p -
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, log p / p := sum_block_eq (fun p => log p / p) hfl
  have hq1 : |∑ p ∈ B, log p / p - (a - 1) * L| ≤ 4 := by
    rw [hb1]
    have := abs_sub (∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, log p / p - a * L)
      (∑ p ∈ Nat.primesLE ⌊z⌋₊, log p / p - L)
    calc _ = |(∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, log p / p - a * L) -
          (∑ p ∈ Nat.primesLE ⌊z⌋₊, log p / p - L)| := by ring_nf
      _ ≤ 4 := by linarith
  have h3w := h3 (z ^ a) hw1
  have h3z := h3 z (by linarith)
  rw [hwz] at h3w
  rw [← hL] at h3z
  have hb2 : ∑ p ∈ B, (log p) ^ 2 / p = ∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, (log p) ^ 2 / p -
      ∑ p ∈ Nat.primesLE ⌊z⌋₊, (log p) ^ 2 / p := sum_block_eq (fun p => (log p) ^ 2 / p) hfl
  have hq2 : |∑ p ∈ B, (log p) ^ 2 / p - (a ^ 2 - 1) * L ^ 2 / 2| ≤ C3 * (2 + 4 * L) := by
    rw [hb2]
    have := abs_sub (∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, (log p) ^ 2 / p - (a * L) ^ 2 / 2)
      (∑ p ∈ Nat.primesLE ⌊z⌋₊, (log p) ^ 2 / p - L ^ 2 / 2)
    have hC : C3 * (1 + a * L) + C3 * (1 + L) ≤ C3 * (2 + 4 * L) := by
      have := mul_le_mul_of_nonneg_left ha3 (mul_nonneg hC3 hL0.le)
      nlinarith
    calc _ = |(∑ p ∈ Nat.primesLE ⌊z ^ a⌋₊, (log p) ^ 2 / p - (a * L) ^ 2 / 2) -
          (∑ p ∈ Nat.primesLE ⌊z⌋₊, (log p) ^ 2 / p - L ^ 2 / 2)| := by ring_nf
      _ ≤ _ := by linarith
  set s1 := ∑ p ∈ B, (1 : ℝ) / p
  set s2 := ∑ p ∈ B, log p / p
  set s3 := ∑ p ∈ B, (log p) ^ 2 / p
  have hkey : (a * L) ^ 2 * s1 - 2 * (a * L) * s2 + s3 -
      L ^ 2 * (a ^ 2 * log a - 3 * a ^ 2 / 2 + 2 * a - 1 / 2) =
      (a * L) ^ 2 * (s1 - log a) - 2 * (a * L) * (s2 - (a - 1) * L) +
        (s3 - (a ^ 2 - 1) * L ^ 2 / 2) := by ring
  rw [hkey]
  have e1 : |(a * L) ^ 2 * (s1 - log a)| ≤ 36 * L := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (a * L) ^ 2 * |s1 - log a| ≤ (a * L) ^ 2 * (4 / L) :=
          mul_le_mul_of_nonneg_left hm2' (sq_nonneg _)
      _ = 4 * a ^ 2 * L := by field_simp
      _ ≤ 36 * L := by
          have ha9 : a ^ 2 ≤ 9 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right ha9 hL0.le]
  have e2 : |2 * (a * L) * (s2 - (a - 1) * L)| ≤ 24 * L := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * (a * L) * |s2 - (a - 1) * L| ≤ 2 * (a * L) * 4 :=
          mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ ≤ 24 * L := by nlinarith
  have e3 : C3 * (2 + 4 * L) ≤ 12 * C3 * L := by
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 8 * L by linarith) hC3
    linarith
  have t1 := abs_add_le ((a * L) ^ 2 * (s1 - log a) - 2 * (a * L) * (s2 - (a - 1) * L))
    (s3 - (a ^ 2 - 1) * L ^ 2 / 2)
  have t2 := abs_sub ((a * L) ^ 2 * (s1 - log a)) (2 * (a * L) * (s2 - (a - 1) * L))
  have hC3L : 0 ≤ C3 * L := mul_nonneg hC3 hL0.le
  linarith only [t1, t2, e1, e2, e3, hq2, hC3L, hL0]

/-! ### W_q, p. 64 -/

/-- The primes z < p ≤ w with p ∤ N, z = N^{1/6}, which can divide an m ≤ w counted in
Σ_{m ≤ w} μ²(m)/f₁(m) but not in W_q. -/
def bigPrimes (N : ℕ) (w : ℝ) : Finset ℕ :=
  (Ioc 0 ⌊w⌋₊).filter (fun p => p.Prime ∧ N < p ^ 6 ∧ ¬ p ∣ N)

/-- Derived finite sum helper for the union bound on p. 64. -/
lemma Wq_eq_sum_hK (N : ℕ) {w : ℝ} (hw : 1 ≤ w) :
    Wq N w = ∑ m ∈ Ioc 0 ⌊w⌋₊, if m ∣ Pz N then hK N m else 0 := by
  have hPN : (Pz N).Coprime N := by
    apply Nat.Coprime.prod_left
    intro p hp
    have hp' := mem_siftPrimes.mp hp
    exact hp'.2.1.coprime_iff_not_dvd.mpr hp'.2.2.2.2
  have heq : (Pz N).divisors.filter (fun l : ℕ => (l : ℝ) ≤ w) =
      (Ioc 0 ⌊w⌋₊).filter (fun m => m ∣ Pz N) := by
    ext m
    simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨hm, _⟩, hmw⟩
      refine ⟨⟨?_, (Nat.le_floor_iff (by linarith)).mpr hmw⟩, hm⟩
      exact Nat.pos_of_dvd_of_pos hm (Nat.pos_of_ne_zero (Pz_ne_zero N))
    · rintro ⟨⟨_, hmw⟩, hm⟩
      exact ⟨⟨hm, Pz_ne_zero N⟩, (Nat.le_floor_iff (by linarith)).mp hmw⟩
  rw [Wq]
  trans ∑ l ∈ (Pz N).divisors.filter (fun l : ℕ => (l : ℝ) ≤ w), hK N l
  · apply sum_congr rfl
    intro l hl
    have hlP := Nat.dvd_of_mem_divisors (mem_filter.mp hl).1
    have hl0 := (Nat.pos_of_mem_divisors (mem_filter.mp hl).1).ne'
    have hls := (Pz_squarefree N).squarefree_of_dvd hlP
    have hlc := hPN.of_dvd_left hlP
    change _ = if l ≠ 0 ∧ Squarefree l ∧ l.Coprime N then _ else _
    rw [ite_eq_left ⟨hl0, hls, hlc⟩]
  · rw [heq, sum_filter]

/-- Derived finite sum helper for the union bound on p. 64. -/
lemma sum_hK_multiples {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (w : ℝ) :
    ∑ m ∈ (Ioc 0 ⌊w⌋₊).filter (p ∣ ·), hK N m =
      2 / ((p : ℝ) - 2) * G (p*N) (w/p) := by
  symm
  rw [G, Nat.floor_div_natCast, mul_sum]
  apply sum_bij (fun d _ => p*d)
  · intro d hd
    rw [mem_filter, mem_Ioc] at *
    refine ⟨⟨Nat.mul_pos hp.pos hd.1, ?_⟩, dvd_mul_right p d⟩
    have := (Nat.le_div_iff_mul_le hp.pos).mp hd.2
    simpa [Nat.mul_comm] using this
  · intro d hd e he hde
    exact Nat.eq_of_mul_eq_mul_left hp.pos hde
  · intro m hm
    obtain ⟨⟨hm0, hmw⟩, hpm⟩ := (by simpa only [mem_filter, mem_Ioc] using hm)
    refine ⟨m/p, ?_, Nat.mul_div_cancel' hpm⟩
    rw [mem_Ioc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
    · exact Nat.div_le_div_right hmw
  · intro d hd
    exact (hK_mul_prime hp hpN d).symm

/-- Derived finite sum helper for the union bound on p. 64. -/
lemma exists_big_prime {N m : ℕ} {w : ℝ} (hN : Even N)
    (hm : m ∈ Ioc 0 ⌊w⌋₊) (hs : Squarefree m) (hc : m.Coprime N)
    (hn : ¬ m ∣ Pz N) :
    ∃ p ∈ (Ioc 0 ⌊w⌋₊).filter (fun p => p.Prime ∧ N < p^6 ∧ ¬p∣N), p ∣ m := by
  have hm0 : m ≠ 0 := (mem_Ioc.mp hm).1.ne'
  have hex : ∃ p ∈ m.primeFactors, p ∉ siftPrimes N := by
    by_contra! h
    apply hn
    rw [← Nat.prod_primeFactors_of_squarefree hs, Pz]
    exact prod_dvd_prod_of_subset _ _ _ (by intro p hp; exact h p hp)
  obtain ⟨p, hpm, hpn⟩ := hex
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpm
  have hpN : ¬ p ∣ N := fun hpN => hpp.not_dvd_one (by
    have := Nat.dvd_gcd hpd hpN
    rwa [hc.gcd_eq_one] at this)
  have hp2 : 2 < p := by
    have : p ≠ 2 := fun h => hpN (h ▸ even_iff_two_dvd.mp hN)
    have := hpp.two_le
    omega
  have hpPow : N < p^6 := by
    by_contra! h
    apply hpn
    rw [mem_siftPrimes]
    refine ⟨?_, hpp, hp2, h, hpN⟩
    exact (Nat.le_self_pow (by norm_num : 6 ≠ 0) p).trans h
  refine ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, (Nat.le_of_dvd (mem_Ioc.mp hm).1 hpd).trans (mem_Ioc.mp hm).2⟩,
    hpp, hpPow, hpN⟩, hpd⟩

/-- LEAF. Unit U-1544. The inequality opening the case a > 1 on p. 64:
W_q ≥ Σ_{m ≤ w} μ²(m)/f₁(m) - Σ_{z<p≤w} (1/f₁(p)) Σ_{m' ≤ w/p, (m', p) = 1} μ²(m')/f₁(m'),
with 1/f₁(p) = 2/(p - 2) and (m', p) = 1, (m', N) = 1 written as (m', pN) = 1. True for even
N because an m ≤ w prime to N with g(m) > z has a prime p > z, p ≤ w, and every term is ≥ 0. -/
theorem Wq_ge_union {N : ℕ} {w : ℝ} (hN : Even N) (hw : 1 ≤ w) :
    G N w - ∑ p ∈ bigPrimes N w, 2 / ((p : ℝ) - 2) * G (p * N) (w / p) ≤ Wq N w := by
  let B := (Ioc 0 ⌊w⌋₊).filter (fun p => p.Prime ∧ N < p^6 ∧ ¬p∣N)
  have hsum : (∑ p ∈ B, 2 / ((p : ℝ)-2) * G (p*N) (w/p)) =
      ∑ m ∈ Ioc 0 ⌊w⌋₊, ∑ p ∈ B, if p ∣ m then hK N m else 0 := by
    calc _ = ∑ p ∈ B, ∑ m ∈ (Ioc 0 ⌊w⌋₊).filter (p ∣ ·), hK N m := by
          apply sum_congr rfl
          intro p hp
          have hp' := (mem_filter.mp hp).2
          exact (sum_hK_multiples hp'.1 hp'.2.2 w).symm
      _ = _ := by simp_rw [sum_filter]; rw [sum_comm]
  change G N w - ∑ p ∈ B, 2 / ((p : ℝ)-2) * G (p*N) (w/p) ≤ Wq N w
  rw [sub_le_iff_le_add, Wq_eq_sum_hK N hw, hsum, G, ← sum_add_distrib]
  apply sum_le_sum
  intro m hm
  by_cases hmP : m ∣ Pz N
  · rw [ite_eq_left hmP]
    exact le_add_of_nonneg_right (sum_nonneg fun p hp => by split_ifs <;> first | exact hK_nonneg N m | exact le_rfl)
  · rw [ite_eq_right hmP, zero_add]
    by_cases hsupport : m ≠ 0 ∧ Squarefree m ∧ m.Coprime N
    · obtain ⟨p, hp, hpm⟩ := exists_big_prime hN hm hsupport.2.1 hsupport.2.2 hmP
      have hle := single_le_sum (f := fun p => if p ∣ m then hK N m else 0)
        (fun p hp => by split_ifs <;> first | exact hK_nonneg N m | exact le_rfl) hp
      simpa only [ite_eq_left hpm] using hle
    · have hz : hK N m = 0 := by simp [hK, hsupport]
      rw [hz]
      apply sum_nonneg
      intro p hp
      simp only [ite_self, le_refl]

/-- Derived finite weight comparison on p. 64. -/
lemma Wq_le_G (N : ℕ) {w : ℝ} (hw : 1 ≤ w) : Wq N w ≤ G N w := by
  rw [Wq_eq_sum_hK N hw, G]
  apply sum_le_sum
  intro m hm
  split_ifs
  · exact le_rfl
  · exact hK_nonneg N m

/-- Derived finite weight comparison on p. 64. -/
lemma G_eq_Wq_of_pow_le {N : ℕ} {w : ℝ} (hN : Even N) (hw : 1 ≤ w)
    (hw6 : w^6 ≤ (N:ℝ)) : G N w = Wq N w := by
  have hB : (Ioc 0 ⌊w⌋₊).filter (fun p => p.Prime ∧ N < p^6 ∧ ¬p∣N) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨⟨hp0, hpw⟩, _, hp6, _⟩ := (by simpa only [mem_filter, mem_Ioc] using hp)
    have hpwR : (p:ℝ) ≤ w := (by exact_mod_cast hpw : (p:ℝ) ≤ ⌊w⌋₊).trans
      (Nat.floor_le (by linarith))
    have hpow : (p:ℝ)^6 ≤ N := (pow_le_pow_left₀ (by positivity) hpwR 6).trans hw6
    have : p^6 ≤ N := by exact_mod_cast hpow
    omega
  have h := Wq_ge_union hN hw
  simp only [bigPrimes] at h
  rw [hB, sum_empty, sub_zero] at h
  exact le_antisymm h (Wq_le_G N hw)

/-- LEAF. Unit U-1544. Q(pN) = (p - 2)/p · Q(N) for an odd prime p ∤ N, N ≥ 1; hence
2/(p - 2) C_{pN} = 2/p C_N, the identity used on p. 64. -/
theorem Q_mul_prime {N p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpN : ¬ p ∣ N) (hN : N ≠ 0) :
    Q (p * N) = ((p : ℝ) - 2) / p * Q N := by
  unfold Q
  rw [Nat.primeFactors_mul hp.ne_zero hN, hp.primeFactors, singleton_union,
    filter_insert, ite_eq_left hp2, prod_insert]
  simp only [mem_filter, Nat.mem_primeFactors]
  exact fun h => hpN h.1.2.1

/-- LEAF. Unit U-1544. T = ∏_{p > 2} (p - 1)²/(p(p - 2)) ≥ 1: every factor is ≥ 1 and the
product converges, p. 61. -/
theorem one_le_Ttwin : 1 ≤ Ttwin := by
  unfold Ttwin
  let f : Nat.Primes → ℝ := fun p => if (p : ℕ) = 2 then 1 else
    ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))
  change 1 ≤ ∏' p, f p
  have hf : ∀ p, 1 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs with hp
    · exact le_rfl
    · have hp2 : 2 < (p : ℕ) := lt_of_le_of_ne p.property.two_le (Ne.symm hp)
      have hpR : (2 : ℝ) < (p : ℕ) := by exact_mod_cast hp2
      rw [le_div_iff₀ (by positivity)]
      nlinarith
  exact ge_of_tendsto Ttwin_multipliable.hasProd (Filter.Eventually.of_forall fun s =>
    Finset.one_le_prod₀ fun p _ => hf p)


lemma CK_nonneg (N : ℕ) : 0 ≤ CK N := by
  have h1 := one_le_Ttwin
  have h2 := (Q_bounds N).1
  simp only [CK, Cpaper]
  exact div_nonneg (mul_nonneg (by linarith) h2.le) (by norm_num)

lemma CK_le (N : ℕ) : CK N ≤ Ttwin / 8 := by
  have := one_le_Ttwin
  have := (Q_bounds N).2
  simp only [CK, Cpaper]
  have : Ttwin * Q N ≤ Ttwin := by nlinarith
  linarith

lemma rpow_sixth (N : ℕ) : ((N : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = N := by
  rw [← rpow_natCast, ← rpow_mul (Nat.cast_nonneg N)]; norm_num

lemma bigPrimes_subset {N : ℕ} {w : ℝ} :
    bigPrimes N w ⊆ (Ioc ⌊(N : ℝ) ^ (1 / 6 : ℝ)⌋₊ ⌊w⌋₊).filter Nat.Prime := by
  intro p hp
  simp only [bigPrimes, mem_filter, mem_Ioc] at hp ⊢
  refine ⟨⟨?_, hp.1.2⟩, hp.2.1⟩
  by_contra h
  push_neg at h
  have hpz : (p : ℝ) ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    (Nat.le_floor_iff (by positivity)).1 h
  have h6 : (p : ℝ) ^ 6 ≤ N := by
    rw [← rpow_sixth N]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hpz 6
  have : p ^ 6 ≤ N := by exact_mod_cast h6
  omega

set_option maxHeartbeats 1600000 in
/-- **W_q lower bound**, p. 64, for 1 ≤ a ≤ 3 and w = z^a = N^{a/6}:
W_q ≥ ((2a - 1)² - 2a² log a)/36 · C_N log² N - C (1 + log N) √(log N) for even N ≥ 64.
Assembly, CONDITIONAL ON `rhoK_moment` and `Decomp1528b.mertens2_block`. -/
theorem Wq_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Even N → 64 ≤ N → ∀ a : ℝ, 1 ≤ a → a ≤ 3 →
      TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2 - C * (1 + log N) * √(log N) ≤
        Wq N ((N : ℝ) ^ (a / 6)) := by
  obtain ⟨C3, hC3, hL3⟩ := lemma3
  obtain ⟨Cs, hCs, hps⟩ := prime_square_sum
  have hT0 : 0 ≤ Ttwin := le_trans zero_le_one one_le_Ttwin
  refine ⟨97 * C3 + Ttwin * Cs / 4 + 1,
    by have := div_nonneg (mul_nonneg hT0 hCs) (show (0 : ℝ) ≤ 4 by norm_num); linarith,
    fun N hN hN64 a ha1 ha3 => ?_⟩
  have hNR : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  set z := (N : ℝ) ^ (1 / 6 : ℝ) with hz
  set w := (N : ℝ) ^ (a / 6) with hw
  set LN := log (N : ℝ) with hLN
  have hLN1 : 1 ≤ LN := by
    rw [hLN, ← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hsq1 : 1 ≤ √LN := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hLN1
  have hlz : log z = LN / 6 := by rw [hz, log_rpow hN0]; ring
  have hlw : log w = a * (LN / 6) := by rw [hw, log_rpow hN0]; ring
  have hzw : z ^ a = w := by rw [hz, hw, ← rpow_mul hN0.le]; ring_nf
  have hz2 : 2 ≤ z := by
    have h64 : (64 : ℝ) ^ (1 / 6 : ℝ) = 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num, ← rpow_mul (by norm_num)]; norm_num
    rw [← h64]; exact rpow_le_rpow (by norm_num) hNR (by norm_num)
  have hzw' : z ≤ w := by
    rw [← hzw]
    calc z = z ^ (1 : ℝ) := (rpow_one z).symm
      _ ≤ z ^ a := rpow_le_rpow_of_exponent_le (by linarith) ha1
  have hw1 : 1 ≤ w := by linarith
  have hwN : w ≤ N := by
    calc w ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = N := rpow_one _
  have hlw0 : 0 ≤ log w := log_nonneg hw1
  have hlwN : log w ≤ LN := log_le_log (by linarith) hwN
  have hN2 : 2 ≤ N := by omega
  have hNne : N ≠ 0 := by omega
  -- the main sum
  have hG := hL3 N hN hN2 w hw1
  have hGlow : CK N * (log w) ^ 2 - C3 * (1 + LN) * √LN ≤ G N w := by
    have := (abs_le.mp hG).1
    have h2 : C3 * (1 + log w) * √LN ≤ C3 * (1 + LN) * √LN := by
      have := sqrt_nonneg LN; gcongr
    linarith
  -- the subtracted sum, termwise
  set B := bigPrimes N w with hB
  have hterm : ∀ p ∈ B, 2 / ((p : ℝ) - 2) * G (p * N) (w / p) ≤
      2 * CK N * ((log w - log p) ^ 2 / p) + 12 * C3 * (1 + LN) * √LN * (1 / p) := by
    intro p hp
    simp only [hB, bigPrimes, mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hp0, hpw⟩, hpp, _, hpN⟩ := hp
    have hp2 : 2 < p := by
      rcases hpp.eq_two_or_odd' with h | h
      · exact absurd (h ▸ even_iff_two_dvd.mp hN) hpN
      · have := hpp.two_le
        rcases Nat.lt_or_ge 2 p with h' | h'
        · exact h'
        · have : p = 2 := by omega
          subst this; exact absurd h (by decide)
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp2
    have hpwR : (p : ℝ) ≤ w := le_trans (by exact_mod_cast hpw) (Nat.floor_le (by linarith))
    have hx : 1 ≤ w / p := by rw [le_div_iff₀ (by linarith)]; linarith
    have hpNe : Even (p * N) := hN.mul_left p
    have hpN2 : 2 ≤ p * N := by nlinarith
    have hGp := (abs_le.mp (hL3 (p * N) hpNe hpN2 (w / p) hx)).2
    have hCKp : CK (p * N) = ((p : ℝ) - 2) / p * CK N := by
      simp only [CK, Cpaper]; rw [Q_mul_prime hpp hp2 hpN hNne]; ring
    have hlogwp : log (w / p) = log w - log p := log_div (by linarith) (by linarith)
    have hlwp0 : 0 ≤ log (w / p) := log_nonneg hx
    have hlwpN : log (w / p) ≤ LN := by rw [hlogwp]; have := log_nonneg (show (1:ℝ) ≤ p by linarith); linarith
    have hlpN : log ((p * N : ℕ) : ℝ) ≤ 2 * LN := by
      push_cast
      rw [log_mul (by linarith) hN0.ne']
      have : log (p : ℝ) ≤ LN := log_le_log (by linarith) (by linarith)
      linarith
    have hsqp : √(log ((p * N : ℕ) : ℝ)) ≤ 2 * √LN := by
      calc √(log ((p * N : ℕ) : ℝ)) ≤ √(2 * LN) := sqrt_le_sqrt hlpN
        _ = √2 * √LN := by rw [sqrt_mul (by norm_num)]
        _ ≤ 2 * √LN := by
            have : √2 ≤ 2 := by
              rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
              exact sqrt_le_sqrt (by norm_num)
            have := sqrt_nonneg LN; nlinarith
    have hGp' : G (p * N) (w / p) ≤ CK (p * N) * (log w - log p) ^ 2 +
        C3 * (1 + LN) * (2 * √LN) := by
      rw [← hlogwp]
      have : C3 * (1 + log (w / p)) * √(log ((p * N : ℕ) : ℝ)) ≤ C3 * (1 + LN) * (2 * √LN) := by
        have := sqrt_nonneg (log ((p * N : ℕ) : ℝ))
        gcongr
      linarith
    have hfac : 0 < 2 / ((p : ℝ) - 2) := by apply div_pos <;> linarith
    have hfac6 : 2 / ((p : ℝ) - 2) ≤ 6 * (1 / p) := by
      rw [div_le_iff₀ (by linarith)]; field_simp; nlinarith
    calc 2 / ((p : ℝ) - 2) * G (p * N) (w / p)
        ≤ 2 / ((p : ℝ) - 2) * (CK (p * N) * (log w - log p) ^ 2 + C3 * (1 + LN) * (2 * √LN)) :=
          mul_le_mul_of_nonneg_left hGp' hfac.le
      _ = 2 * CK N * ((log w - log p) ^ 2 / p) +
          2 / ((p : ℝ) - 2) * (C3 * (1 + LN) * (2 * √LN)) := by
          have hne : (p : ℝ) - 2 ≠ 0 := by linarith
          have hpne : (p : ℝ) ≠ 0 := by linarith
          rw [hCKp]; field_simp
      _ ≤ 2 * CK N * ((log w - log p) ^ 2 / p) + 6 * (1 / p) * (C3 * (1 + LN) * (2 * √LN)) := by
          have : 0 ≤ C3 * (1 + LN) * (2 * √LN) :=
            mul_nonneg (mul_nonneg hC3.le (by linarith only [hLN1])) (by linarith only [sqrt_nonneg LN])
          linarith [mul_le_mul_of_nonneg_right hfac6 this]
      _ = _ := by ring
  have hsumB : ∑ p ∈ B, 2 / ((p : ℝ) - 2) * G (p * N) (w / p) ≤
      2 * CK N * ∑ p ∈ (Ioc ⌊z⌋₊ ⌊w⌋₊).filter Nat.Prime, (log w - log p) ^ 2 / p +
        12 * C3 * (1 + LN) * √LN * ∑ p ∈ (Ioc ⌊z⌋₊ ⌊w⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hs := @bigPrimes_subset N w
    have hCK := CK_nonneg N
    have hcoef : 0 ≤ 12 * C3 * (1 + LN) * √LN :=
      mul_nonneg (mul_nonneg (by linarith only [hC3]) (by linarith only [hLN1])) (sqrt_nonneg LN)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hs
        (fun p _ _ => by positivity)) (by linarith only [hCK])
    · exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hs
        (fun p _ _ => by positivity)) hcoef
  -- the block sums
  have hPS := hps z a hz2 ha1 ha3
  rw [hzw, hlz, ← hlw] at hPS
  have hPSu := (abs_le.mp hPS).2
  have hM2 := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hz2 hzw'
  have hinv : ∑ p ∈ (Ioc ⌊z⌋₊ ⌊w⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤ 8 := by
    have hu := (abs_le.mp hM2).2
    rw [hlw, hlz] at hu
    have hLz : 0 < LN / 6 := by linarith
    rw [log_mul (by linarith) hLz.ne'] at hu
    have hla : log a ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by linarith); linarith
    have h4 : 4 / (LN / 6) ≤ 4 * 6 / 4 := by
      rw [div_le_iff₀ hLz]
      have hl64 : (4 : ℝ) ≤ LN := by
        have h64 : log (64 : ℝ) = 6 * log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_gt_d9
        have := log_le_log (by norm_num) hNR
        linarith
      linarith
    linarith only [hu, hla, h4]
  have hCKle := CK_le N
  have hCK0 := CK_nonneg N
  have hq : TogashiUchiyama.q a = a ^ 2 - 2 * (a ^ 2 * log a - 3 * a ^ 2 / 2 + 2 * a - 1 / 2) := by
    unfold TogashiUchiyama.q; ring
  have hsq0 := sqrt_nonneg LN
  -- assemble
  have hW := Wq_ge_union hN hw1
  rw [hq]
  have hmain : CK N * (log w) ^ 2 = CK N * (a ^ 2 * (LN / 6) ^ 2) := by rw [hlw]; ring
  have hbig : 2 * CK N * ∑ p ∈ (Ioc ⌊z⌋₊ ⌊w⌋₊).filter Nat.Prime, (log w - log p) ^ 2 / p ≤
      2 * CK N * ((LN / 6) ^ 2 * (a ^ 2 * log a - 3 * a ^ 2 / 2 + 2 * a - 1 / 2) +
        Cs * (LN / 6)) := mul_le_mul_of_nonneg_left (by linarith only [hPSu])
          (by linarith only [hCK0])
  have hsmall : 12 * C3 * (1 + LN) * √LN *
      ∑ p ∈ (Ioc ⌊z⌋₊ ⌊w⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤ 12 * C3 * (1 + LN) * √LN * 8 :=
    mul_le_mul_of_nonneg_left hinv
      (mul_nonneg (mul_nonneg (by linarith only [hC3]) (by linarith only [hLN1])) hsq0)
  have hCsterm : 2 * CK N * (Cs * (LN / 6)) ≤ Ttwin * Cs / 4 * (1 + LN) * √LN := by
    have h1 : 2 * CK N * (Cs * (LN / 6)) ≤ 2 * (Ttwin / 8) * (Cs * (LN / 6)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hCKle])
        (mul_nonneg hCs (by linarith only [hLN1]))
    have h2 : LN / 6 ≤ (1 + LN) * √LN := by
      have := mul_le_mul_of_nonneg_left hsq1 (show 0 ≤ 1 + LN by linarith only [hLN1])
      linarith only [this, hLN1]
    have hT0 : 0 ≤ Ttwin := le_trans zero_le_one one_le_Ttwin
    have h3 := mul_le_mul_of_nonneg_left h2
      (show 0 ≤ Ttwin * Cs / 4 from div_nonneg (mul_nonneg hT0 hCs) (by norm_num))
    calc 2 * CK N * (Cs * (LN / 6)) ≤ 2 * (Ttwin / 8) * (Cs * (LN / 6)) := h1
      _ = Ttwin * Cs / 4 * (LN / 6) := by ring
      _ ≤ Ttwin * Cs / 4 * ((1 + LN) * √LN) := h3
      _ = _ := by ring
  have hfinal : C3 * (1 + LN) * √LN + 12 * C3 * (1 + LN) * √LN * 8 +
      Ttwin * Cs / 4 * (1 + LN) * √LN ≤ (97 * C3 + Ttwin * Cs / 4 + 1) * (1 + LN) * √LN := by
    have : 0 ≤ (1 + LN) * √LN := mul_nonneg (by linarith only [hLN1]) hsq0
    linarith only [this]
  have hLN6 : (LN / 6) ^ 2 = LN ^ 2 / 36 := by ring
  rw [hmain] at hGlow
  linarith only [hW, hGlow, hsumB, hbig, hsmall, hCsterm, hfinal, hLN6]

/-! ### Vacuity instances -/

/-- The hypotheses of `lemma3` and `Wq_lower` can hold: K = N = 64 is even and ≥ 64, and
a = 2 lies in [1, 3]; x = 1 ≥ 1. -/
theorem vacuity_b1 : Even 64 ∧ 2 ≤ 64 ∧ 64 ≤ 64 ∧ (1 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 3 ∧ (1 : ℝ) ≤ 1 := by
  refine ⟨by decide, by norm_num, le_rfl, by norm_num, by norm_num, le_rfl⟩

/-- The hypotheses of `Q_mul_prime` can hold: p = 3, N = 4. -/
theorem vacuity_b2 : Nat.Prime 3 ∧ 2 < 3 ∧ ¬ 3 ∣ 4 ∧ (4 : ℕ) ≠ 0 :=
  ⟨Nat.prime_three, by norm_num, by decide, by norm_num⟩

/-- The hypotheses of `prime_square_sum` can hold: z = 2, a = 1. -/
theorem vacuity_b3 : (2 : ℝ) ≤ 2 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 3 := ⟨le_rfl, le_rfl, by norm_num⟩

/-! Concrete instances checked with CODEX task187. AI wrote the Lean code. -/
example : rhoK 2 1 = 1 := (rhoK_multiplicative 2).map_one
example : rhoK 2 3 = 4/3 := by
  rw [rhoK_prime 2 Nat.prime_three, hK_prime 2 Nat.prime_three]
  norm_num
example : rhoK 2 (3^2) = -11/9 := by
  rw [rhoK_prime_sq 2 Nat.prime_three, hK_prime 2 Nat.prime_three]
  norm_num
example : rhoK 2 (3^3) = 2/9 := by
  rw [rhoK_prime_cube 2 Nat.prime_three, hK_prime 2 Nat.prime_three]
  norm_num
example : rhoK 2 (3^4) = 0 := rhoK_prime_pow_zero 2 Nat.prime_three (by norm_num)
example : rhoK 2 (3*5) = rhoK 2 3 * rhoK 2 5 :=
  (rhoK_multiplicative 2).map_mul_of_coprime (by decide)
example : Q (3*4) = ((3:ℝ)-2)/3 * Q 4 :=
  Q_mul_prime Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
example : G 64 2 = Wq 64 2 := G_eq_Wq_of_pow_le (by decide) (by norm_num) (by norm_num)
example : G 4 3 - ∑ p ∈ bigPrimes 4 3, 2/((p:ℝ)-2) * G (p*4) (3/p) ≤ Wq 4 3 :=
  Wq_ge_union (by decide) (by norm_num)
example : HasSum (fun d => rhoK 2 d) (Ttwin/4) := by
  have hset : (2:ℕ).primeFactors.filter (2 < ·) = ∅ := by
    rw [Nat.prime_two.primeFactors]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have he : p = 2 := mem_singleton.mp (mem_filter.mp hp).1
    have ht := (mem_filter.mp hp).2
    omega
  have hQ : Q 2 = 1 := by unfold Q; rw [hset]; simp
  simpa only [hQ, mul_one] using rhoK_hasSum (K := 2) (by decide) (by norm_num)
example : Summable (fun n : ℕ => |rhoK 2 n| * (n:ℝ)^(1/4:ℝ)) :=
  rhoK_weighted_summable (by norm_num)
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    ∑ d ∈ Ioc 0 n, |rhoK 2 d| * (1 + log d)^2 ≤ C := rhoK_fixed_moment (by norm_num)
example : ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 2 ≤ K → K ≤ 6 → ∀ n : ℕ,
    ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d)^2 ≤ C * √(log K) :=
  rhoK_moment_bounded_modulus 6
example : Summable (fun n : ℕ => (1 : ArithmeticFunction ℝ) n) := by
  have hu {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : (1 : ArithmeticFunction ℝ) (p^k) = 0 := by
    simp [hp.ne_one, hk]
  apply summable_of_prime_power_tail
  · simp
  · intro n; rw [ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  · simp
  · intro m n hmn
    exact ArithmeticFunction.isMultiplicative_one.map_mul_of_coprime hmn
  · intro p k hp hk
    exact hu hp (by omega)
  · have he : (fun p : Nat.Primes => (1 : ArithmeticFunction ℝ) p +
          (1 : ArithmeticFunction ℝ) ((p:ℕ)^2) + (1 : ArithmeticFunction ℝ) ((p:ℕ)^3)) =
        fun _ => 0 := by
      funext p
      have h1 := hu p.property (by norm_num : (1:ℕ) ≠ 0)
      simp only [pow_one] at h1
      rw [h1, hu p.property (by norm_num : (2:ℕ) ≠ 0), hu p.property (by norm_num : (3:ℕ) ≠ 0)]
      norm_num
    rw [he]
    exact summable_zero

end LeanLab.AlmostPrimeSums.Decomp1544b
