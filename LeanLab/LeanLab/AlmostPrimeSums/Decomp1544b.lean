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

Leaves, all OPEN: `rhoK_mul_tauW`, `harmonic_asymp`, `sum_log_div_asymp`, `rhoK_hasSum`,
`rhoK_moment`, `Wq_ge_union`, `Q_mul_prime`, `sum_logsq_div_primes`, `one_le_Ttwin`.
Also used, from AlmostPrimes/Decomp1528a and Decomp1528b and not restated: `mertens1_abs`
and `mertens2_block`, assemblies CONDITIONAL ON the leaves of those files.
Assemblies, no sorry of their own: `Tsum_asymp`; `rhoK_partial`; `lemma3`, Lemma 3;
`prime_square_sum`, the prime sum on p. 64 with the three Mertens type estimates;
`Wq_lower`, the W_q display of p. 64 for 1 ≤ a ≤ 3.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress
on it.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.Decomp1544a
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale
import LeanLab.AlmostPrimes.Decomp1528b

open Finset Real Filter Topology
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

/-! ### Lemma 3, p. 62, in leaves -/

/-- LEAF. Unit U-1544. ρ_K * (τ(n)/n) = μ²(m)/f₁(m) as arithmetic functions: (μ/·) * (1/·) is
the unit, since twisting by the completely multiplicative 1/n respects Dirichlet convolution
and μ * 1 = ε. Route for Lemma 3, p. 62. -/
theorem rhoK_mul_tauW (K : ℕ) : rhoK K * tauW = hK K := by
  sorry

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

/-- LEAF. Unit U-1544. Σ_{d ≤ x} log d/d = ½ log² x + O(1) for x ≥ 1, by comparison with
∫_1^x log t/t dt, the function log t/t being decreasing for t ≥ e. Route for Lemma 3, p. 62. -/
theorem sum_log_div_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ d ∈ Ioc 0 ⌊x⌋₊, log d / d - (log x) ^ 2 / 2| ≤ C := by
  sorry

/-- LEAF. Unit U-1544. Euler product: for even K ≥ 2, Σ_d ρ_K(d) converges to T Q(K)/4 = 2C_K.
The local factor at p is (p - 1)²/p², which is 1/4 at p = 2, at an odd p ∣ K, and
(p - 1)²/(p(p - 2)) at p ∤ K. Route: `EulerProduct.eulerProduct_hasProd` with
summability from `rhoK_moment`. Route for Lemma 3, p. 62. -/
theorem rhoK_hasSum {K : ℕ} (hK : Even K) (hK2 : 2 ≤ K) :
    HasSum (fun d => rhoK K d) (Ttwin * Q K / 4) := by
  sorry

/-- LEAF. Unit U-1544. Moment bound, uniform in K: Σ_{d ≤ n} |ρ_K(d)| (1 + log d)² ≤ C √(log K)
for even K ≥ 2. ρ_K is multiplicative, supported on cube free times p³, with
|ρ_K(p)| ≤ 2/p at p ∣ K and ≤ 4/(p(p - 2)) at p ∤ K; the full sum is ≪ (log log K)⁴. Route for
Lemma 3, p. 62. -/
theorem rhoK_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, Even K → 2 ≤ K → ∀ n : ℕ,
      ∑ d ∈ Ioc 0 n, |rhoK K d| * (1 + log d) ^ 2 ≤ C * √(log K) := by
  sorry

/-- Σ_{n ≤ y} τ(n)/n = ½ log² y + 2γ log y + O(1) for y ≥ 1.
Assembly, CONDITIONAL ON `harmonic_asymp`, `sum_log_div_asymp`, with Mathlib
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
Assembly, CONDITIONAL ON `rhoK_hasSum` and `rhoK_moment`. -/
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

/-- **Lemma 3**, p. 62, in the form used on p. 64: there is C with
|Σ_{m ≤ x, (m, K) = 1} μ²(m)/f₁(m) - C_K log² x| ≤ C (1 + log x) √(log K)
for every even K ≥ 2 and x ≥ 1. Assembly, CONDITIONAL ON `rhoK_mul_tauW`, `rhoK_moment` and
the leaves of `Tsum_asymp` and `rhoK_partial`. -/
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
  sorry

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
`sum_logsq_div_primes` and the Decomp1528 leaves behind `mertens1_abs` and `mertens2_block`. -/
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

/-- LEAF. Unit U-1544. The inequality opening the case a > 1 on p. 64:
W_q ≥ Σ_{m ≤ w} μ²(m)/f₁(m) - Σ_{z<p≤w} (1/f₁(p)) Σ_{m' ≤ w/p, (m', p) = 1} μ²(m')/f₁(m'),
with 1/f₁(p) = 2/(p - 2) and (m', p) = 1, (m', N) = 1 written as (m', pN) = 1. True for even
N because an m ≤ w prime to N with g(m) > z has a prime p > z, p ≤ w, and every term is ≥ 0. -/
theorem Wq_ge_union {N : ℕ} {w : ℝ} (hN : Even N) (hw : 1 ≤ w) :
    G N w - ∑ p ∈ bigPrimes N w, 2 / ((p : ℝ) - 2) * G (p * N) (w / p) ≤ Wq N w := by
  sorry

/-- LEAF. Unit U-1544. Q(pN) = (p - 2)/p · Q(N) for an odd prime p ∤ N, N ≥ 1; hence
2/(p - 2) C_{pN} = 2/p C_N, the identity used on p. 64. -/
theorem Q_mul_prime {N p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpN : ¬ p ∣ N) (hN : N ≠ 0) :
    Q (p * N) = ((p : ℝ) - 2) / p * Q N := by
  sorry

/-- LEAF. Unit U-1544. T = ∏_{p > 2} (p - 1)²/(p(p - 2)) ≥ 1: every factor is ≥ 1 and the
product converges, p. 61. -/
theorem one_le_Ttwin : 1 ≤ Ttwin := by
  sorry

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
Assembly, CONDITIONAL ON `Wq_ge_union`, `Q_mul_prime`, `one_le_Ttwin`, and the leaves of
`lemma3` and `prime_square_sum`, with `Decomp1528b.mertens2_block`. -/
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

end LeanLab.AlmostPrimeSums.Decomp1544b
