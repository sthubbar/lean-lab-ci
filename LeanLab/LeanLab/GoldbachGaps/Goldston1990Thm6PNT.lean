import LeanLab.GoldbachGaps.Goldston1990Thm6
import LeanLab.GoldbachAverage.OddSumPNT

/-!
# Goldston 1990, the Theorem of display 6, PROVED

Lab proof, unit U-6300, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990.

`theorem6_proved : Theorem6`: the cited Prop `Theorem6` of `Goldston1990Main.lean`, display 6,
with `C = 1`, from `fejer_explicit` and the prime number theorem with error term of the lab's
StrongPNT port, `GoldbachAverage.psi_div_log`, plus Mathlib's `ψ - θ ≪ √x`. No cited input, no
hypothesis: unconditional. Goldston's own proof needs the unconditional bound
`J(N, h) = o(h² N)` for `h ≥ N^{1/6 + ε}`; the window form of the Fejér step avoids it.

With this, `near_of_theorem6` and `near_even_of_theorem6` hold outright, and the corollaries'
inputs reduce to bounds on `J(N, K)` alone. Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset

/-- The prime number theorem for `θ` on the naturals, with error `A N/log N + C √N`. -/
lemma theta_pnt_nat : ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    |θ (N : ℝ) - N| ≤ A * N / Real.log N + C * Real.sqrt N := by
  obtain ⟨A, hA, hpsi⟩ := LeanLab.GoldbachAverage.psi_div_log
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨A, |C|, hA, abs_nonneg _, fun N hN => ?_⟩
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := hpsi N hx
  have h2 := hC N
  have h3 := theta_le_psi (N : ℝ)
  have h4 : C * √(N : ℝ) ≤ |C| * √(N : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
  have h5 : 0 ≤ |C| * √(N : ℝ) := by positivity
  rw [abs_le] at h1 ⊢; constructor <;> linarith

/-- **Goldston's Theorem, display 6, PROVED unconditionally.** -/
theorem theorem6_proved : Theorem6 := by
  obtain ⟨A, C, hA, hC, hθ⟩ := theta_pnt_nat
  refine ⟨1, one_pos, fun ε hε => ?_⟩
  set M : ℝ := max 1 (max (16 * A / ε) (84 / ε)) with hM
  set S : ℝ := 16 * C / ε + 1 with hS
  refine ⟨⌈Real.exp M⌉₊ + ⌈S ^ 2⌉₊ + 3, fun N hN K hK hKle => ?_⟩
  have hN3 : 3 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNexp : Real.exp M ≤ N := by
    have := Nat.le_ceil (Real.exp M)
    have h' : (⌈Real.exp M⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp M⌉₊ ≤ N by omega)
    linarith
  have hNS : S ^ 2 ≤ N := by
    have := Nat.le_ceil (S ^ 2)
    have h' : (⌈S ^ 2⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈S ^ 2⌉₊ ≤ N by omega)
    linarith
  set L := Real.log N with hL
  have hLM : M ≤ L := by
    rw [hL, ← Real.log_exp M]; exact Real.log_le_log (Real.exp_pos M) hNexp
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLM
  have hLA : 16 * A / ε ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLM
  have hL84 : 84 / ε ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLM
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hsqrt : S ≤ Real.sqrt N := by
    rw [← Real.sqrt_sq hS0]; exact Real.sqrt_le_sqrt hNS
  have hL3 : 0 < L ^ 3 := by positivity
  have hKL : (K : ℝ) * L ^ 3 ≤ N := (le_div_iff₀ hL3).mp hKle
  have hKN : K ≤ N := by
    have : (K : ℝ) ≤ N := by nlinarith [one_le_pow₀ (n := 3) hL1]
    exact_mod_cast this
  have hE := fejer_explicit N K hK hKN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- the θ term
  have hθN := hθ N (by omega)
  have hA' : A * N / L ≤ ε * N / 16 := by
    rw [div_le_iff₀ (by linarith)]
    have : 16 * A ≤ ε * L := by rw [div_le_iff₀ hε] at hLA; linarith
    nlinarith
  have hC' : C * Real.sqrt N ≤ ε * N / 16 := by
    have hs : 16 * C ≤ ε * Real.sqrt N := by
      have : 16 * C / ε ≤ Real.sqrt N := by linarith
      rw [div_le_iff₀ hε] at this; linarith
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    have := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (N : ℝ))
    nlinarith
  have hθb : 2 * (K : ℝ) ^ 2 * |θ (N : ℝ) - N| ≤ ε * K ^ 2 * N / 4 := by
    have : |θ (N : ℝ) - N| ≤ ε * N / 8 := by linarith
    have hK2 : (0 : ℝ) ≤ K ^ 2 := by positivity
    nlinarith
  -- the K³ term
  have hlogNK : Real.log (N + K) ≤ 2 * L := by
    have h2N : (N : ℝ) + K ≤ 2 * N := by
      have : (K : ℝ) ≤ N := by exact_mod_cast hKN
      linarith
    have := Real.log_le_log (by positivity) h2N
    rw [Real.log_mul (by norm_num) hNpos.ne'] at this
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogNK0 : 0 ≤ Real.log (N + K) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith)
  have hΦ : 2 * Real.log (N + K) ^ 2 + 1 + 2 * (L + 1) + 2 * (L + 1) ^ 2 ≤ 21 * L ^ 2 := by
    have : Real.log (N + K) ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hlogNK0 hlogNK 2
    nlinarith
  have hKL2 : (K : ℝ) * L ^ 2 * 84 ≤ ε * N := by
    have h84 : 84 ≤ ε * L := by rw [div_le_iff₀ hε] at hL84; linarith
    have hKL20 : (0 : ℝ) ≤ K * L ^ 2 := by positivity
    calc (K : ℝ) * L ^ 2 * 84 ≤ K * L ^ 2 * (ε * L) := mul_le_mul_of_nonneg_left h84 hKL20
      _ = ε * (K * L ^ 3) := by ring
      _ ≤ ε * N := mul_le_mul_of_nonneg_left hKL hε.le
  have hK3 : (K : ℝ) ^ 3 * (2 * Real.log (N + K) ^ 2 + 1 + 2 * (L + 1) + 2 * (L + 1) ^ 2) ≤
      ε * K ^ 2 * N / 4 := by
    have hK3' : (0 : ℝ) ≤ K ^ 3 := by positivity
    calc (K : ℝ) ^ 3 * (2 * Real.log (N + K) ^ 2 + 1 + 2 * (L + 1) + 2 * (L + 1) ^ 2)
        ≤ (K : ℝ) ^ 3 * (21 * L ^ 2) := mul_le_mul_of_nonneg_left hΦ hK3'
      _ = (K : ℝ) ^ 2 * (K * L ^ 2 * 84) / 4 := by ring
      _ ≤ (K : ℝ) ^ 2 * (ε * N) / 4 := by
          have : (0 : ℝ) ≤ K ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hKL2 this
          linarith
      _ = ε * K ^ 2 * N / 4 := by ring
  have hKN0 : (0 : ℝ) ≤ 1 * K * N := by positivity
  have hεK : 0 ≤ ε * (K : ℝ) ^ 2 * N := by positivity
  linarith

/-- `near_of_theorem6` with no hypothesis: a sum of two primes in `[N - K, N + K]` whenever
`K > 4`, `K ≤ N / log³ N` and `J(N, K) ≤ K² N / 2`, for all large `N`. Unconditional. -/
theorem near_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 4 * C < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Jg N K ≤ (K : ℝ) ^ 2 * N / 2 →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ IsGoldbachSum m :=
  near_of_theorem6 theorem6_proved

/-- The even form, unconditional. -/
theorem near_even_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 4 * C < K →
      (K : ℝ) ≤ N / Real.log N ^ 3 → Jg N K ≤ (K : ℝ) ^ 2 * N / 2 →
      ∃ m, N - K ≤ m ∧ m ≤ N + K ∧ Even m ∧ IsGoldbachSum m :=
  near_even_of_theorem6 theorem6_proved

/-- Page 287, now CONDITIONAL ON `PC9Upper` only, the upper half of display 9, a pair
correlation hypothesis that is NOT known: every interval around `N` of length about
`(2 + 2ε) log N` holds a sum of two primes, for large `N`. -/
theorem short_of_pc (hPC : PC9Upper) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ m : ℕ, IsGoldbachSum m ∧
      (N : ℝ) - ((1 + ε) * Real.log N + 1) ≤ m ∧ (m : ℝ) ≤ N + ((1 + ε) * Real.log N + 1) :=
  short_of_theorem6_pc theorem6_proved hPC ε hε hε1

/-- The even form, CONDITIONAL ON `PC9Upper` only. -/
theorem short_even_of_pc (hPC : PC9Upper) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ m : ℕ, Even m ∧ IsGoldbachSum m ∧
      (N : ℝ) - ((1 + ε) * Real.log N + 1) ≤ m ∧ (m : ℝ) ≤ N + ((1 + ε) * Real.log N + 1) :=
  short_even_of_theorem6_pc theorem6_proved hPC ε hε hε1

end LeanLab.GoldbachGaps.Goldston1990
