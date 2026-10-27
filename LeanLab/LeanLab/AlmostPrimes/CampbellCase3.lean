/-
AI-written Lean code, Claude, 2026-10-20, session 20261020T2113Z-cloud51, unit U-6748.
P0020 P. J. Campbell 2026, A Sharper Explicit Result for the Sum of Two Almost Primes,
arXiv 2608.09488 v1, read on arxiv.org/html/2608.09488 this session, Section 5, proof of
Theorem 1.2, Case 3, `N ≥ N₁ = 10^132`: the sieve gives
`S(𝒜, z) > 6.34 (N - 1)/log² N - 2.05·10^-10 N^{14.66/16.5} log^8 N`, and the paper says
"This ratio is increasing for N ≥ 10^132, and at N = N₁ ... it exceeds 2.41", with no argument
for the monotonicity. `Campbell2026.case3_ratio` had the endpoint only.

PROVED here, no cited input:
* `case3_key`: `2.05e-10 · N^{14.66/16.5} · log^{10} N < 6.34 (N - 1)` for every real `N ≥ 10^132`.
* `case3_all`: `0 < 6.34 (N - 1)/log² N - 2.05e-10 · N^{14.66/16.5} · log^8 N` for every real
  `N ≥ 10^132`, the printed conclusion of Case 3, MATCH, so the unproved monotonicity is not needed.
Method as in DDCase3: `L = log N`, `L₀ = 132 log 10`, `u = L/L₀`,
`u^{10} ≤ e^{10(u-1)} ≤ e^{0.04(L-L₀)} ≤ e^{(1.84/16.5)(L-L₀)}`, and the endpoint is
`Campbell2026.case3_ratio`.

CONDITIONAL, counted apart:
* `theorem1_2_of_cases`: Theorem 1.2, `Ω(ab) ≤ 33` for every `N ≥ 2`, CONDITIONAL ON `GapTable`,
  `Case2Check`, the finite computer range `N₀ < N < 10^132`, and `Case3Sieve`, the printed sieve
  lower bound for `N ≥ 10^132` stated for the count `siftCount`. This replaces the single input
  `S(𝒜, z) > 0 for all N > N₀` of `Campbell2026.theorem1_2_of` by the paper's own sieve display.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.Campbell2026
import LeanLab.AlmostPrimes.DDCase3

open Real

noncomputable section
namespace LeanLab.AlmostPrimes.CampbellCase3
open LeanLab.AlmostPrimes Campbell2026

/-- `10^{(1.84/16.5) · 132 log 10 / log 10} = 10^{14.72}` as an exponential. -/
lemma exp_endpoint : exp ((1.84 / 16.5) * (132 * log 10)) = (10 : ℝ) ^ (14.72 : ℝ) := by
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  congr 1; ring_nf

/-- **Key bound, Case 3 for every `N ≥ 10^132`.** -/
theorem case3_key (N : ℝ) (hN : (10 : ℝ) ^ 132 ≤ N) :
    2.05e-10 * N ^ (14.66 / 16.5 : ℝ) * (log N) ^ 10 < 6.34 * (N - 1) := by
  obtain ⟨hl1, hl2⟩ := DDCase3.log_ten_bounds
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  set L := log N with hLdef
  set L0 := 132 * log 10 with hL0def
  have hL0L : L0 ≤ L := by
    have := Real.log_le_log (by positivity) hN
    rw [Real.log_pow] at this; push_cast at this; simpa [hL0def, hLdef] using this
  have hL0pos : 0 < L0 := by rw [hL0def]; linarith
  have hL0big : 250 ≤ L0 := by rw [hL0def]; linarith
  set u := L / L0 with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hL0pos.le
  have hpow := DDCase3.pow10_le_exp hu0
  have hexp_arg : 10 * (u - 1) ≤ (1.84 / 16.5) * (L - L0) := by
    have e : u - 1 = (L - L0) / L0 := by rw [hu]; field_simp
    rw [e]
    have hd : 0 ≤ L - L0 := by linarith
    rw [mul_div_assoc', div_le_iff₀ hL0pos]
    nlinarith
  have hpow2 : u ^ 10 ≤ exp ((1.84 / 16.5) * (L - L0)) :=
    hpow.trans (exp_le_exp.mpr hexp_arg)
  have hLu : L ^ 10 = L0 ^ 10 * u ^ 10 := by rw [hu, div_pow]; field_simp
  -- the endpoint, from `Campbell2026.case3_ratio`
  have hr := case3_ratio
  have hR0 : 0 < (10 : ℝ) ^ (14.72 : ℝ) := by positivity
  set R := (10 : ℝ) ^ (14.72 : ℝ) with hRdef
  set ε : ℝ := 1 - 1 / 10 ^ 132 with hε
  have hε0 : 0 < ε := by rw [hε]; norm_num
  have hend : 2.05e-10 * L0 ^ 10 < 6.34 * ε * R := by
    have h1 : 2.41 * L0 ^ 10 < (6.34 / 2.05e-10) * ε * R := hr
    have hL10 : 0 ≤ L0 ^ 10 := by positivity
    have : 2.05e-10 * (2.41 * L0 ^ 10) < 2.05e-10 * ((6.34 / 2.05e-10) * ε * R) :=
      mul_lt_mul_of_pos_left h1 (by norm_num)
    have e2 : (2.05e-10 : ℝ) * ((6.34 / 2.05e-10) * ε * R) = 6.34 * ε * R := by
      field_simp
    nlinarith [mul_pos hε0 hR0]
  -- exp(b L) = R · exp(b (L - L0)), b = 1.84/16.5
  have hexpL : exp ((1.84 / 16.5) * L) = R * exp ((1.84 / 16.5) * (L - L0)) := by
    rw [hRdef, ← exp_endpoint, ← exp_add]; congr 1; rw [hL0def]; ring
  have hcore : 2.05e-10 * L ^ 10 < 6.34 * ε * exp ((1.84 / 16.5) * L) := by
    rw [hLu, hexpL]
    have hE := exp_pos ((1.84 / 16.5) * (L - L0))
    have hu10 : 0 ≤ u ^ 10 := pow_nonneg hu0 10
    calc 2.05e-10 * (L0 ^ 10 * u ^ 10) = (2.05e-10 * L0 ^ 10) * u ^ 10 := by ring
      _ ≤ (2.05e-10 * L0 ^ 10) * exp ((1.84 / 16.5) * (L - L0)) :=
          mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ < (6.34 * ε * R) * exp ((1.84 / 16.5) * (L - L0)) := mul_lt_mul_of_pos_right hend hE
      _ = 6.34 * ε * (R * exp ((1.84 / 16.5) * (L - L0))) := by ring
  -- N - 1 ≥ ε N
  have hN1 : ε * N ≤ N - 1 := by
    have : 1 ≤ N / 10 ^ 132 := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [hε, sub_mul, one_mul, div_mul_eq_mul_div, one_mul]; linarith
  have hNr : N ^ (14.66 / 16.5 : ℝ) = exp ((14.66 / 16.5) * L) := by
    rw [rpow_def_of_pos hN0, hLdef, mul_comm]
  have hNe : N = exp ((14.66 / 16.5) * L) * exp ((1.84 / 16.5) * L) := by
    rw [← exp_add, show (14.66 / 16.5) * L + (1.84 / 16.5) * L = L by ring, hLdef, exp_log hN0]
  have hA := exp_pos ((14.66 / 16.5) * L)
  calc 2.05e-10 * N ^ (14.66 / 16.5 : ℝ) * L ^ 10
      = exp ((14.66 / 16.5) * L) * (2.05e-10 * L ^ 10) := by rw [hNr]; ring
    _ < exp ((14.66 / 16.5) * L) * (6.34 * ε * exp ((1.84 / 16.5) * L)) :=
        mul_lt_mul_of_pos_left hcore hA
    _ = 6.34 * (ε * (exp ((14.66 / 16.5) * L) * exp ((1.84 / 16.5) * L))) := by ring
    _ = 6.34 * (ε * N) := by rw [← hNe]
    _ ≤ 6.34 * (N - 1) := by linarith

/-- **Campbell Theorem 1.2, Case 3, the final display, for every real `N ≥ 10^132`.** MATCHES. -/
theorem case3_all (N : ℝ) (hN : (10 : ℝ) ^ 132 ≤ N) :
    0 < 6.34 * (N - 1) / (log N) ^ 2 - 2.05e-10 * N ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8 := by
  have hk := case3_key N hN
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have hl2 : 0 < (log N) ^ 2 := by have := log_pos hN1; positivity
  rw [sub_pos, lt_div_iff₀ hl2]
  calc 2.05e-10 * N ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8 * (log N) ^ 2
      = 2.05e-10 * N ^ (14.66 / 16.5 : ℝ) * (log N) ^ 10 := by ring
    _ < 6.34 * (N - 1) := hk

/-! ### Theorem 1.2 from the paper's three cases -/

/-- `N₁ = 10^132`, Section 4. -/
def N1 : ℕ := 10 ^ 132

/-- `S(𝒜, z)` as a count: the `1 ≤ n ≤ N - 1` whose `aₙ` has no prime factor below `z`.
For `z > 3` this is the paper's pre-sieved count, see `Campbell2026.SiftedExists`. -/
def siftCount (N : ℕ) (z : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 (N - 1)).filter
    (fun n => ∀ p : ℕ, p.Prime → p ∣ aSeq N n → z ≤ p)).card

theorem siftedExists_of_count_pos {N : ℕ} {z : ℝ} (h : 0 < siftCount N z) :
    SiftedExists N z := by
  classical
  unfold siftCount at h
  obtain ⟨n, hn⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  exact ⟨n, hn.1.1, hn.1.2, hn.2⟩

/-- Cited: Case 2, the paper's finite computer verification, read as
`S(𝒜, N^{1/16.5}) > 0` for `N₀ < N < N₁`. -/
def Case2Check : Prop :=
  ∀ N : ℕ, N0 < N → N < N1 → SiftedExists N ((N : ℝ) ^ (1 / (16.5 : ℝ)))

/-- Cited: Case 3's sieve lower bound from Theorem 2.1 and Lemmas 4.1 to 4.3, as printed,
weakened from `>` to `≤`. -/
def Case3Sieve : Prop :=
  ∀ N : ℕ, N1 ≤ N →
    6.34 * ((N : ℝ) - 1) / (log N) ^ 2 - 2.05e-10 * (N : ℝ) ^ (14.66 / 16.5 : ℝ) * (log N) ^ 8
      ≤ (siftCount N ((N : ℝ) ^ (1 / (16.5 : ℝ))) : ℝ)

/-- **Case 3, CONDITIONAL ON `Case3Sieve`:** `S(𝒜, N^{1/16.5}) > 0` for every `N ≥ 10^132`. -/
theorem case3_sifted (h3 : Case3Sieve) (N : ℕ) (hN : N1 ≤ N) :
    SiftedExists N ((N : ℝ) ^ (1 / (16.5 : ℝ))) := by
  apply siftedExists_of_count_pos
  have hR : (10 : ℝ) ^ 132 ≤ N := by
    have h : 10 ^ 132 ≤ N := hN
    exact_mod_cast h
  have := lt_of_lt_of_le (case3_all N hR) (h3 N hN)
  exact_mod_cast this

/-- **Theorem 1.2, CONDITIONAL ON `GapTable`, `Case2Check` and `Case3Sieve`.** -/
theorem theorem1_2_of_cases (hG : GapTable) (h2 : Case2Check) (h3 : Case3Sieve) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  apply theorem1_2_of hG
  intro N hN
  rcases Nat.lt_or_ge N N1 with h | h
  · exact h2 N hN h
  · exact case3_sifted h3 N h

#print axioms exp_endpoint
#print axioms case3_key
#print axioms case3_all
#print axioms siftedExists_of_count_pos
#print axioms case3_sifted
#print axioms theorem1_2_of_cases
#print axioms Campbell2026.lemma5_1
#print axioms Campbell2026.lemma5_2
#print axioms Campbell2026.theorem1_2_of
#print axioms Campbell2026.case3_ratio

end LeanLab.AlmostPrimes.CampbellCase3
