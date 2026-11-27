import LeanLab.AlmostPrimeSums.Decomp243a

/-!
AI wrote this Lean code, burst S82 burst-20261122 feed1122. Binary Goldbach is open.
Split of `Decomp243a.lower_sieve_application` into leaves following
BJS https://arxiv.org/abs/2207.09452 pp. 43 to 44 equations 141 to 145.
The sieve set is `A = {N - p : p < N, p prime, p ∤ N}` with density `g(d) = 1/φ(d)`
and main mass `X = π(N)`. The parent is proved here from the leaves as
`lower_sieve_application_of_leaves`. The original file is untouched, because
its definitions live in it, so importing this file there would be a cycle.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a

noncomputable section

/-- The sifting primorial `P(z) = ∏_{2 < p < N^θ, p ∤ N} p`, the product of the primes
indexing `sieveProduct`. BJS p. 37 equation 109 and p. 38 equation 119. -/
def sievePrimorial (N : ℕ) (θ : ℝ) : ℕ :=
  ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
    (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N), p

/-- The sieve remainder `R = Σ_{d ∣ P(z), d < D} |#A_d - X/φ(d)|` with `X = π(N)` and
`D = sieveLevel N B`. BJS p. 3 equations 3 and 10, specialised on p. 43 equation 141. -/
def sieveRemainder (N : ℕ) (B : ℝ) : ℝ :=
  ∑ d ∈ (sievePrimorial N ((1 : ℝ) / 8)).divisors.filter
      (fun d : ℕ => (d : ℝ) < sieveLevel N B),
    |(#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p)) : ℝ)
      - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|

/-- LEAF: BJS p. 43 equation 142, the lower linear sieve applied to `A` at
`z = N^{1/8}`, level `D = sieveLevel N B`, `X = π(N)`, `g(d) = 1/φ(d)`, with a varying
relative error `O((log N)^{-1/3})`. Iwaniec 1980 Rosser sieve, or Halberstam and Richert
Theorem 8.4 with an improved error; Halberstam and Richert Theorem 11.1 alone has the
weaker error `(log log D)^{3/4} (log D)^{-1/4}`. Class HARD. -/
theorem leaf_linear_sieve_lower (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) *
          fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 8)))
        - C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) /
            log N ^ ((1 : ℝ) / 3)
        - sieveRemainder N B ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  sorry

/-- LEAF: BJS p. 43 equation 141, the remainder bound from Bombieri Vinogradov:
for some level exponent `B`, `R ≤ C N / (log N)^3`. Uses `LevelBV` with `A = 3`,
squarefree moduli and the identity `#A_d = π(N - 1; d, N) - #{p ∣ N, d ∣ N - p}`.
Class HARD. -/
theorem leaf_remainder_BV (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      sieveRemainder N B ≤ C * N / log N ^ 3 := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962 Corollary 1, `π(x) > x / log x` for `x ≥ 17`,
used to pass from `X = π(N)` to the ideal mass `N / log N` of BJS p. 43 equation 142.
Class MEDIUM. -/
theorem leaf_pi_lower : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (N : ℝ) / log N ≤ Nat.primeCounting N := by
  sorry

/-- LEAF: Chebyshev upper bound `π(x) ≤ 2 x / log x` for large `x`,
used to absorb the relative sieve error of BJS p. 44 equation 145. Class MEDIUM. -/
theorem leaf_pi_upper : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Nat.primeCounting N : ℝ) ≤ 2 * N / log N := by
  have h₁ : 0 < (2 - Real.log 4 : ℝ) := by
    have := Real.log_two_lt_d9
    have := Real.log_two_gt_d9
    norm_num at *
    <;> linarith
  have h₂ : ∀ᶠ (x : ℝ) in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + (2 - Real.log 4)) * x / Real.log x := by
    -- Chebyshev.eventually_primeCounting_le uses notation π for Nat.primeCounting
    have h₃ : ∀ᶠ (x : ℝ) in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + (2 - Real.log 4)) * x / Real.log x := by
      simpa using Chebyshev.eventually_primeCounting_le h₁
    exact h₃
  have h₃ : ∃ (X₀ : ℝ), ∀ (x : ℝ), x ≥ X₀ → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + (2 - Real.log 4)) * x / Real.log x := by
    rw [eventually_atTop] at h₂
    obtain ⟨X₀, hX₀⟩ := h₂
    refine' ⟨X₀, fun x hx => _⟩
    exact hX₀ x hx
  obtain ⟨X₀, hX₀⟩ := h₃
  use ⌈X₀⌉₊
  intro N hN
  have h₄ : (N : ℝ) ≥ X₀ := by
    have h₄₁ : (⌈X₀⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h₄₂ : X₀ ≤ (⌈X₀⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil X₀
    linarith
  have h₅ : (Nat.primeCounting ⌊(N : ℝ)⌋₊ : ℝ) ≤ (Real.log 4 + (2 - Real.log 4)) * (N : ℝ) / Real.log (N : ℝ) := hX₀ (N : ℝ) h₄
  have h₆ : ⌊(N : ℝ)⌋₊ = N := by
    rw [Nat.floor_eq_iff]
    <;> norm_cast
    <;> simp [Nat.cast_le]
    <;> norm_num
    <;> linarith
  rw [h₆] at h₅
  have h₇ : (Real.log 4 + (2 - Real.log 4) : ℝ) = 2 := by ring
  rw [h₇] at h₅
  have h₈ : (2 : ℝ) * (N : ℝ) / Real.log (N : ℝ) = (2 : ℝ) * (N : ℝ) / Real.log (N : ℝ) := rfl
  simpa [h₈, Nat.cast_id] using h₅

/-- `f(s) ≥ 0` for the closed form lower sieve function. -/
theorem fsieve_nonneg (s : ℝ) : 0 ≤ fsieve s := by
  unfold fsieve
  split_ifs with hs
  · exact le_rfl
  · push Not at hs
    have h1 : 0 < log (s - 1) := log_pos (by linarith)
    have h2 : 0 < s := by linarith
    positivity

/-- A uniform positive lower bound for `U_N`. -/
theorem U_ge (N : ℕ) : 2 * exp (-eulerMascheroniConstant) * twinC ≤ U N := by
  unfold U
  have h1 := one_le_oddFactor N
  have h2 : 0 ≤ 2 * exp (-eulerMascheroniConstant) * twinC := by
    have := twinC_pos; positivity
  calc 2 * exp (-eulerMascheroniConstant) * twinC
      = 2 * exp (-eulerMascheroniConstant) * twinC * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2

/-- The parent `lower_sieve_application`, assembled from the four leaves.
CONDITIONAL ON LevelBV and the open leaves above. -/
theorem lower_sieve_application_of_leaves (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N → lowerMain N B - C * sieveError N ≤
        SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  obtain ⟨B, C2, hB, hC2, N2, h2⟩ := leaf_remainder_BV h
  obtain ⟨C1, hC1, N1, h1⟩ := leaf_linear_sieve_lower B hB
  obtain ⟨N3, h3⟩ := leaf_pi_lower
  obtain ⟨N4, h4⟩ := leaf_pi_upper
  set K : ℝ := 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hratio := (idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) < K by rw [hK]; linarith))
  obtain ⟨N5, h5⟩ := eventually_atTop.mp hratio
  set c0 : ℝ := 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC)
    with hc0
  have hc0pos : 0 < c0 := by have := twinC_pos; rw [hc0]; positivity
  refine ⟨B, 2 * C1 * K + C2 / c0, hB, by positivity, max (max (max N1 N2) (max N3 N4))
    (max N5 3), fun N hEven hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN3, hN4⟩, hN5, hN6⟩ := hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN6
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hLpos : 0 < log (N : ℝ) := by linarith
  set L := log (N : ℝ) with hL
  set P := sieveProduct N ((1 : ℝ) / 8)
  set f := fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 8)))
  set pi : ℝ := (Nat.primeCounting N : ℝ)
  have hP : 0 < P := sieveProduct_pos _ _
  have hf : 0 ≤ f := fsieve_nonneg _
  have hM : 0 < Mchen N := Mchen_pos N (by omega)
  have hA := h1 N hEven hN1
  have hR := h2 N hN2
  have hpl := h3 N hN3
  have hpu := h4 N hN4
  have hI := h5 N hN5
  have hI' : idealMass N (1 / 8) ≤ K * Mchen N := by
    have := (div_lt_iff₀ hM).mp hI; linarith
  have hL14 : 0 < L ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hLpos _
  have hL13 : 0 < L ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hLpos _
  have h1413 : L ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 3) :=
    rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h14L : L ^ ((1 : ℝ) / 4) ≤ L := by
    calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := rpow_one L
  -- main term comparison
  have hmain : lowerMain N B ≤ pi * P * f := by
    simp only [lowerMain, idealMass]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpl hP.le) hf
  -- first error
  have hE1 : C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ 2 * C1 * K * sieveError N := by
    have hpiP : pi * P ≤ 2 * K * Mchen N := by
      calc pi * P ≤ 2 * N / L * P := mul_le_mul_of_nonneg_right hpu hP.le
        _ = 2 * idealMass N (1 / 8) := by simp only [idealMass]; ring
        _ ≤ 2 * (K * Mchen N) := by linarith
        _ = 2 * K * Mchen N := by ring
    calc C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ C1 * (2 * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpiP hC1.le) hL14 h1413
      _ = 2 * C1 * K * sieveError N := by simp only [sieveError]; ring
  -- second error
  have hE2 : sieveRemainder N B ≤ C2 / c0 * sieveError N := by
    have hU := U_ge N
    have hMc : c0 * N / L ^ 2 ≤ Mchen N := by
      simp only [Mchen, hc0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (N : ℝ) := hNpos.le
      have he : 0 < 2 * exp eulerMascheroniConstant := by positivity
      calc 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC) * N
          = 2 * exp eulerMascheroniConstant * ((2 * exp (-eulerMascheroniConstant) * twinC) * N)
            := by ring
        _ ≤ 2 * exp eulerMascheroniConstant * (U N * N) := by gcongr
        _ = _ := by ring
    calc sieveRemainder N B ≤ C2 * N / L ^ 3 := hR
      _ ≤ C2 * N / (L ^ 2 * L ^ ((1 : ℝ) / 4)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [pow_succ]; exact mul_le_mul_of_nonneg_left h14L (by positivity)
      _ = C2 / c0 * ((c0 * N / L ^ 2) / L ^ ((1 : ℝ) / 4)) := by
          field_simp
      _ ≤ C2 / c0 * (Mchen N / L ^ ((1 : ℝ) / 4)) := by
          gcongr
      _ = C2 / c0 * sieveError N := by simp only [sieveError]; rfl
  have hfin : lowerMain N B - (2 * C1 * K + C2 / c0) * sieveError N ≤
      pi * P * f - C1 * (pi * P) / L ^ ((1 : ℝ) / 3) - sieveRemainder N B := by
    nlinarith only [hmain, hE1, hE2]
  exact hfin.trans hA

end

#print axioms lower_sieve_application_of_leaves
#print axioms fsieve_nonneg
#print axioms U_ge

end LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower