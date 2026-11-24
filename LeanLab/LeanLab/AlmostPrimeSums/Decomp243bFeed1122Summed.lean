import LeanLab.AlmostPrimeSums.Base243
import LeanLab.AlmostPrimeSums.Lower243

/-!
AI wrote this Lean code, burst S82 burst-20261122 feed1122. Binary Goldbach is open.
Split of `Decomp243b.summed_sieve_application` into leaves following
BJS https://arxiv.org/abs/2207.09452 pp. 52 to 54 equations 164 to 172.
For each middle prime `q` the sieve set is `A_q = {N - p : q ∣ N - p}`, of mass
`π(N)/(q - 1)` with density `g(d) = 1/φ(d)`, sifted to level `D/q`.
The parent is proved here from the leaves as `summed_sieve_application_of_leaves`,
over the definitions of `Base243` and `Decomp243a`, so `Decomp243b` can import this file.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243bFeed1122Summed

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243b

noncomputable section

/-- The sifting primorial `P(z) = ∏_{2 < p < N^{1/8}, p ∤ N} p`, the product of the primes
indexing `sieveProduct N (1/8)`. BJS p. 37 equation 109 and p. 38 equation 119. -/
def summedPrimorial (N : ℕ) : ℕ :=
  ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
    (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N), p

/-- The summed remainder `Σ_q Σ_{d ∣ P(z), d < D/q} |#A_{qd} - π(N)/φ(qd)|` over the
primes `q` of `qSet`, with `D = sieveLevel N B`. BJS p. 3 equations 3 and 10,
specialised on p. 53 equations 168 to 171. -/
def summedRemainder (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ qSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)),
    ∑ d ∈ (summedPrimorial N).divisors.filter
        (fun d : ℕ => (d : ℝ) < sieveLevel N B / q),
      |(#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ q * d ∣ N - p)) : ℝ)
        - (Nat.primeCounting N : ℝ) / ((q * d).totient : ℝ)|

/-- LEAF: BJS pp. 52 to 53 equations 164 to 170, the upper linear sieve applied to each
`A_q` at `z = N^{1/8}`, level `D/q`, mass `π(N)/(q - 1)`, summed over `q`, with the sum
of `F(s_q)/(q - 1)` extended from `q ∤ N` to all middle primes, and a varying relative
error `O((log N)^{-1/3})`. Iwaniec 1980 Rosser sieve, or Halberstam and Richert
Theorem 8.4 with an improved error; Theorem 11.1 alone has the weaker error
`(log log D)^{3/4} (log D)^{-1/4}`. Class HARD. -/
theorem leaf_summed_linear_sieve_upper (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
        ≤ (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) * primeCoefficient N B
          + C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) /
              log N ^ ((1 : ℝ) / 3)
          + summedRemainder N B := by
  sorry

/-- LEAF: BJS p. 53 equation 171, the bilinear remainder bound from Bombieri
Vinogradov: for some level exponent `B`, the summed remainder is at most
`C N / (log N)^3`. Moduli `qd < D` are squarefree; each is counted at most
`ω(qd)` times, absorbed by taking `A = 4` in `LevelBV`. Class HARD. -/
theorem leaf_summed_remainder_BV (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      summedRemainder N B ≤ C * N / log N ^ 3 := by
  sorry

/-- LEAF: Rosser and Schoenfeld 1962 Theorem 1 equation 3.2,
`π(x) < x/log x · (1 + 3/(2 log x))` for `x > 1`, in the weaker eventual form
`π(N) ≤ N/log N + 2N/(log N)^2`; passes from `X = π(N)` to the ideal mass of
BJS p. 52 equation 164. Class MEDIUM. -/
theorem leaf_pi_upper_sharp : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Nat.primeCounting N : ℝ) ≤ N / log N + 2 * N / log N ^ 2 := by
  sorry

/-- A uniform positive lower bound for `U_N`. -/
theorem U_ge' (N : ℕ) : 2 * exp (-eulerMascheroniConstant) * twinC ≤ U N := by
  unfold U
  have h1 := one_le_oddFactor N
  have h2 : 0 ≤ 2 * exp (-eulerMascheroniConstant) * twinC := by
    have := twinC_pos; positivity
  calc 2 * exp (-eulerMascheroniConstant) * twinC
      = 2 * exp (-eulerMascheroniConstant) * twinC * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2

/-- The parent `summed_sieve_application`, assembled from the three leaves and the
proved prime coefficient limit. CONDITIONAL ON LevelBV and the open leaves above. -/
theorem summed_sieve_application_of_leaves (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N →
      (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ summedMain N B + C * sieveError N := by
  obtain ⟨B, C2, hB, hC2, N2, h2⟩ := leaf_summed_remainder_BV h
  obtain ⟨C1, hC1, N1, h1⟩ := leaf_summed_linear_sieve_upper B hB
  obtain ⟨N4, h4⟩ := leaf_pi_upper_sharp
  set K : ℝ := 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hratio := (idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) < K by rw [hK]; linarith))
  obtain ⟨N5, h5⟩ := eventually_atTop.mp hratio
  set K2 : ℝ := exp eulerMascheroniConstant * log 6 / 2 + 1 with hK2
  have hlog6 : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have hK2pos : 0 < K2 := by rw [hK2]; positivity
  have hpc := LeanLab.AlmostPrimeSums.Lower243.primeCoefficient_limit B hB
  have hpc1 := hpc.eventually (gt_mem_nhds (show exp eulerMascheroniConstant * log 6 / 2 < K2 by
    rw [hK2]; linarith))
  have hpc0 := hpc.eventually (lt_mem_nhds (show (0 : ℝ) < exp eulerMascheroniConstant * log 6 / 2
    by positivity))
  obtain ⟨N6, h6⟩ := eventually_atTop.mp (hpc1.and hpc0)
  set c0 : ℝ := 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC)
    with hc0
  have hc0pos : 0 < c0 := by have := twinC_pos; rw [hc0]; positivity
  refine ⟨B, K * K2 + 3 * C1 * K + C2 / c0, hB, by positivity,
    max (max (max N1 N2) (max N4 N5)) (max N6 3), fun N hEven hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN4, hN5⟩, hN6, hN7⟩ := hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN7
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hLpos : 0 < log (N : ℝ) := by linarith
  set L := log (N : ℝ) with hL
  set P := sieveProduct N ((1 : ℝ) / 8)
  set pc := primeCoefficient N B
  set pi : ℝ := (Nat.primeCounting N : ℝ)
  have hP : 0 < P := sieveProduct_pos _ _
  have hM : 0 < Mchen N := Mchen_pos N (by omega)
  have hA := h1 N hEven hN1
  have hR := h2 N hN2
  have hpu := h4 N hN4
  have hI := h5 N hN5
  obtain ⟨hpcK, hpc0'⟩ := h6 N hN6
  have hI' : idealMass N (1 / 8) ≤ K * Mchen N := by
    have := (div_lt_iff₀ hM).mp hI; linarith
  have hidl : idealMass N (1 / 8) = N / L * P := rfl
  have hidpos : 0 ≤ idealMass N (1 / 8) := by rw [hidl]; positivity
  have hL14 : 0 < L ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hLpos _
  have hL13 : 0 < L ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hLpos _
  have h1413 : L ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 3) :=
    rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h14L : L ^ ((1 : ℝ) / 4) ≤ L := by
    calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := rpow_one L
  have hSE : sieveError N = Mchen N / L ^ ((1 : ℝ) / 4) := rfl
  have hSEpos : 0 ≤ sieveError N := by rw [hSE]; positivity
  -- π(N) ≤ 3 N / log N
  have hpi3 : pi * P ≤ 3 * idealMass N (1 / 8) := by
    have : 2 * N / L ^ 2 ≤ 2 * N / L := by
      apply div_le_div_of_nonneg_left (by positivity) hLpos
      nlinarith
    calc pi * P ≤ (N / L + 2 * N / L) * P := mul_le_mul_of_nonneg_right (by linarith) hP.le
      _ = 3 * idealMass N (1 / 8) := by rw [hidl]; ring
  -- main term
  have hmain : pi * P * pc ≤ 2 * summedMain N B + 2 * K * K2 * sieveError N := by
    have hstep : pi * P * pc ≤ (N / L + 2 * N / L ^ 2) * P * pc :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpu hP.le) hpc0'.le
    have hsplit : (N / L + 2 * N / L ^ 2) * P * pc =
        2 * summedMain N B + 2 * (idealMass N (1 / 8) * pc) / L := by
      simp only [summedMain, hidl]; field_simp; ring
    have hx : idealMass N (1 / 8) * pc ≤ K * Mchen N * K2 :=
      mul_le_mul hI' hpcK.le hpc0'.le (by positivity)
    have hy : 2 * (idealMass N (1 / 8) * pc) / L ≤ 2 * (K * Mchen N * K2) / L ^ ((1 : ℝ) / 4) :=
      div_le_div₀ (by positivity) (by linarith) hL14 h14L
    have hz : 2 * (K * Mchen N * K2) / L ^ ((1 : ℝ) / 4) = 2 * K * K2 * sieveError N := by
      rw [hSE]; ring
    linarith
  -- relative sieve error
  have hE1 : C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ 2 * (3 * C1 * K) * sieveError N := by
    have hpiP : pi * P ≤ 3 * K * Mchen N := by linarith
    calc C1 * (pi * P) / L ^ ((1 : ℝ) / 3) ≤ C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpiP hC1.le) hL14 h1413
      _ ≤ 2 * (3 * C1 * K) * sieveError N := by
          rw [hSE]
          have : 0 ≤ C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by positivity
          have he : 2 * (3 * C1 * K) * (Mchen N / L ^ ((1 : ℝ) / 4)) =
            2 * (C1 * (3 * K * Mchen N) / L ^ ((1 : ℝ) / 4)) := by ring
          rw [he]; linarith
  -- remainder
  have hE2 : summedRemainder N B ≤ 2 * (C2 / c0) * sieveError N := by
    have hU := U_ge' N
    have hMc : c0 * N / L ^ 2 ≤ Mchen N := by
      simp only [Mchen, hc0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (N : ℝ) := hNpos.le
      calc 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC) * N
          = 2 * exp eulerMascheroniConstant * ((2 * exp (-eulerMascheroniConstant) * twinC) * N)
            := by ring
        _ ≤ 2 * exp eulerMascheroniConstant * (U N * N) := by gcongr
        _ = _ := by ring
    have hb : summedRemainder N B ≤ C2 / c0 * sieveError N := by
      calc summedRemainder N B ≤ C2 * N / L ^ 3 := hR
        _ ≤ C2 * N / (L ^ 2 * L ^ ((1 : ℝ) / 4)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            rw [pow_succ]; exact mul_le_mul_of_nonneg_left h14L (by positivity)
        _ = C2 / c0 * ((c0 * N / L ^ 2) / L ^ ((1 : ℝ) / 4)) := by
            field_simp
        _ ≤ C2 / c0 * (Mchen N / L ^ ((1 : ℝ) / 4)) := by
            gcongr
        _ = C2 / c0 * sieveError N := by rw [hSE]
    have : 0 ≤ C2 / c0 * sieveError N := by positivity
    linarith
  have hfin : (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
      ≤ 2 * (summedMain N B + (K * K2 + 3 * C1 * K + C2 / c0) * sieveError N) := by
    have := hA
    nlinarith only [this, hmain, hE1, hE2]
  linarith

end

#print axioms summed_sieve_application_of_leaves
#print axioms U_ge'

end LeanLab.AlmostPrimeSums.Decomp243bFeed1122Summed
