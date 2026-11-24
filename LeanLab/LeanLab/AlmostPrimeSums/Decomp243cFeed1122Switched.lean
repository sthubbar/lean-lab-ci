import LeanLab.AlmostPrimeSums.Decomp243b
import LeanLab.AlmostPrimeSums.Double243

/-!
AI wrote this Lean code, burst S82 burst-20261122 feed1122. Binary Goldbach is open.
Split of `Decomp243c.switched_sieve_application` into leaves following
BJS https://arxiv.org/abs/2207.09452 p. 59 equation 191 and pp. 59 to 60.
The sieve set is the switched set `B = {N - m : m ∈ T}` sifted to `y = N^{1/3}`,
with mass `X = #T` and density `g(d) = 1/φ(d)`. The parent is proved here from the
leaves as `switched_sieve_application_of_leaves`, stated with `switchedMain`
unfolded, so `Decomp243c` can import this file without a cycle.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243cFeed1122Switched

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243b

noncomputable section

/-- The switched sifting primorial `P(y) = ∏_{2 < p < N^{1/3}, p ∤ N} p`, the product of
the primes indexing `sieveProduct N (1/3)`. BJS p. 37 equation 109 at `y`. -/
def switchedPrimorial (N : ℕ) : ℕ :=
  ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
    (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3) ∧ ¬ p ∣ N), p

/-- The switched remainder `Σ_{d ∣ P(y), d < D} |#B_d - #T/φ(d)|` with
`D = sieveLevel N B`. BJS p. 3 equations 3 and 10, specialised on pp. 59 to 60. -/
def switchedRemainder (N : ℕ) (B : ℝ) : ℝ :=
  ∑ d ∈ (switchedPrimorial N).divisors.filter (fun d : ℕ => (d : ℝ) < sieveLevel N B),
    |(#((BSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))).filter (d ∣ ·)) : ℝ)
      - (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) /
          (d.totient : ℝ)|

/-- LEAF: BJS p. 59 equation 191, the upper linear sieve applied to `B` at `y = N^{1/3}`,
level `D = sieveLevel N B`, mass `#T`, `g(d) = 1/φ(d)`, with a varying relative error
`O((log N)^{-1/3})`. Iwaniec 1980 Rosser sieve, or Halberstam and Richert Theorem 8.4
with an improved error; Theorem 11.1 alone has the weaker error
`(log log D)^{3/4} (log D)^{-1/4}`. Class HARD. -/
theorem leaf_switched_linear_sieve_upper (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
        ≤ (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) *
            sieveProduct N (1 / 3) *
            Fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 3)))
          + C * ((#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) *
              sieveProduct N (1 / 3)) / log N ^ ((1 : ℝ) / 3)
          + switchedRemainder N B := by
  sorry

/-- LEAF: BJS pp. 59 to 60 remainder calculation: for some level exponent `B`, the
switched remainder is at most `C N / (log N)^3`. Follows from the proved conditional
`remainder_bset_full_mass_of_levelBVTriples` with `A = 3`, since divisors of `P(y)`
below `D` are coprime to `N` and lie in `[1, ⌊D⌋]`, together with
`N^{7/8} (1 + log D)^2 ≤ N / (log N)^3` for large `N`. Class MEDIUM. -/
theorem leaf_switched_remainder (h : LevelBVTriples) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      switchedRemainder N B ≤ C * N / log N ^ 3 := by
  sorry

/-- A uniform positive lower bound for `U_N`. -/
theorem U_ge'' (N : ℕ) : 2 * exp (-eulerMascheroniConstant) * twinC ≤ U N := by
  unfold U
  have h1 := one_le_oddFactor N
  have h2 : 0 ≤ 2 * exp (-eulerMascheroniConstant) * twinC := by
    have := twinC_pos; positivity
  calc 2 * exp (-eulerMascheroniConstant) * twinC
      = 2 * exp (-eulerMascheroniConstant) * twinC * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2

/-- The parent `switched_sieve_application` with `switchedMain` unfolded, assembled from
the two leaves and the proved `Double243.triple_mass_upper`.
CONDITIONAL ON LevelBVTriples and the open leaves above. -/
theorem switched_sieve_application_of_leaves (h : LevelBVTriples) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) *
            (sieveProduct N (1 / 3) *
              Fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 3))) / 2)
          + C * sieveError N := by
  obtain ⟨B, C2, hB, hC2, N2, h2⟩ := leaf_switched_remainder h
  obtain ⟨C1, hC1, N1, h1⟩ := leaf_switched_linear_sieve_upper B hB
  obtain ⟨Nt, ht⟩ := LeanLab.AlmostPrimeSums.Double243.triple_mass_upper 1 one_pos
  set cb := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β)) with hcb
  set K : ℝ := 1 / (2 * exp eulerMascheroniConstant * (1 / 3)) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hratio := (idealMass_ratio (1 / 3) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show 1 / (2 * exp eulerMascheroniConstant * (1 / 3)) < K by rw [hK]; linarith))
  obtain ⟨N5, h5⟩ := eventually_atTop.mp hratio
  set c0 : ℝ := 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC)
    with hc0
  have hc0pos : 0 < c0 := by have := twinC_pos; rw [hc0]; positivity
  have hcbp : 0 < |cb| + 1 := by positivity
  refine ⟨B, C1 * (|cb| + 1) * K + C2 / c0, hB, by positivity,
    max (max (max N1 N2) (max Nt N5)) 3, fun N hEven hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hNt, hN5⟩, hN7⟩ := hN
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN7
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hLpos : 0 < log (N : ℝ) := by linarith
  set L := log (N : ℝ) with hL
  set P := sieveProduct N (1 / 3)
  set T : ℝ := (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
  set F := Fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 3)))
  have hP : 0 < P := sieveProduct_pos _ _
  have hM : 0 < Mchen N := Mchen_pos N (by omega)
  have hA := h1 N hEven hN1
  have hR := h2 N hN2
  have hT : T ≤ (|cb| + 1) * (N / L) := by
    have := ht N hNt
    have hle : cb + 1 ≤ |cb| + 1 := by linarith [le_abs_self cb]
    calc T ≤ (cb + 1) * (N / L) := this
      _ ≤ (|cb| + 1) * (N / L) := mul_le_mul_of_nonneg_right hle (by positivity)
  have hI := h5 N hN5
  have hI' : idealMass N (1 / 3) ≤ K * Mchen N := by
    have := (div_lt_iff₀ hM).mp hI; linarith
  have hidl : idealMass N (1 / 3) = N / L * P := rfl
  have hL14 : 0 < L ^ ((1 : ℝ) / 4) := rpow_pos_of_pos hLpos _
  have hL13 : 0 < L ^ ((1 : ℝ) / 3) := rpow_pos_of_pos hLpos _
  have h1413 : L ^ ((1 : ℝ) / 4) ≤ L ^ ((1 : ℝ) / 3) :=
    rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h14L : L ^ ((1 : ℝ) / 4) ≤ L := by
    calc L ^ ((1 : ℝ) / 4) ≤ L ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := rpow_one L
  have hSE : sieveError N = Mchen N / L ^ ((1 : ℝ) / 4) := rfl
  have hSEpos : 0 ≤ sieveError N := by rw [hSE]; positivity
  have hE1 : C1 * (T * P) / L ^ ((1 : ℝ) / 3) ≤ C1 * (|cb| + 1) * K * sieveError N := by
    have hTP : T * P ≤ (|cb| + 1) * K * Mchen N := by
      calc T * P ≤ (|cb| + 1) * (N / L) * P := mul_le_mul_of_nonneg_right hT hP.le
        _ = (|cb| + 1) * idealMass N (1 / 3) := by rw [hidl]; ring
        _ ≤ (|cb| + 1) * (K * Mchen N) := mul_le_mul_of_nonneg_left hI' hcbp.le
        _ = (|cb| + 1) * K * Mchen N := by ring
    calc C1 * (T * P) / L ^ ((1 : ℝ) / 3) ≤ C1 * ((|cb| + 1) * K * Mchen N) / L ^ ((1 : ℝ) / 4) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hTP hC1.le) hL14 h1413
      _ = C1 * (|cb| + 1) * K * sieveError N := by rw [hSE]; ring
  have hE2 : switchedRemainder N B ≤ C2 / c0 * sieveError N := by
    have hU := U_ge'' N
    have hMc : c0 * N / L ^ 2 ≤ Mchen N := by
      simp only [Mchen, hc0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ (N : ℝ) := hNpos.le
      calc 2 * exp eulerMascheroniConstant * (2 * exp (-eulerMascheroniConstant) * twinC) * N
          = 2 * exp eulerMascheroniConstant * ((2 * exp (-eulerMascheroniConstant) * twinC) * N)
            := by ring
        _ ≤ 2 * exp eulerMascheroniConstant * (U N * N) := by gcongr
        _ = _ := by ring
    calc switchedRemainder N B ≤ C2 * N / L ^ 3 := hR
      _ ≤ C2 * N / (L ^ 2 * L ^ ((1 : ℝ) / 4)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [pow_succ]; exact mul_le_mul_of_nonneg_left h14L (by positivity)
      _ = C2 / c0 * ((c0 * N / L ^ 2) / L ^ ((1 : ℝ) / 4)) := by
          field_simp
      _ ≤ C2 / c0 * (Mchen N / L ^ ((1 : ℝ) / 4)) := by
          gcongr
      _ = C2 / c0 * sieveError N := by rw [hSE]
  have hmain : T * P * F = 2 * (T * (P * F / 2)) := by ring
  have hpos2 : 0 ≤ C2 / c0 * sieveError N := by positivity
  have hpos1 : 0 ≤ C1 * (|cb| + 1) * K * sieveError N := by positivity
  have hfin : (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ)
      ≤ 2 * (T * (P * F / 2) + (C1 * (|cb| + 1) * K + C2 / c0) * sieveError N) := by
    nlinarith only [hA, hmain, hE1, hE2, hpos1, hpos2]
  linarith

end

#print axioms switched_sieve_application_of_leaves
#print axioms U_ge''

end LeanLab.AlmostPrimeSums.Decomp243cFeed1122Switched
