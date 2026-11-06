import LeanLab.AlmostPrimeSums.Decomp243b
import LeanLab.AlmostPrimeSums.Double243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Supply decomposition of SB_upper. The original file stays sealed.
The unsifted triple mass is proved in Double243. The upper sieve application
is the remaining input.
BJS https://arxiv.org/abs/2207.09452 pp. 56 to 60, Lemma 52 and equation 191.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243c

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243b

noncomputable section

/-- The switched upper sieve multiplier at cutoff N to the power one third.
BJS p. 59 equation 191, before replacing the triple cardinality. -/
def switchedMultiplier (N : ℕ) (B : ℝ) : ℝ :=
  sieveProduct N (1 / 3) *
    Fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 3))) / 2

/-- The switched main term before bounding the unsifted triple mass.
BJS p. 59 equation 191 summed over the switching pieces. -/
def switchedMain (N : ℕ) (B : ℝ) : ℝ :=
  (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) *
    switchedMultiplier N B

/-- The ideal switched multiplier has normalized limit one.
Derived evaluation of BJS p. 59 equation 191 at s tending to three halves. -/
theorem switchedMultiplier_ratio (B : ℝ) :
    Tendsto (fun N : ℕ => ((N : ℝ) / log N * switchedMultiplier N B) / Mchen N)
      atTop (𝓝 1) := by
  have h := ((idealMass_ratio (1 / 3) (by norm_num) (by norm_num)).mul
    (chen_switched_sieve_coefficient_tendsto B)).div_const 2
  have hv : 1 / (2 * exp eulerMascheroniConstant * (1 / 3)) *
      (4 * exp eulerMascheroniConstant / 3) / 2 = 1 := by
    field_simp
    ring
  rw [hv] at h
  apply h.congr'
  filter_upwards with N
  dsimp [idealMass, switchedMultiplier, sieveLevel]
  ring

/-- The switched multiplier is eventually positive.
Derived sign check needed when inserting Lemma 52 into BJS p. 59 equation 191. -/
theorem switchedMultiplier_eventually_pos (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < switchedMultiplier N B := by
  have hpos := (switchedMultiplier_ratio B).eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hpos, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hm := Mchen_pos N hN2
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := (div_pos_iff_of_pos_right hm).mp hN
  exact (mul_pos_iff_of_pos_left (div_pos hNp hL)).mp hp

/-- LEAF. The unsifted triple count has the upper mass coefficient cbar.
For every positive epsilon it is eventually at most cbar plus epsilon times
N divided by log N. BJS pp. 57 to 58, Lemma 52 and equations 186 to 189.
This statement contains no sifted B count and no distribution input. -/
theorem triple_mass_upper :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + ε) *
          ((N : ℝ) / log N) := by
  exact LeanLab.AlmostPrimeSums.Double243.triple_mass_upper

/-- LEAF. Upper sieve application to the switched set before its mass estimate.
LevelBVTriples gives a fixed logarithmic level and a vanishing relative error.
BJS p. 59 equation 191 and pp. 59 to 60 remainder calculation, with the
coprimality correction in remainder_bset_full_mass_of_levelBVTriples.
This statement retains the actual triple cardinality and does not replace
it by the cbar coefficient. -/
theorem switched_sieve_application (h : LevelBVTriples) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ switchedMain N B + C * sieveError N := by
  sorry

/-- Exact supply for the sealed SB_upper statement.
CONDITIONAL ON LevelBVTriples and the open switched_sieve_application leaf. -/
theorem SB_upper (h : LevelBVTriples) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * Mchen N := by
  intro η hη
  let cb := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))
  obtain ⟨B, C, _, _, Ns, hs⟩ := switched_sieve_application h
  obtain ⟨Nt, ht⟩ := triple_mass_upper (η / 2) (by positivity)
  let envelope : ℕ → ℝ := fun N => (cb + η / 2) * ((N : ℝ) / log N * switchedMultiplier N B)
  have he : Tendsto (fun N => envelope N / Mchen N) atTop (𝓝 (cb + η / 2)) := by
    have hh := (switchedMultiplier_ratio B).const_mul (cb + η / 2)
    simpa only [envelope, mul_div_assoc, mul_one] using hh
  have hv : ∀ᶠ N : ℕ in atTop, Even N →
      (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
        ≤ envelope N + C * sieveError N := by
    filter_upwards [eventually_ge_atTop Ns, eventually_ge_atTop Nt,
      switchedMultiplier_eventually_pos B] with N hNs hNt hpos hEven
    have hm := mul_le_mul_of_nonneg_right (ht N hNt) hpos.le
    have hmain : switchedMain N B ≤ envelope N := by
      dsimp [switchedMain, envelope, cb] at *
      nlinarith only [hm]
    exact (hs N hEven hNs).trans (by linarith [hmain])
  obtain ⟨N₀, hN₀⟩ := upper_from_limits envelope sieveError Mchen
    (fun N => (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2)
    (cb + η / 2) C
    (by filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN; exact Mchen_pos N hN)
    he sieveError_ratio hv (η / 2) (by positivity)
  refine ⟨N₀, fun N hEven hN => ?_⟩
  have hh := hN₀ N hEven hN
  convert hh using 1 <;> dsimp [cb] <;> ring

end
end LeanLab.AlmostPrimeSums.Decomp243c
