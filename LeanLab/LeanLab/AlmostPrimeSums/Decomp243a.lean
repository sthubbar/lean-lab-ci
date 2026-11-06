import LeanLab.AlmostPrimeSums.Decomp1527c

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Supply decomposition of SA_lower. The original file stays sealed.
The finite sieve application is separated from its normalized main term.
Source: BJS https://arxiv.org/abs/2207.09452 pp. 43 to 44 equations 141 to 145.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243a

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c

noncomputable section

/-- The twin sieve product at cutoff N to the power theta.
BJS p. 37 equation 116 and p. 38 equation 119. -/
def sieveProduct (N : ℕ) (θ : ℝ) : ℝ :=
  ∏ p ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
    (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N), (1 - 1 / ((p : ℝ) - 1))

/-- The ideal prime mass times the twin sieve product.
Derived main term for BJS p. 43 equation 142. -/
def idealMass (N : ℕ) (θ : ℝ) : ℝ :=
  (N : ℝ) / log N * sieveProduct N θ

/-- The logarithmically reduced square root distribution level.
BJS p. 43 equation 141 with the LevelBV logarithmic level. -/
def sieveLevel (N : ℕ) (B : ℝ) : ℝ := √(N : ℝ) / log N ^ B

/-- The lower linear sieve main term before evaluating its limiting coefficient.
Derived from BJS p. 43 equation 142. -/
def lowerMain (N : ℕ) (B : ℝ) : ℝ :=
  idealMass N (1 / 8) * fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 8)))

/-- A relative error envelope tending to zero on the Chen main scale.
Derived qualitative envelope for the remainders in BJS pp. 43 to 44 equations 142 to 145. -/
def sieveError (N : ℕ) : ℝ := Mchen N / log N ^ ((1 : ℝ) / 4)

/-- The sieve product is positive at every natural N.
Derived finite product fact for BJS p. 37 equation 116. -/
theorem sieveProduct_pos (N : ℕ) (θ : ℝ) : 0 < sieveProduct N θ := by
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.2.1
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))

/-- The ideal mass divided by Mchen tends to the reciprocal of two exp gamma theta.
This evaluates only the product factor in BJS p. 43 equation 142. -/
theorem idealMass_ratio (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    Tendsto (fun N : ℕ => idealMass N θ / Mchen N) atTop
      (𝓝 (1 / (2 * exp eulerMascheroniConstant * θ))) := by
  have h := (mertens_twin θ hθ hθ1).div_const (2 * exp eulerMascheroniConstant * θ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hU : U N ≠ 0 := (U_pos N).ne'
  have he : exp eulerMascheroniConstant ≠ 0 := (exp_pos _).ne'
  dsimp [idealMass, sieveProduct, Mchen]
  rw [log_rpow hNp]
  field_simp [hL, hNp.ne', hU, he, hθ.ne']

/-- The lower main term has limiting coefficient two log three.
Derived evaluation of BJS p. 43 equation 142 at s tending to four. -/
theorem lowerMain_ratio (B : ℝ) :
    Tendsto (fun N : ℕ => lowerMain N B / Mchen N) atTop (𝓝 (2 * log 3)) := by
  have h := (idealMass_ratio (1 / 8) (by norm_num) (by norm_num)).mul
    (chen_lower_sieve_coefficient_tendsto B)
  have hv : 1 / (2 * exp eulerMascheroniConstant * (1 / 8)) *
      (exp eulerMascheroniConstant * log 3 / 2) = 2 * log 3 := by
    field_simp
    ring
  rw [hv] at h
  simpa only [lowerMain, sieveLevel, div_mul_eq_mul_div] using h

/-- The chosen sieve error is negligible relative to Mchen.
Derived error absorption for BJS pp. 43 to 44 equations 142 to 145. -/
theorem sieveError_ratio :
    Tendsto (fun N : ℕ => sieveError N / Mchen N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hM := (Mchen_pos N hN).ne'
  have hL : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  simp only [Function.comp_apply, sieveError, rpow_neg hL, div_div, mul_comm (log (N : ℝ) ^ ((1 : ℝ) / 4))]
  field_simp

/-- A main term limit and a negligible error give an eventual lower bound.
Derived limit argument used after BJS p. 44 equation 145. -/
theorem lower_from_limits (a e m v : ℕ → ℝ) (c C : ℝ)
    (hm : ∀ᶠ N in atTop, 0 < m N)
    (ha : Tendsto (fun N => a N / m N) atTop (𝓝 c))
    (he : Tendsto (fun N => e N / m N) atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, Even N → a N - C * e N ≤ v N) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (c - η) * m N ≤ v N := by
  intro η hη
  have hlim : Tendsto (fun N => (a N - C * e N) / m N) atTop (𝓝 c) := by
    have hh := ha.sub (he.const_mul C)
    simpa only [mul_zero, sub_zero, sub_div, mul_div_assoc] using hh
  have hbound := hlim.eventually (lt_mem_nhds (sub_lt_self c hη))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hm.and (hbound.and hv))
  refine ⟨N₀, fun N hEven hN => ?_⟩
  obtain ⟨hmN, hlt, hvN⟩ := hN₀ N hN
  exact ((le_div_iff₀ hmN).mp hlt.le).trans (hvN hEven)

/-- LEAF. Finite lower sieve application with an unevaluated main term.
For the prime sequence and its LevelBV input, some fixed logarithmic level
and constant bound SA below by lowerMain minus C times sieveError.
BJS p. 43 equation 142 and p. 44 equation 145, using the varying error
linear sieve of Halberstam and Richert Theorem 11.1.
This is the sieve application only. It does not evaluate lowerMain or
state the coefficient two log three. -/
theorem lower_sieve_application (h : LevelBV) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ,
      Even N → N₀ ≤ N → lowerMain N B - C * sieveError N ≤
        SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  sorry

/-- Exact supply for the sealed SA_lower statement, from the smaller sieve
application and the independently evaluated main term and error limits.
CONDITIONAL ON LevelBV and the open lower_sieve_application leaf. -/
theorem SA_lower (h : LevelBV) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (2 * log 3 - η) * Mchen N ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  obtain ⟨B, C, _, _, N₀, hN₀⟩ := lower_sieve_application h
  apply lower_from_limits (lowerMain · B) sieveError Mchen
    (fun N => (SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ)) (2 * log 3) C
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact Mchen_pos N hN
  · exact lowerMain_ratio B
  · exact sieveError_ratio
  · filter_upwards [eventually_ge_atTop N₀] with N hN hEven
    exact hN₀ N hEven hN

end
end LeanLab.AlmostPrimeSums.Decomp243a
