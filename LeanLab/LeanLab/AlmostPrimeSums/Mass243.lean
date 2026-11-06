import LeanLab.AlmostPrimeSums.PrimeCount243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The remaining unsifted mass calculation is a double logarithmic prime kernel.
The finite counting and qualitative prime counting steps are proved separately.
BJS https://arxiv.org/abs/2207.09452 pp. 57 to 58 equations 186 to 189.
-/

namespace LeanLab.AlmostPrimeSums.Mass243

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Decomp1527c LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Triple243 LeanLab.AlmostPrimeSums.PrimeCount243

noncomputable section

/-- The double logarithmic prime kernel before its two Abel evaluations.
BJS p. 57 equation 186 and p. 58 equation 188, without enlargement. -/
def doubleKernel (N : ℕ) : ℝ :=
  ∑ p₁ ∈ middlePrimes N, (1 / (p₁ : ℝ)) *
    ∑ p₂ ∈ primesIco ((N : ℝ) ^ ((1 : ℝ) / 3)) (√((N : ℝ) / p₁)),
      1 / ((p₂ : ℝ) * log ((N : ℝ) / (p₁ * p₂)))

/-- The actual triple count is eventually bounded by the double logarithmic
prime kernel with every coefficient above one. This supplies the prime
counting step in BJS p. 57 equation 186 with no cited prime estimate. -/
theorem triple_count_le_double_kernel (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ) ≤
        (1 + ε) * N * doubleKernel N := by
  filter_upwards [primeCounting_triple_uniform ε hε] with N hπ
  refine (triple_count_le_prime_majorant N).trans ?_
  dsimp [primeTripleMajorant, doubleKernel]
  rw [mul_sum]
  apply sum_le_sum
  intro p₁ hp₁
  have hh := sum_le_sum (fun p₂ hp₂ => hπ p₁ hp₁ p₂ hp₂)
  simpa only [mul_sum, mul_assoc] using hh

/-- The normalized double kernel limit supplies the exact unsifted triple
mass leaf. CONDITIONAL ON that explicitly stated double kernel limit.
BJS pp. 57 to 58 equations 186 to 189. No distribution input is required. -/
theorem triple_mass_upper_of_kernel_limit
    (hkernel : Tendsto (fun N : ℕ => log N * doubleKernel N) atTop
      (𝓝 (∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))))) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + ε) *
          ((N : ℝ) / log N) := by
  intro ε hε
  let cb := ∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))
  have hcb : cb < 1 := by have hh := cbar_lt'; dsimp [cb]; linarith
  have hlim : Tendsto (fun N : ℕ => ((1 + ε) * N * doubleKernel N) /
      ((N : ℝ) / log N)) atTop (𝓝 ((1 + ε) * cb)) := by
    have hh := hkernel.const_mul (1 + ε)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
    <;> ring
  have hgap : (1 + ε) * cb < cb + ε := by nlinarith
  have hevent := hlim.eventually (gt_mem_nhds hgap)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((triple_count_le_double_kernel ε hε).and (hevent.and (eventually_ge_atTop (2 : ℕ))))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hcount, hupper, hN2⟩ := hN₀ N hN
  have hscale : 0 < (N : ℝ) / log N := div_pos
    (by exact_mod_cast (show 0 < N by omega))
    (log_pos (by exact_mod_cast (show 1 < N by omega)))
  exact hcount.trans ((div_le_iff₀ hscale).mp hupper.le)

end
end LeanLab.AlmostPrimeSums.Mass243
