/-
P0079 pages 3 to 5, existential thresholds with the smaller analytic inputs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountAssembly396
import LeanLab.LZPowersOfTwo.Decomp293d

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 pages 3 to 5, the strict-margin existential-threshold argument.
CONDITIONAL ON the four prime replacement and minor inputs in CountAssembly396.
This is the exact normalized_large_s293 statement and does not assert the printed s0 endpoint. -/
theorem normalized_large_s396 (ν l1 l2 : ℝ) (μ : ℕ → ℝ)
    (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|) :
    ∃ S0 : ℕ, ∀ s : ℕ, 2 ≤ s → S0 ≤ s → ∀ γ : ℝ,
      (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite := by
  have hν0 : 0 ≤ ν := by
    rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact nuTr_pos.le
    · exact nuAlg_pos.le
  have hν1 : ν < 1 := by
    rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact nuTr_lt_one
    · exact nuAlg_lt_one
  have hprod : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hν0 hν1).comp
    (tendsto_sub_atTop_nat 2)).mul_const (Cq r1.den r2.den)
  have Hpow : ∀ᶠ s : ℕ in atTop,
      ν ^ (s - 2) * Cq r1.den r2.den < η / (8 * |l1 * l2|) :=
    hlim.eventually (eventually_lt_nhds (by simpa using (div_pos hη
      (show 0 < 8 * |l1 * l2| by positivity))))
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp Hpow
  refine ⟨S0, fun s hs hS γ => ?_⟩
  let ε : ℝ := 1 / (16 * l1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε' : ε < 1 / (8 * l1) := by
    dsimp [ε]
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  have hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η -
      ν ^ (s - 2) * Cq r1.den r2.den := by
    have heq : (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η =
        3 * η / (8 * |l1 * l2|) := by
      dsimp [ε]
      field_simp
      ring
    rw [heq, show 3 * η / (8 * |l1 * l2|) = 3 * (η / (8 * |l1 * l2|)) by ring]
    have hb := hS0 s hS
    have hp : 0 < η / (8 * |l1 * l2|) := by positivity
    linarith
  have hmass : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  exact infinite_of_NX_lower293 (density_at_margin396 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc
    hμ r1 r2 hr1 hr2 hη hη1 hη2 hε hε' hmass hgap)


end LeanLab.LZPowersOfTwo
