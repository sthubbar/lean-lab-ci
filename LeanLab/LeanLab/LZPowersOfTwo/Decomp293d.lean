/-
P0079 existential thresholds beyond the endpoint issue.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293c

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4 after display 13. A quantitative bound for the fixed box
forces infinitely many solutions. This uses no cited analytic input. -/
theorem infinite_of_NX_lower293 {s : ℕ} {l1 l2 γ η ε : ℝ} {μ : Fin s → ℝ}
    (h : ∃ c X0 : ℝ, 0 < c ∧ ∀ X, X0 ≤ X →
      c * X * (log X) ^ (s - 2) ≤ NX l1 l2 μ γ η ε X) :
    (Sol l1 l2 μ γ η).Infinite := by
  obtain ⟨c, X0, hc, H⟩ := h
  intro hfin
  set S := Sol l1 l2 μ γ η
  set X := max (max X0 3) ((S.ncard + 1) / c)
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans (le_max_left _ _)
  have hlog : 1 ≤ log X := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
  have hpow : 1 ≤ (log X) ^ (s - 2) := one_le_pow₀ hlog
  have hcX : (S.ncard : ℝ) + 1 ≤ c * X := by
    have hX : (S.ncard + 1) / c ≤ X := le_max_right _ _
    rwa [div_le_iff₀ hc, mul_comm] at hX
  have hbig : c * X ≤ c * X * (log X) ^ (s - 2) := by
    have hnonneg : 0 ≤ c * X := by positivity
    nlinarith
  have hN := H X ((le_max_left _ _).trans (le_max_left _ _))
  have hsub : NX l1 l2 μ γ η ε X ≤ S.ncard :=
    Set.ncard_le_ncard (fun x hx => hx.1) hfin
  have hsub' : (NX l1 l2 μ γ η ε X : ℝ) ≤ S.ncard := by exact_mod_cast hsub
  linarith

/-- P0079 page 12, Section 8, with an existential large s threshold.
CONDITIONAL ON the four shared analytic leaves. This avoids the printed
endpoint formula and uses the absolute lattice bounds from Lemma 4. -/
theorem normalized_large_s293 (ν l1 l2 : ℝ) (μ : ℕ → ℝ)
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
  exact infinite_of_NX_lower293 (density_at_margin293 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc
    hμ r1 r2 hr1 hr2 hη hη1 hη2 hε hε' hmass hgap)

end LeanLab.LZPowersOfTwo
