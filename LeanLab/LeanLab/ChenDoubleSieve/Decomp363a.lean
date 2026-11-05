import LeanLab.ChenDoubleSieve.Decomp348o

/-!
Elementary error absorption for Wu 2004 page 38 before equation 10.2.
The exact ordinary odd prime product input was already proved in task348.
Source: https://arxiv.org/pdf/0705.1652, pages 6 and 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348

/-- The exact sealed density target is supplied by the existing clean proof. -/
theorem scaledDensity_supplied :
    Tendsto scaledDensity evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) :=
  Task348.scaledDensity_supplied

/-- The local density scale divided by the exact normalizer is scaledDensity. -/
theorem density_scale_ratio {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) / log N * lowerDensity N) / Θ N = scaledDensity N := by
  simpa only [main0, mul_one] using (main0_ratio (fun _ => 1) 1 hN)

/-- The local density scale is uniformly bounded by the actual normalizer
on the even tail. No raw sieve estimate is used. -/
theorem density_scale_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (N : ℝ) / log N * lowerDensity N ≤ K * Θ N := by
  let c : ℝ := 2 / (kappa1 * exp eulerMascheroniConstant)
  have hc : 0 < c := by dsimp [c, kappa1]; positivity
  have he : ∀ᶠ N in evenAtTop, scaledDensity N < c + 1 :=
    scaledDensity_supplied.eventually (eventually_lt_nhds (by dsimp [c]; linarith))
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨c + 1, by linarith, max 2 M, ?_⟩
  intro N hEven hN
  have ht : 0 < Θ N := Θ_pos (by omega)
  have hb : scaledDensity N ≤ c + 1 := (hM N (by omega) hEven).le
  rw [← density_scale_ratio (by omega : 2 ≤ N)] at hb
  exact (div_le_iff₀ ht).1 hb

/-- Every fixed multiple of N over log cubed is absorbed by an arbitrary
positive multiple of the exact normalizer. Source: page 38 remainder display. -/
theorem log_cubic_absorbed (C η : ℝ) (_hC : 0 ≤ C) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * (N : ℝ) / log N ^ 3 ≤ η * Θ N := by
  have hlogtop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (hlogtop.eventually_ge_atTop (C / (η * LeanLab.ChenExplicit.twinC)))
  refine ⟨max 2 M, ?_⟩
  intro N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcpos := LeanLab.ChenExplicit.twinC_pos
  have hsmall : C / log (N : ℝ) ≤ η * LeanLab.ChenExplicit.twinC := by
    apply (div_le_iff₀ hlog).2
    have hb := (div_le_iff₀ (mul_pos hη hcpos)).1 (hM N (by omega))
    nlinarith
  have hcn : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN
    nlinarith [oddFactor_one_le N]
  calc
    C * (N : ℝ) / log N ^ 3 = (C / log N) * (N / log N ^ 2) := by ring
    _ ≤ (η * LeanLab.ChenExplicit.twinC) * (N / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ (η * CN N) * (N / log N ^ 2) := by gcongr
    _ = η * Θ N := by unfold Θ; ring

end LeanLab.ChenDoubleSieve.Task363
