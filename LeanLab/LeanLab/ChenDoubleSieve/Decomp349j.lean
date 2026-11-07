import LeanLab.ChenDoubleSieve.Decomp349i

/-!
Uniform variable density normalization for Wu 2004 page 39 equation 10.3.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- Uniform Mertens normalization for all sifting cutoffs above the lower prime band. -/
theorem variableDensity_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → ∀ z : ℝ,
      (N : ℝ) ^ kappa1 ≤ z →
      |log z * Task363.localDensity N z / CN N -
        2 / exp eulerMascheroniConstant| ≤ ε := by
  let c : ℝ := 2 / exp eulerMascheroniConstant
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Z, hZ⟩ := Metric.tendsto_atTop.1 ordinaryDensity_tendsto (ε / 2) (by positivity)
  have htail : ∀ᶠ N : ℕ in atTop, |tailCorrection N - 1| < ε / (2 * c) := by
    have ht := tailCorrection_tendsto.eventually (Metric.ball_mem_nhds (1 : ℝ) (by positivity : 0 < ε / (2 * c)))
    simpa only [Metric.mem_ball, Real.dist_eq] using ht
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ hEven : Even N, ∀ z : ℝ,
      (N : ℝ) ^ kappa1 ≤ z →
      |log z * Task363.localDensity N z / CN N - c| ≤ ε := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hpow.eventually_ge_atTop Z, htail]
      with N hN hNZ hNt
    intro hEven z hz
    have ha : |log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC - c| < ε / 2 := by
      simpa only [Real.dist_eq] using hZ z (hNZ.trans hz)
    let x := log z * Task363.localDensity N z / CN N
    let t := variableTail N z
    have ht1 : 1 ≤ t := variableTail_one_le N z
    have htbound : t ≤ tailCorrection N := variableTail_le hz
    have htdiff : 0 ≤ t - 1 := by linarith
    have htdiff' : t - 1 < ε / (2 * c) := by
      have habs : tailCorrection N - 1 ≤ |tailCorrection N - 1| := le_abs_self _
      linarith
    have hprod : x * t = log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC :=
      variableDensity_normalization hN hEven z
    have habs : |x - c| ≤ |x * t - c| + c * (t - 1) := by
      calc
        |x - c| ≤ |x - c| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
        _ = |(x - c) * t| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ t)]
        _ = |(x * t - c) - c * (t - 1)| := by congr 1; ring
        _ ≤ |x * t - c| + |c * (t - 1)| := abs_sub _ _
        _ = |x * t - c| + c * (t - 1) := by rw [abs_of_nonneg (mul_nonneg hc.le htdiff)]
    rw [hprod] at habs
    have hsmall : c * (t - 1) < ε / 2 := by
      have hh := mul_lt_mul_of_pos_left htdiff' hc
      have hid : c * (ε / (2 * c)) = ε / 2 := by field_simp
      rw [hid] at hh
      exact hh
    change |x - c| ≤ ε
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  exact ⟨M, fun N hEven hN z hz => hM N hN hEven z hz⟩

/-- Every even modulus cutoff sequence above the lower endpoint has the same normalization. -/
theorem variableDensity_sequence (z : ℕ → ℝ)
    (hz : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ kappa1 ≤ z N) :
    Tendsto (fun N : ℕ => log (z N) * Task363.localDensity N (z N) / CN N)
      evenAtTop (𝓝 (2 / exp eulerMascheroniConstant)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨M, hM⟩ := variableDensity_uniform (ε / 2) (by positivity)
  change ∀ᶠ N in atTop ⊓ principal {N : ℕ | Even N}, _
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop M, hz] with N hN hzN hEven
  rw [Real.dist_eq]
  exact (hM N hEven hN (z N) hzN).trans_lt (by linarith)

end LeanLab.ChenDoubleSieve.Task349
