import LeanLab.ChenDoubleSieve.Decomp349l

/-!
The actual first ordinary main term limit before inverse substitution.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The actual normalized first main term approaches its exact continuous weighted average.
CONDITIONAL ON IsLinearSieve only. -/
theorem basicMain_variable_approx (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      |basicMain F B N 1 / Θ N - weightedCoprimeTotientPrimeSum (variableKernel F) N| ≤ ε := by
  obtain ⟨K, hK, J, hJ⟩ := variable_mass_bounded
  obtain ⟨M, hM, L, hL⟩ := variable_values_bounded F f h B
  let c : ℝ := 2 / exp eulerMascheroniConstant
  have hc : 0 < c := by dsimp [c]; positivity
  let η : ℝ := ε * kappa1 / (K * (M + c))
  have hk : 0 < kappa1 := by norm_num [kappa1]
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D, hD⟩ := variableDensity_uniform η hη
  obtain ⟨S, hS⟩ := variable_values_shift_small F f h B η hη
  refine ⟨max 2 (max J (max L (max D S))), ?_⟩
  intro N hEven hN
  have hN2 : 2 ≤ N := by omega
  have hmodel : weightedCoprimeTotientPrimeSum (variableKernel F) N =
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        c * F (variableLevel 0 N p) / (log (p : ℝ) / log N) / ((p : ℝ) - 1) := by
    unfold weightedCoprimeTotientPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    rw [variableLevel_zero hN2 (Wu41.mem_PS.mp hp).1]
    rfl
  rw [basicMain_variable_ratio F B hN2, hmodel, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
      |(log (p : ℝ) * Task363.localDensity N p / CN N /
          (log (p : ℝ) / log N)) * F (variableLevel B N p) / ((p : ℝ) - 1) -
        c * F (variableLevel 0 N p) / (log (p : ℝ) / log N) / ((p : ℝ) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (η * (M + c) / kappa1) * (1 / ((p : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Wu41.mem_PS.mp hp
      have hpfull : p ∈ Task366.primeBand4 N := by
        rw [upperBand_eq_filter hN2] at hp
        exact (Finset.mem_filter.mp hp).1
      let A : ℝ := log (p : ℝ) * Task363.localDensity N p / CN N
      let t : ℝ := log (p : ℝ) / log N
      have ht : kappa1 ≤ t := (primeBand4_coordinates hN2 hpfull).1
      have htpos : 0 < t := hk.trans_le ht
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hm.1.two_le
      have hA : |A - c| ≤ η := hD N hEven (by omega) p hm.2.1
      have hFB : |F (variableLevel B N p)| ≤ M := hL N (by omega) p hpfull
      have hshift : |F (variableLevel B N p) - F (variableLevel 0 N p)| ≤ η :=
        hS N (by omega) p hpfull
      have hnum : |A * F (variableLevel B N p) - c * F (variableLevel 0 N p)| ≤ η * (M + c) := by
        calc
          _ = |(A - c) * F (variableLevel B N p) +
              c * (F (variableLevel B N p) - F (variableLevel 0 N p))| := by congr 1; ring
          _ ≤ |(A - c) * F (variableLevel B N p)| +
              |c * (F (variableLevel B N p) - F (variableLevel 0 N p))| := abs_add_le _ _
          _ = |A - c| * |F (variableLevel B N p)| +
              c * |F (variableLevel B N p) - F (variableLevel 0 N p)| := by
                rw [abs_mul, abs_mul, abs_of_pos hc]
          _ ≤ η * M + c * η := add_le_add
            (mul_le_mul hA hFB (abs_nonneg _) hη.le)
            (mul_le_mul_of_nonneg_left hshift hc.le)
          _ = _ := by ring
      have heq : (A / t) * F (variableLevel B N p) / ((p : ℝ) - 1) -
          c * F (variableLevel 0 N p) / t / ((p : ℝ) - 1) =
          ((A * F (variableLevel B N p) - c * F (variableLevel 0 N p)) / t) /
            ((p : ℝ) - 1) := by ring
      change |(A / t) * F (variableLevel B N p) / ((p : ℝ) - 1) -
          c * F (variableLevel 0 N p) / t / ((p : ℝ) - 1)| ≤ _
      rw [heq, abs_div, abs_div, abs_of_pos htpos,
        abs_of_pos (by linarith : 0 < (p : ℝ) - 1)]
      calc
        _ ≤ (η * (M + c) / t) / ((p : ℝ) - 1) :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum htpos.le) (by linarith)
        _ ≤ (η * (M + c) / kappa1) / ((p : ℝ) - 1) :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hk ht) (by linarith)
        _ = _ := by ring
    _ = (η * (M + c) / kappa1) *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2), 1 / ((p : ℝ) - 1) := by
      rw [Finset.mul_sum]
    _ ≤ (η * (M + c) / kappa1) * K :=
      mul_le_mul_of_nonneg_left (hJ N (by omega)) (by positivity)
    _ = ε := by dsimp [η]; field_simp

/-- The exact first ordinary finite main term has its logarithmic coordinate integral limit.
CONDITIONAL ON IsLinearSieve only. The final inverse substitution is separate. -/
theorem basicMain_variable_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N : ℕ => basicMain F B N 1 / Θ N) evenAtTop
      (𝓝 (∫ t in kappa1..kappa2, variableKernel F t / t)) := by
  have hdiff : Tendsto (fun N : ℕ => basicMain F B N 1 / Θ N -
      weightedCoprimeTotientPrimeSum (variableKernel F) N) evenAtTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨M, hM⟩ := basicMain_variable_approx F f h B (ε / 2) (by positivity)
    change ∀ᶠ N in atTop ⊓ principal {N : ℕ | Even N}, _
    rw [eventually_inf_principal]
    filter_upwards [eventually_ge_atTop M] with N hN hEven
    simpa only [Real.dist_eq, sub_zero] using
      (hM N hEven hN).trans_lt (by linarith : ε / 2 < ε)
  have hmodel := tendsto_inf_left (x₂ := principal {N : ℕ | Even N})
    (weightedCoprimeTotientPrimeSum_tendsto (variableKernel F) (variableKernel_continuous F f h))
  simpa only [Pi.add_def, sub_add_cancel, zero_add] using hdiff.add hmodel

end LeanLab.ChenDoubleSieve.Task349
