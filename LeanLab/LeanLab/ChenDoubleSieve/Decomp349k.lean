import LeanLab.ChenDoubleSieve.Decomp349j

/-!
Variable sifting level preparation for Wu 2004 page 39 equation 10.3.
Source: https://arxiv.org/pdf/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The residual logarithmic level when the prime itself is the sifting cutoff. -/
def variableLevel (B : ℝ) (N p : ℕ) : ℝ :=
  log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) / log p

/-- The fixed and variable levels differ only by the ratio of their logarithms. -/
theorem variableLevel_relation (B : ℝ) {N p : ℕ} (hN : 2 ≤ N) :
    variableLevel B N p = lowerLevel B N p * (kappa1 * log N / log p) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  unfold variableLevel lowerLevel
  rw [log_rpow hNpos]
  field_simp [hlog, show kappa1 ≠ 0 by norm_num [kappa1]]

/-- The loss free variable level is the exact rational function of the prime coordinate. -/
theorem variableLevel_zero {N p : ℕ} (hN : 2 ≤ N) (hp : p.Prime) :
    variableLevel 0 N p = 1 / (2 * (log (p : ℝ) / log N)) - 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogN : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
  unfold variableLevel
  rw [rpow_zero, div_one, log_div (rpow_pos_of_pos hNpos _).ne' hp0.ne', log_rpow hNpos]
  field_simp
  <;> ring

/-- The loss free variable level stays between three and five on the full band. -/
theorem variableLevel_zero_range {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ Task366.primeBand4 N) : variableLevel 0 N p ∈ Icc (3 : ℝ) 5 := by
  have hm := hp
  simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter] at hm
  rw [variableLevel_zero hN hm.1.2.1]
  have ht := primeBand4_coordinates hN hp
  have htpos : 0 < log (p : ℝ) / log N := by
    have hk : 0 < kappa1 := by norm_num [kappa1]
    linarith [ht.1]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    norm_num [kappa2] at ht
    linarith [ht.2]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    norm_num [kappa1] at ht
    linarith [ht.1]

/-- On the actual band the variable level loss is no larger than the fixed level loss. -/
theorem variableLevel_shift_le (B : ℝ) {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ Task366.primeBand4 N) :
    |variableLevel B N p - variableLevel 0 N p| ≤ |lowerLevel B N 1 - 6| := by
  have hm := hp
  simp only [Task366.primeBand4, lowerPrimeBand, Finset.mem_filter] at hm
  have hprime := hm.1.2.1
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hprime.one_lt)
  have ht := primeBand4_coordinates hN hp
  have hratio : 0 ≤ kappa1 * log N / log p ∧ kappa1 * log N / log p ≤ 1 := by
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num [kappa1]) hlogN.le) hlogp.le
    · rw [div_le_one hlogp]
      exact (le_div_iff₀ hlogN).1 ht.1
  rw [variableLevel_relation B hN, variableLevel_relation 0 hN, ← sub_mul,
    abs_mul, abs_of_nonneg hratio.1, Task367.lowerLevel_shift B hN hprime.one_lt.le]
  exact mul_le_of_le_one_right (abs_nonneg _) hratio.2

/-- The logarithmic sieve loss can be removed uniformly at the variable sifting level.
CONDITIONAL ON IsLinearSieve only. -/
theorem variable_values_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (ε : ℝ) (hε : 0 < ε) : ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → ∀ p ∈ Task366.primeBand4 N,
      |F (variableLevel B N p) - F (variableLevel 0 N p)| ≤ ε := by
  have hc : ContinuousOn F (Icc (2 : ℝ) 6) := h.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  have hnear : ∀ᶠ N : ℕ in atTop, |lowerLevel B N 1 - 6| < min 1 δ := by
    have ht := ((lowerLevel_one_tendsto B).sub_const 6).abs
    have he : Tendsto (fun N : ℕ => |lowerLevel B N 1 - 6|) atTop (𝓝 0) := by simpa using ht
    exact he.eventually (eventually_lt_nhds (lt_min (by norm_num) hδ))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hnear
  refine ⟨max 2 M, ?_⟩
  intro N hN p hp
  have hN2 : 2 ≤ N := by omega
  have hr := variableLevel_zero_range hN2 hp
  have hd := (variableLevel_shift_le B hN2 hp).trans_lt (hM N (by omega))
  have habs : |variableLevel B N p - variableLevel 0 N p| < 1 := hd.trans_le (min_le_left _ _)
  have hdiff := abs_lt.mp habs
  have hvar : variableLevel B N p ∈ Icc (2 : ℝ) 6 := by
    constructor <;> linarith [hr.1, hr.2, hdiff.1, hdiff.2]
  have hzero : variableLevel 0 N p ∈ Icc (2 : ℝ) 6 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  simpa only [Real.dist_eq] using
    (hcont _ hvar _ hzero (by simpa only [Real.dist_eq] using hd.trans_le (min_le_right _ _))).le

end LeanLab.ChenDoubleSieve.Task349
