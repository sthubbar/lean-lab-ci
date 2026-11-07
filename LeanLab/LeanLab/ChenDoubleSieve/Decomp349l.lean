import LeanLab.ChenDoubleSieve.Decomp349k

/-!
The first ordinary upper main term in prime logarithmic coordinates.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The exact continuous weight before the final inverse coordinate substitution. -/
def variableKernel (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2 / exp eulerMascheroniConstant) * F (1 / (2 * t) - 1) / t

/-- The variable sieve argument lies in a fixed positive interval on the exponent band. -/
theorem variable_argument_range {t : ℝ} (ht : t ∈ Icc kappa1 kappa2) :
    1 / (2 * t) - 1 ∈ Icc (3 : ℝ) 5 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num [kappa1]) ht.1
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    norm_num [kappa2] at ht
    linarith [ht.2]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    norm_num [kappa1] at ht
    linarith [ht.1]

/-- The variable upper sieve weight is continuous on the exact exponent band.
CONDITIONAL ON IsLinearSieve only. -/
theorem variableKernel_continuous (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ContinuousOn (variableKernel F) (Icc kappa1 kappa2) := by
  have htpos : ∀ t ∈ Icc kappa1 kappa2, 0 < t := by
    intro t ht
    exact lt_of_lt_of_le (by norm_num [kappa1]) ht.1
  have harg : ContinuousOn (fun t : ℝ => 1 / (2 * t) - 1) (Icc kappa1 kappa2) := by
    fun_prop (disch := intro t ht; have := htpos t ht; positivity)
  have hF : ContinuousOn (fun t : ℝ => F (1 / (2 * t) - 1)) (Icc kappa1 kappa2) :=
    h.1.comp harg (fun t ht => by
      have hr := variable_argument_range ht
      change 0 < 1 / (2 * t) - 1
      linarith [hr.1])
  exact (continuousOn_const.mul hF).div continuousOn_id (fun t ht => (htpos t ht).ne')

/-- The normalized first ordinary main term is an exact weighted finite average. -/
theorem basicMain_variable_ratio (F : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    basicMain F B N 1 / Θ N =
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        ((log (p : ℝ) * Task363.localDensity N p / CN N) /
          (log (p : ℝ) / log N)) * F (variableLevel B N p) / ((p : ℝ) - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  simp only [basicMain, basicEndpoint, basicSifting, ↓reduceIte]
  unfold Θ
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (Wu41.mem_PS.mp hp).1
  have hp0 : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hprime.one_lt)).ne'
  unfold variableLevel
  field_simp [(CN_pos N).ne', hn.ne', hl.ne', hp0]
  <;> ring

/-- The actual first prime band has a uniform positive reciprocal totient mass bound. -/
theorem variable_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N →
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        1 / ((p : ℝ) - 1)) ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := basic_fixed_mass_bounded
  refine ⟨K, hK, max 2 M, ?_⟩
  intro N hN
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (s :=
    Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2)) (t :=
    Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint 2)) ?_ ?_)
    (hM N (by omega) 2 (by simp))
  · intro p hp
    have hm := Wu41.mem_PS.mp hp
    apply Wu41.mem_PS.mpr
    refine ⟨hm.1, hm.2.1, hm.2.2.1.trans_le ?_, hm.2.2.2⟩
    apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    norm_num [basicEndpoint, kappa2, sigma1]
  · intro p hp _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Wu41.mem_PS.mp hp).1.two_le
    exact one_div_nonneg.mpr (by linarith)

/-- The variable upper values have a common finite bound over all sufficiently large bands.
CONDITIONAL ON IsLinearSieve only. -/
theorem variable_values_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ p ∈ Task366.primeBand4 N, |F (variableLevel B N p)| ≤ M := by
  have hc : ContinuousOn F (Icc (3 : ℝ) 5) := h.1.mono (by
    intro t ht
    change 0 < t
    linarith [ht.1])
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨J, hJ⟩ := variable_values_shift_small F f h B 1 (by norm_num)
  refine ⟨max C 0 + 1, by positivity, max 2 J, ?_⟩
  intro N hN p hp
  have hbound := hC _ (variableLevel_zero_range (by omega) hp)
  rw [Real.norm_eq_abs] at hbound
  calc
    |F (variableLevel B N p)| ≤
        |F (variableLevel B N p) - F (variableLevel 0 N p)| + |F (variableLevel 0 N p)| :=
      by
        have hh := abs_add_le (F (variableLevel B N p) - F (variableLevel 0 N p))
          (F (variableLevel 0 N p))
        simpa only [sub_add_cancel] using hh
    _ ≤ 1 + C := add_le_add (hJ N (by omega) p hp) hbound
    _ ≤ _ := by linarith [le_max_left C 0]

end LeanLab.ChenDoubleSieve.Task349
