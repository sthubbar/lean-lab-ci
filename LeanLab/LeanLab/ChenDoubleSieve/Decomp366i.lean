import LeanLab.ChenDoubleSieve.Decomp366b

/-!
The fixed F4 kernel and its compact integration domain.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
These lemmas supply regularity and exact coordinates, not prime mass convergence.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The fixed F4 integrand in exponent coordinates. -/
def kernel4 (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  f ((1 / 2 - x.1 - x.2) / kappa1) / (x.1 * x.2)

/-- The actual ordered prime domain is the fixed logarithmic triangle.
The natural bounds below N follow from the upper exponent cutoff. -/
theorem mem_fullPairs4_triangle {N p q : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hq : q.Prime) :
    (p, q) ∈ fullPairs4 N ↔
      kappa1 ≤ log (p : ℝ) / log N ∧
        log (p : ℝ) / log N < log (q : ℝ) / log N ∧
        log (q : ℝ) / log N < kappa2 := by
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have horder : p < q ↔ log (p : ℝ) / log N < log (q : ℝ) / log N := by
    rw [div_lt_div_iff_of_pos_right hlog, log_lt_log_iff hp0 hq0]
    norm_cast
  simp only [fullPairs4, mem_filter, mem_product, Finset.mem_range, hp, hq, true_and,
    Task367.power_cutoff_le_iff hN hp.pos, Task367.lt_power_cutoff_iff hN hq.pos, horder]
  constructor
  · tauto
  · intro hx
    have hq1 : log (q : ℝ) / log N < 1 := hx.2.2.trans (by norm_num [kappa2])
    have hp1 : log (p : ℝ) / log N < 1 := hx.2.1.trans hq1
    have hpN : p < N := by
      have he := (Task367.lt_power_cutoff_iff hN hp.pos 1).2 hp1
      simpa only [rpow_one, Nat.cast_lt] using he
    have hqN : q < N := by
      have he := (Task367.lt_power_cutoff_iff hN hq.pos 1).2 hq1
      simpa only [rpow_one, Nat.cast_lt] using he
    exact ⟨⟨hpN, hqN⟩, hx⟩

/-- The zero loss sum uses exactly the fixed argument printed in the paper. -/
theorem reciprocalFullSum4_zero_coordinates (f : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    reciprocalFullSum4 f 0 N = ∑ p ∈ fullPairs4 N,
      f ((1 / 2 - log (p.1 : ℝ) / log N - log (p.2 : ℝ) / log N) / kappa1) /
        ((p.1 : ℝ) * p.2) := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2, _⟩ := fullPairs4_primes hp
  rw [Task367.lowerLevel_zero_coordinates hN hp1.pos hp2.pos]

/-- The fixed kernel is continuous on the full closed square.
CONDITIONAL ON IsLinearSieve only. -/
theorem kernel4_continuousOn (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ContinuousOn (kernel4 f) (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) := by
  apply (lower_kernel_continuous F f h).div (continuous_fst.mul continuous_snd).continuousOn
  intro x hx
  apply mul_ne_zero
  · exact (lt_of_lt_of_le (by norm_num [kappa1] : 0 < kappa1) hx.1.1).ne'
  · exact (lt_of_lt_of_le (by norm_num [kappa1] : 0 < kappa1) hx.2.1).ne'

/-- Compactness makes the F4 kernel uniformly continuous on the exponent square.
CONDITIONAL ON IsLinearSieve only. -/
theorem kernel4_uniformContinuousOn (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    UniformContinuousOn (kernel4 f) (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) := by
  exact (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (kernel4_continuousOn F f h)

/-- The F4 kernel is integrable on the closed ordered triangle.
CONDITIONAL ON IsLinearSieve only. -/
theorem kernel4_integrableOn_triangle (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    IntegrableOn (kernel4 f)
      {x : ℝ × ℝ | kappa1 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ kappa2} volume := by
  have hi : IntegrableOn (kernel4 f) (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) volume :=
    (kernel4_continuousOn F f h).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply hi.mono_set
  intro x hx
  exact ⟨⟨hx.1, hx.2.1.trans hx.2.2⟩, ⟨hx.1.trans hx.2.1, hx.2.2⟩⟩

/-- The printed nested integral is the iterated integral of the fixed kernel. -/
theorem lowerIntegral4_kernel (f : ℝ → ℝ) :
    lowerIntegral4 f = ∫ t in kappa1..kappa2, ∫ u in t..kappa2, kernel4 f (t, u) := by
  unfold lowerIntegral4
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only [kernel4]
  ring

end LeanLab.ChenDoubleSieve.Task366
