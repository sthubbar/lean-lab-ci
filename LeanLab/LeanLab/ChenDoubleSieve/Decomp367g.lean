import LeanLab.ChenDoubleSieve.Decomp367d

/-!
The fixed continuous F5 kernel after the elementary replacements.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The prime mass convergence on the diagonal triangle is still unproved.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The fixed F5 kernel in logarithmic prime coordinates. -/
def kernel5 (f : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  f ((1 / 2 - z.1 - z.2) / kappa1) / (z.1 * z.2)

/-- The finite natural bounds are redundant inside the logarithmic F5 triangle. -/
theorem mem_fullPairs5_triangle {N p q : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hq : q.Prime) :
    (p, q) ∈ fullPairs5 N ↔
      kappa1 ≤ log (p : ℝ) / log N ∧ log (p : ℝ) / log N < kappa2 ∧
      kappa2 ≤ log (q : ℝ) / log N ∧
      log (p : ℝ) / log N + log (q : ℝ) / log N < 1 / 3 := by
  rw [mem_fullPairs5_coordinates hN hp hq]
  constructor
  · tauto
  · intro hz
    have hp1 : log (p : ℝ) / log N < 1 :=
      hz.2.1.trans (by norm_num [kappa2])
    have hq1 : log (q : ℝ) / log N < 1 := by
      have hpos : 0 < log (p : ℝ) / log N :=
        lt_of_lt_of_le (by norm_num [kappa1]) hz.1
      linarith [hz.2.2.2]
    have hpN : p < N := by
      have he := (lt_power_cutoff_iff hN hp.pos 1).2 hp1
      simpa only [rpow_one, Nat.cast_lt] using he
    have hqN : q < N := by
      have he := (lt_power_cutoff_iff hN hq.pos 1).2 hq1
      simpa only [rpow_one, Nat.cast_lt] using he
    exact ⟨hpN, hqN, hz⟩

/-- The zero loss prime sum uses exactly the printed argument of f. -/
theorem reciprocalFullSum5_zero_coordinates (f : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    reciprocalFullSum5 f 0 N = ∑ p ∈ fullPairs5 N,
      f ((1 / 2 - log (p.1 : ℝ) / log N - log (p.2 : ℝ) / log N) / kappa1) /
        ((p.1 : ℝ) * p.2) := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2, _⟩ := fullPairs5_primes hp
  rw [lowerLevel_zero_coordinates hN hp1.pos hp2.pos]

/-- The fixed F5 kernel is continuous on a rectangle containing the full triangle.
CONDITIONAL ON IsLinearSieve only. -/
theorem kernel5_continuousOn (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ContinuousOn (kernel5 f)
      (Icc kappa1 kappa2 ×ˢ Icc kappa2 (1 / 3 - kappa1)) := by
  have ha : Continuous (fun z : ℝ × ℝ => (1 / 2 - z.1 - z.2) / kappa1) := by
    fun_prop
  have hf : ContinuousOn (fun z : ℝ × ℝ => f ((1 / 2 - z.1 - z.2) / kappa1))
      (Icc kappa1 kappa2 ×ˢ Icc kappa2 (1 / 3 - kappa1)) :=
    h.2.1.comp ha.continuousOn (by
      intro z hz
      change 0 < (1 / 2 - z.1 - z.2) / kappa1
      apply div_pos
      · have ht := hz.1.2
        have hu := hz.2.2
        norm_num [kappa1, kappa2] at ht hu ⊢
        linarith
      · norm_num [kappa1])
  apply hf.div (continuous_fst.mul continuous_snd).continuousOn
  intro z hz
  apply mul_ne_zero
  · have ht := hz.1.1
    have hp : 0 < z.1 := lt_of_lt_of_le (by norm_num [kappa1]) ht
    exact hp.ne'
  · have hu := hz.2.1
    have hp : 0 < z.2 := lt_of_lt_of_le (by norm_num [kappa2]) hu
    exact hp.ne'

/-- Compactness makes the fixed F5 kernel uniformly continuous on that rectangle.
CONDITIONAL ON IsLinearSieve only. -/
theorem kernel5_uniformContinuousOn (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    UniformContinuousOn (kernel5 f)
      (Icc kappa1 kappa2 ×ˢ Icc kappa2 (1 / 3 - kappa1)) := by
  exact (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (kernel5_continuousOn F f h)

/-- The printed nested F5 integral is the integral of the fixed kernel. -/
theorem lowerIntegral5_kernel (f : ℝ → ℝ) :
    lowerIntegral5 f = ∫ t in kappa1..kappa2,
      ∫ u in kappa2..(1 / 3 - t), kernel5 f (t, u) := by
  unfold lowerIntegral5
  rw [show (1 / 2 - 2 * kappa1 : ℝ) = 1 / 3 by norm_num [kappa1]]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only [kernel5]
  ring

end LeanLab.ChenDoubleSieve.Task367
