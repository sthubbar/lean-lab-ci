/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 Section 7 page 29, the finite direction reduction before 42.
-/
import LeanLab.PlattTrudgian2014.LambdaMoment

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex
open scoped ComplexConjugate

/-- A finite set of unit directions detects at least a 1 minus epsilon fraction of every norm. -/
theorem exists_finite_directions {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Finset ℂ, (∀ ρ ∈ D, ‖ρ‖ = 1) ∧
      ∀ z : ℂ, z ≠ 0 → ∃ ρ ∈ D, (1 - ε) * ‖z‖ ≤ (ρ * z).re := by
  classical
  obtain ⟨T, hT, hfin, hcover⟩ :=
    (isCompact_sphere (0 : ℂ) 1).finite_cover_balls hε
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro ρ hρ
    simpa only [Metric.mem_sphere, dist_zero_right] using hT (hfin.mem_toFinset.mp hρ)
  · intro z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let y : ℂ := conj z / (‖z‖ : ℂ)
    have hy : ‖y‖ = 1 := by
      simp [y, hn]
    have hymem : y ∈ Metric.sphere (0 : ℂ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hy
    obtain ⟨ρ, hρ, hdist⟩ := Set.mem_iUnion₂.mp (hcover hymem)
    refine ⟨ρ, hfin.mem_toFinset.mpr hρ, ?_⟩
    have hyz : y * z = (‖z‖ : ℂ) := by
      dsimp [y]
      rw [div_mul_eq_mul_div, Complex.conj_mul']
      field_simp
    have hd : ‖y - ρ‖ ≤ ε := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hdist).le
    have he := Complex.re_le_norm ((y - ρ) * z)
    rw [norm_mul] at he
    have hm := mul_le_mul_of_nonneg_right hd (norm_nonneg z)
    rw [sub_mul, Complex.sub_re, hyz, Complex.ofReal_re] at he
    linarith

def projectedSet (L : ℕ) (a : ℝ) (ρ : ℂ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ a * L ≤ (ρ * G L x).re}

theorem projectedSet_volume_ne_top (L : ℕ) (a : ℝ) (ρ : ℂ) :
    volume (projectedSet L a ρ) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono (fun _ hx => hx.1))

theorem projectedSet_markov (L : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) (ρ : ℂ) :
    Real.exp (t * (a * L)) * (volume (projectedSet L a ρ)).toReal ≤ expMoment L t ρ := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := momentIntegrand L t ρ)
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (continuous_momentIntegrand L t ρ).integrableOn_Icc
    (Real.exp (t * (a * L)))
  have hset : {x | Real.exp (t * (a * L)) ≤ momentIntegrand L t ρ x} =
      {x | a * L ≤ (ρ * G L x).re} := by
    ext x
    simp only [Set.mem_ofPred_eq, momentIntegrand, Real.exp_le_exp, mul_le_mul_iff_right₀ ht]
  rw [hset, Measure.real, Measure.restrict_apply' measurableSet_Icc] at hm
  have heq : {x | a * L ≤ (ρ * G L x).re} ∩ Set.Icc (0 : ℝ) 1 =
      projectedSet L a ρ := by ext x; simp [projectedSet, and_comm]
  rw [heq] at hm
  simpa only [expMoment, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] using hm

theorem projectedSet_bound (L : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    (volume (projectedSet L a ρ)).toReal ≤
      Real.exp (-(t * (a * L))) * Real.cosh t ^ L := by
  have hm := (projectedSet_markov L a ht ρ).trans (expMoment_le_cosh_pow L ht.le hρ)
  have he : (volume (projectedSet L a ρ)).toReal ≤
      Real.cosh t ^ L / Real.exp (t * (a * L)) := by
    rw [le_div_iff₀ (Real.exp_pos _)]
    nlinarith [hm]
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using he

theorem bigSet_exp_bound {a lam t : ℝ} (ha : 0 < a) (hal : a < lam) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (volume (bigSet N lam)).toReal ≤
        C * Real.exp (-(t * a - Real.log (Real.cosh t)) * Lof N) := by
  classical
  have hl : 0 < lam := ha.trans hal
  have hε : 0 < 1 - a / lam := by
    rw [sub_pos, div_lt_one hl]
    exact hal
  obtain ⟨D, hD, hnet⟩ := exists_finite_directions hε
  refine ⟨D.card, Nat.cast_nonneg _, fun N _ => ?_⟩
  let U := ⋃ ρ ∈ D, projectedSet (Lof N) a ρ
  have hcover : bigSet N lam ⊆ U := by
    intro x hx
    have hn : G (Lof N) x ≠ 0 := by
      apply norm_ne_zero_iff.mp
      exact ne_of_gt ((mul_nonneg hl.le (Nat.cast_nonneg _)).trans_lt hx.2)
    obtain ⟨ρ, hρ, hp⟩ := hnet (G (Lof N) x) hn
    apply Set.mem_iUnion₂.mpr
    refine ⟨ρ, hρ, hx.1, ?_⟩
    have haL : a * Lof N ≤ (1 - (1 - a / lam)) * ‖G (Lof N) x‖ := by
      have hf : a * Lof N = (a / lam) * (lam * Lof N) := by field_simp
      rw [show 1 - (1 - a / lam) = a / lam by ring, hf]
      exact mul_le_mul_of_nonneg_left hx.2.le (div_nonneg ha.le hl.le)
    exact haL.trans hp
  have hU : volume U ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    apply measure_mono
    intro x hx
    obtain ⟨ρ, _, hp⟩ := Set.mem_iUnion₂.mp hx
    exact hp.1
  calc
    _ ≤ volume.real U := measureReal_mono hcover hU
    _ ≤ ∑ ρ ∈ D, (volume (projectedSet (Lof N) a ρ)).toReal :=
      measureReal_biUnion_finset_le D _
    _ ≤ ∑ ρ ∈ D, Real.exp (-(t * (a * Lof N))) * Real.cosh t ^ Lof N :=
      Finset.sum_le_sum fun ρ hρ => projectedSet_bound _ _ ht (hD ρ hρ).le
    _ = (D.card : ℝ) * Real.exp (-(t * a - Real.log (Real.cosh t)) * Lof N) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : Real.cosh t ^ Lof N = Real.exp (Real.log (Real.cosh t) * Lof N) := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log (Real.cosh_pos t)]
      rw [hc, ← Real.exp_add]
      congr 2
      ring

#print axioms exists_finite_directions

#print axioms projectedSet_volume_ne_top

#print axioms projectedSet_markov

#print axioms projectedSet_bound

#print axioms bigSet_exp_bound

end LeanLab.PlattTrudgian2014
