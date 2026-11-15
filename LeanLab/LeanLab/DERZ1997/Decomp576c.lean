import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Rosser's limiting choice of powers for the real-part Jensen function.
Trudgian arXiv:1206.1844v4 page 7, display 4.2.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576c
open Filter Topology

/-- Every nonzero complex centre value admits increasing powers whose normalized
real parts converge to one. Trudgian page 7, display 4.2.
-/
theorem rosser_power_sequence576 {z : ℂ} (hz : z ≠ 0) :
    ∃ N : ℕ → ℕ, StrictMono N ∧
      Tendsto (fun k => (z ^ N k).re / ‖z‖ ^ N k) atTop (𝓝 1) := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Circle := ⟨z / (‖z‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [hnorm.ne']⟩
  obtain ⟨N, hN, hlim⟩ := (mapClusterPt_one_atTop_pow u).tendsto_subseq
  refine ⟨N, hN, ?_⟩
  have hcoe : Tendsto (fun k => ((u ^ N k : Circle) : ℂ)) atTop (𝓝 1) := by
    have hh := (continuous_subtype_val.tendsto (1 : Circle)).comp hlim
    convert hh using 1 <;> rfl
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcoe
  have heq (n : ℕ) : ((u ^ n : Circle) : ℂ).re = (z ^ n).re / ‖z‖ ^ n := by
    rw [Circle.coe_pow]
    change ((z / (‖z‖ : ℂ)) ^ n).re = _
    rw [div_pow, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  simpa only [Function.comp_def, heq, Complex.one_re] using hre

/-- The normalized centre value is eventually positive along Rosser's powers.
Trudgian page 7, display 4.2, the nonvanishing needed before applying Jensen.
-/
theorem power_centre_eventually_pos576 {z : ℂ} (hz : z ≠ 0)
    (N : ℕ → ℕ)
    (hcentre : Tendsto (fun k => (z ^ N k).re / ‖z‖ ^ N k) atTop (𝓝 1)) :
    ∀ᶠ k in atTop, 0 < (z ^ N k).re := by
  filter_upwards [hcentre.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with k hk
  simpa using (lt_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) (N k))).mp hk

/-- The centre logarithm divided by the power tends to log of the modulus.
Trudgian page 8, the limiting centre estimate following display 4.9.
This states the normalized limit, rather than a limit with a moving value.
-/
theorem power_centre_log_limit576 {z : ℂ} (hz : z ≠ 0)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k => (z ^ N k).re / ‖z‖ ^ N k) atTop (𝓝 1)) :
    Tendsto (fun k => Real.log |(z ^ N k).re| / (N k : ℝ)) atTop
      (𝓝 (Real.log ‖z‖)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlog : Tendsto (fun k => Real.log ((z ^ N k).re / ‖z‖ ^ N k)) atTop (𝓝 0) := by
    have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcentre
    convert hh using 1 <;> first | rfl | simp
  have hinv : Tendsto (fun k => (1 : ℝ) / (N k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp hN.tendsto_atTop
  have hsum : Tendsto (fun k => Real.log ‖z‖ +
      Real.log ((z ^ N k).re / ‖z‖ ^ N k) * (1 / (N k : ℝ))) atTop
      (𝓝 (Real.log ‖z‖)) := by
    simpa using tendsto_const_nhds.add (hlog.mul hinv)
  refine hsum.congr' ?_
  filter_upwards [power_centre_eventually_pos576 hz N hcentre,
    hN.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk hkN
  have hNk : (N k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hkN))
  rw [abs_of_pos hk, Real.log_div hk.ne' (pow_pos hn _).ne', Real.log_pow]
  field_simp
  <;> ring

end LeanLab.DERZ1997.Decomp576c
