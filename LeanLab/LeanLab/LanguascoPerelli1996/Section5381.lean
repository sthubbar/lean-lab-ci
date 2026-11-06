import LeanLab.LanguascoPerelli1996.Section5108
import LeanLab.PNTPort.Selberg.LZLemma1Full

/-!
P0071 page 360 display 25 at modulus one and integer N.
The source identifies this case with reference 11, display 23.
Reuse the proved Selberg mean square theorem from PNTPort.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Section5381
open Real MeasureTheory intervalIntegral

/-- Page 360 display 25 at modulus one. The damped sum is the existing
Languasco Zaccagnini polynomial limit, with the same exponential phase. -/
theorem dampedSum_mod_one (N : ℕ) (η : ℝ) :
    Section5108.dampedSum (N : ℝ) η (1 : DirichletCharacter ℂ 1) =
      LeanLab.LZCesaroShort.St N η := by
  unfold Section5108.dampedSum LeanLab.LZCesaroShort.St
  apply tsum_congr
  intro n
  have he (x : ℝ) : e x = LeanLab.PNTPort.LargeSieve.e x := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hchar : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) (1 : ZMod 1)]
    exact map_one _
  simp only [hchar, mul_one, he, Complex.ofReal_mul]

/-- Pages 359 and 360, the parameter z in the two encodings agrees. -/
theorem laplaceParameter_eq_zz (N : ℕ) (η : ℝ) :
    Section5108.laplaceParameter (N : ℝ) η = LeanLab.LZCesaroShort.zz N η := by
  unfold Section5108.laplaceParameter LeanLab.LZCesaroShort.zz
  rw [one_div]
  ring

/-- Page 360 display 25 for modulus one, integer N at least four and
2 at most Q at most N. CONDITIONAL ON RiemannHypothesis alone.
Reference 11 page 315 display 23 gives the same mean square mechanism.
The existing PNTPort theorem supplies the full analytic proof. -/
theorem estimate25_mod_one (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ Q : ℝ, 2 ≤ Q → Q ≤ N →
      (∫ η in (-(1 / Q))..(1 / Q),
        ‖Section5108.dampedSum (N : ℝ) η (1 : DirichletCharacter ℂ 1) -
          1 / Section5108.laplaceParameter (N : ℝ) η‖ ^ 2) ≤
        C * (N : ℝ) * Real.log N ^ 2 / Q := by
  obtain ⟨K, hK, hm⟩ := LeanLab.PNTPort.Selberg.lz_lemma1_explicit hRH
  refine ⟨2 * K + 1, by positivity, ?_⟩
  intro N hN Q hQ hQN
  have hN1 : 1 ≤ N := by omega
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hQ0 : 0 < Q := by linarith
  have hξ0 : 0 ≤ 1 / Q := by positivity
  have hξ2 : 1 / Q ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hQ0 (by norm_num)).2
    linarith
  have hb := hm N hN1 (1 / Q) hξ0 hξ2
  have hlo : 1 ≤ 2 * (N : ℝ) * (1 / Q) := by
    have hh : 1 ≤ 2 * (N : ℝ) / Q := (le_div_iff₀ hQ0).2 (by linarith)
    simpa only [mul_one_div] using hh
  have hhi : 2 * (N : ℝ) * (1 / Q) ≤ N := by
    have hh : 2 * (N : ℝ) ≤ (N : ℝ) * Q := by nlinarith
    simpa only [mul_one_div] using (div_le_iff₀ hQ0).2 hh
  have hl0 : 0 ≤ Real.log (2 * (N : ℝ) * (1 / Q)) := Real.log_nonneg hlo
  have hlhi : Real.log (2 * (N : ℝ) * (1 / Q)) ≤ Real.log N :=
    Real.log_le_log (by positivity) hhi
  have hlogN : 1 ≤ Real.log N := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9]
    exact h4.trans (Real.log_le_log (by norm_num) hN4)
  have hsq : 1 + Real.log (2 * (N : ℝ) * (1 / Q)) ^ 2 ≤ 2 * Real.log N ^ 2 := by
    nlinarith [pow_le_pow_left₀ hl0 hlhi 2]
  simp_rw [dampedSum_mod_one, laplaceParameter_eq_zz]
  calc
    _ ≤ K * N * (1 / Q) * (1 + Real.log (2 * (N : ℝ) * (1 / Q)) ^ 2) := hb
    _ ≤ K * N * (1 / Q) * (2 * Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ (2 * K + 1) * (N : ℝ) * Real.log N ^ 2 / Q := by
      have hp : 0 ≤ (N : ℝ) * Real.log N ^ 2 / Q := by positivity
      calc
        _ = (2 * K) * ((N : ℝ) * Real.log N ^ 2 / Q) := by ring
        _ ≤ (2 * K + 1) * ((N : ℝ) * Real.log N ^ 2 / Q) :=
          mul_le_mul_of_nonneg_right (by linarith) hp
        _ = _ := by ring

end LeanLab.LanguascoPerelli1996.Section5381

#print axioms LeanLab.LanguascoPerelli1996.Section5381.dampedSum_mod_one
#print axioms LeanLab.LanguascoPerelli1996.Section5381.laplaceParameter_eq_zz
#print axioms LeanLab.LanguascoPerelli1996.Section5381.estimate25_mod_one
