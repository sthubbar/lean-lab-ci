/-
P0069, page 12, logarithmic energy and the powered level estimate 3.10.
The unrestricted logarithmic divisor moment remains an explicit premise.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437d

namespace LeanLab.BHP1997.Decomp437i
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp437d
open scoped BigOperators

/-- Page 12, the logarithmic energy allowance for each fixed polynomial power.
Apply the supplied energy estimate to its proved divisor-bounded convolution
coefficients and the enlarged length F to the power g.
CONDITIONAL on EnergyLogBound. -/
theorem truncated_power_energy_log (henergy : EnergyLogBound) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ a : ℕ → ℂ, CoeffBound a B →
    ∀ x F : ℝ, 2 ≤ x → 1 ≤ Real.log x → 2 ≤ F → F ≤ x →
      energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) ≤
        C * Real.log x ^ K := by
  have hg0 : g ≠ 0 := by omega
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : (0 : ℝ) < g := by linarith
  obtain ⟨Ce, K, hCe, hK, he⟩ := energy_log_uniform henergy
    ((g : ℝ) * (max B 0 + 1)) (c1 ^ g) (c2 ^ g)
    (pow_pos hc1 _) (pow_lt_pow_left₀ hc2 hc1.le hg0)
  refine ⟨Ce * (g : ℝ) ^ K, K, by positivity, hK, ?_⟩
  intro a ha x F hx hlx hF hFx
  have hxpow : 1 ≤ x ^ g := one_le_pow₀ (by linarith)
  have hFpow : 2 ≤ F ^ g := hF.trans (le_self_pow₀ (by linarith) hg0)
  have hlogpow : 1 ≤ Real.log (x ^ g) := by
    rw [Real.log_pow]
    exact one_le_mul_of_one_le_of_one_le hgR hlx
  have hh := he (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) (x ^ g) (F ^ g) hlogpow hFpow
    (pow_le_pow_left₀ (by linarith) hFx g)
  rw [Real.log_pow, Real.mul_rpow hgpos.le (by linarith : 0 ≤ Real.log x)] at hh
  exact hh.trans_eq (by ring)

/-- Page 12, the exact minimum-form powered level estimate with a logarithmic loss.
This supplies the cardinality input before the Case 2 and Case 3 exponent arguments.
CONDITIONAL on the three explicit original analytic inputs. -/
theorem power_level_log_bound (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2)
    (g : ℕ) (hg : 1 ≤ g) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
    ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
    CoeffBound a B → 2 ≤ x → 1 ≤ Real.log x → 2 ≤ F → F ≤ x →
    2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, V ≤ ‖dirPoly a c1 c2 F p.2 (half p.1)‖) →
    (S.card : ℝ) ≤ C * Real.log x ^ D *
      (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
  obtain ⟨C0, hC0, hlevel⟩ := power_level_min hmean hlarge B c1 c2 hc1 hc2 g hg
  obtain ⟨Ce, K, hCe, hK, he⟩ := truncated_power_energy_log henergy B c1 c2 hc1 hc2 g hg
  let C := 2 * C0 * (Ce + 16 * Ce ^ 3)
  let D := 3 * K + 2
  refine ⟨C, D, by dsimp [C]; positivity, by dsimp [D]; linarith, ?_⟩
  intro x F T V q S a ha hx hlx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  let E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun n hn => by positivity)
  have hEF : E ≤ Ce * Real.log x ^ K := he a ha x F hx hlx hF hFx
  have hEcube : E + E ^ 3 ≤ (Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K) := by
    have hh := energy_cubic_log_bound hE hCe.le hK hlx hEF
    nlinarith [pow_nonneg hE 3]
  have hlogs : Real.log x + Real.log x ^ 2 ≤ 2 * Real.log x ^ 2 := by nlinarith
  have hh := hlevel x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  change (S.card : ℝ) ≤ C0 * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * _ at hh
  calc
    (S.card : ℝ) ≤ _ := hh
    _ ≤ C0 * (2 * Real.log x ^ 2) * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K)) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
      gcongr
    _ = C * (Real.log x ^ (3 * K) * Real.log x ^ 2) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
      dsimp [C]
      ring
    _ = _ := by
      have heq : Real.log x ^ (3 * K) * Real.log x ^ 2 = Real.log x ^ D := by
        calc
          _ = Real.log x ^ (3 * K) * Real.log x ^ (2 : ℝ) := by simp
          _ = _ := (Real.rpow_add (by linarith : 0 < Real.log x) _ _).symm
      rw [heq]

end LeanLab.BHP1997.Decomp437i
