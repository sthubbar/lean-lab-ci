import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, page 74, the lower count for the special polynomial F = X.
This proves a restricted lower bound, not the general degree one theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset Filter Real Asymptotics
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The part 1 count for the identity polynomial. -/
def c1IdentityCount (ξ : ℕ) : ℕ :=
  #{n ∈ Icc (1 : ℕ) ξ | AlmostGT 2 (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) n}

/-- Every prime is counted, with its own index as the threshold variable. -/
lemma primeCounting_le_c1IdentityCount (ξ : ℕ) : ξ.primeCounting ≤ c1IdentityCount ξ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply card_le_card
  intro p hp
  obtain ⟨hpξ, hprime⟩ := Nat.mem_primesLE.mp hp
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_le, hpξ⟩, hprime.one_le, ?_, ?_⟩
  · rw [Nat.primeFactorsList_prime hprime]
    simp
  · intro q hq
    rw [Nat.primeFactorsList_prime hprime, List.mem_singleton] at hq
    subst q
    exact Real.rpow_lt_self_of_one_lt (by exact_mod_cast hprime.one_lt) (by norm_num)

/-- Chebyshev's elementary lower bound gives a positive constant in the identity case. -/
theorem c1Identity_lower :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      a * ξ / Real.log ξ < c1IdentityCount ξ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / 4 := by positivity
  have hsmall : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.natCast_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / 4 * n / Real.log n < (c1IdentityCount n : ℝ) := by
    filter_upwards [hsmall.def hc, eventually_ge_atTop 4] with n hn hn4
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    simp only [Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hnpos] at hn
    have hshift : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
      rw [← Real.log_mul (by norm_num) hnpos.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have hshift2 : Real.log ((n : ℝ) + 1) ≤ Real.log 2 / 2 * n := by
      nlinarith
    have hpi := Chebyshev.pi_ge n
    have hpc : (n.primeCounting : ℝ) ≤ c1IdentityCount n := by
      exact_mod_cast primeCounting_le_c1IdentityCount n
    have hmain : Real.log 2 / 4 * n < n * Real.log 2 - Real.log ((n : ℝ) + 1) := by
      nlinarith
    calc
      Real.log 2 / 4 * n / Real.log n <
          (n * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log n :=
        div_lt_div_of_pos_right hmain hlog
      _ ≤ (n.primeCounting : ℝ) := by simpa only [Nat.cast_add, Nat.cast_one] using hpi
      _ ≤ c1IdentityCount n := hpc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨Real.log 2 / 4, hc, N, fun ξ hξ => hN ξ (by omega)⟩

example : (5 : ℕ).primeCounting ≤ c1IdentityCount 5 := primeCounting_le_c1IdentityCount 5

end
end LeanLab.Ricci1937
