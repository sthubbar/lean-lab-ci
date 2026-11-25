/-
P0083 Perelli 1996, page 485, display 21.
ROUTE BURST S110 burst-20261122 split of Decomp582a.leaf_zero_density.
The range 1/2 ≤ σ ≤ 7/12 is already proved by Decomp582a.zero_density_left_strip from the
local Jensen count. The range 7/12 ≤ σ ≤ 1, the Huxley hybrid density estimate, is the new LEAF;
joining the two ranges with a common power of log qT is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp582a

namespace LeanLab.Perelli1996.Dens1123
open Real
open LeanLab.Perelli1996.Decomp582a
noncomputable section

/-- LEAF: Page 485 display 21 in the range 7/12 ≤ σ ≤ 1, the part not covered by
Decomp582a.zero_density_left_strip: ∑_{χ mod q} N(σ,T,χ) ≪ (qT)^(12(1-σ)/5) log^(c₄) qT,
zeros counted with analytic multiplicity. Class HARD. Cited inputs: Huxley, Large values of
Dirichlet polynomials III, Acta Arith. 26 1975, the hybrid form of the 12/5 density
estimate, and Ramachandra, reference 9 of the paper. -/
theorem leaf_zero_density_right :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
      ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 7 / 12 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d := by
  sorry

/-- For x ≥ log 2 and 0 ≤ a ≤ D, x^a ≤ (log 2)^(-D) x^D. -/
theorem rpow_le_log_two_mul {x a D : ℝ} (hx : Real.log 2 ≤ x) (ha : 0 ≤ a) (haD : a ≤ D) :
    x ^ a ≤ (Real.log 2) ^ (-D) * x ^ D := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hx0 : 0 < x := lt_of_lt_of_le hl2 hx
  have hsplit : x ^ a = x ^ (a - D) * x ^ D := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc x ^ (a - D) ≤ (Real.log 2) ^ (a - D) :=
        Real.rpow_le_rpow_of_nonpos hl2 hx (by linarith)
    _ ≤ (Real.log 2) ^ (-D) :=
        Real.rpow_le_rpow_of_exponent_ge hl2 hl21.le (by linarith)

/-- Page 485 display 21, the exact statement of Decomp582a.leaf_zero_density, proved from
Decomp582a.zero_density_left_strip and the LEAF leaf_zero_density_right with the log
exponent max d 1. CONDITIONAL ON leaf_zero_density_right. -/
theorem leaf_zero_density_of_split1123 :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧
      ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d := by
  obtain ⟨C1, hC1, hleft⟩ := zero_density_left_strip
  obtain ⟨C2, d2, hC2, hd2, hright⟩ := leaf_zero_density_right
  set D := max d2 1 with hD
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := (Real.log 2) ^ (-D) with hK
  have hK0 : 0 < K := Real.rpow_pos_of_pos hl2 _
  refine ⟨(C1 + C2) * K, D, by positivity, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro q _ T σ hT hσ hσ1 Z hZ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
  have hlog : Real.log 2 ≤ Real.log ((q : ℝ) * T) := Real.log_le_log (by norm_num) hqT
  have hP : 0 ≤ ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) := by positivity
  have hlog0 : 0 ≤ Real.log ((q : ℝ) * T) := hl2.le.trans hlog
  rcases le_total σ (7 / 12) with h | h
  · have hb := hleft q T σ hT hσ h Z (fun χ ρ hρ => hZ χ ρ hρ)
    have hc : Real.log ((q : ℝ) * T) ≤ K * Real.log ((q : ℝ) * T) ^ D := by
      have := rpow_le_log_two_mul hlog zero_le_one (le_max_right d2 1)
      rwa [Real.rpow_one] at this
    calc _ ≤ C1 * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * Real.log ((q : ℝ) * T) := hb
      _ ≤ C1 * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * (K * Real.log ((q : ℝ) * T) ^ D) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := by
          have : 0 ≤ C2 * K * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
              Real.log ((q : ℝ) * T) ^ D := by positivity
          nlinarith
  · have hb := hright q T σ hT h hσ1 Z hZ
    have hc : Real.log ((q : ℝ) * T) ^ d2 ≤ K * Real.log ((q : ℝ) * T) ^ D :=
      rpow_le_log_two_mul hlog hd2.le (le_max_left d2 1)
    calc _ ≤ C2 * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * Real.log ((q : ℝ) * T) ^ d2 := hb
      _ ≤ C2 * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * (K * Real.log ((q : ℝ) * T) ^ D) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := by
          have : 0 ≤ C1 * K * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
              Real.log ((q : ℝ) * T) ^ D := by positivity
          nlinarith

end
end LeanLab.Perelli1996.Dens1123
