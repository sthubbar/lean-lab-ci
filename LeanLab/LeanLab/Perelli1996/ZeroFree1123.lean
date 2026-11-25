/-
P0083 Perelli 1996, page 484, display 19.
ROUTE BURST S110 burst-20261122 split of BadMod1123.leaf_zero_free_region_19 by the character:
the nonprincipal characters and the Riemann zeta function are the two new LEAFs; the principal
character modulo q, whose L-function is ∏_{p | q} (1 - p^(-s)) ζ(s), is proved from the zeta LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Perelli1996.ZeroFree1123
open Real
noncomputable section

/-- LEAF: Page 484 display 19 for the nonprincipal characters, by the zero free region of
Prachar Chapter 8 and Siegel's theorem: for every ε' > 0 there is c > 0 with L(s,χ) ≠ 0 for
χ ≠ χ₀ modulo q and σ > 1 - c/max{q^ε', log^(4/5)(|t|+1)}.
Class HARD. Cited inputs: Prachar, Primzahlverteilung, Chapter 8, and Siegel's theorem. -/
theorem leaf_zero_free_nonprincipal (ε' : ℝ) (hε' : 0 < ε') :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      1 - c / max ((q : ℝ) ^ ε') (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

/-- LEAF: Page 484 display 19 for q = 1, the zero free region of the Riemann zeta function
of Prachar Chapter 8: ζ(s) ≠ 0 for s ≠ 1 and σ > 1 - c/max{1, log^(4/5)(|t|+1)}.
Class HARD. Cited input: Prachar, Primzahlverteilung, Chapter 8, a Vinogradov type region,
which is stronger than the exponent 4/5 needed here. -/
theorem leaf_zero_free_zeta :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / max 1 (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) < s.re → riemannZeta s ≠ 0 := by
  sorry

/-- Page 484 display 19, the exact statement of BadMod1123.leaf_zero_free_region_19,
from the two LEAFs: for the principal character L(s,χ₀) = ∏_{p | q} (1 - p^(-s)) ζ(s) and
each factor 1 - p^(-s) vanishes only on σ = 0. CONDITIONAL ON leaf_zero_free_nonprincipal
and leaf_zero_free_zeta. -/
theorem zero_free_region_19_of_split1123 (ε' : ℝ) (hε' : 0 < ε') :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), s ≠ 1 →
      1 - c / max ((q : ℝ) ^ ε') (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c1, hc1, h1⟩ := leaf_zero_free_nonprincipal ε' hε'
  obtain ⟨c2, hc2, h2⟩ := leaf_zero_free_zeta
  refine ⟨min (min c1 c2) (1 / 2), by positivity, ?_⟩
  intro q _ χ s hs hre
  set b := Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5) with hb
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqa : 1 ≤ (q : ℝ) ^ ε' := Real.one_le_rpow hq1 hε'.le
  have hb0 : 0 ≤ b := by
    rw [hb]; apply Real.rpow_nonneg
    exact Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hM1 : 1 ≤ max ((q : ℝ) ^ ε') b := hqa.trans (le_max_left _ _)
  have hM0 : 0 < max ((q : ℝ) ^ ε') b := by linarith
  have hcm : min (min c1 c2) (1 / 2) ≤ c1 := (min_le_left _ _).trans (min_le_left _ _)
  have hcm2 : min (min c1 c2) (1 / 2) ≤ c2 := (min_le_left _ _).trans (min_le_right _ _)
  have hch : min (min c1 c2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  -- σ > 1/2
  have hhalf : 1 / 2 < s.re := by
    have : min (min c1 c2) (1 / 2) / max ((q : ℝ) ^ ε') b ≤ 1 / 2 := by
      rw [div_le_iff₀ hM0]; nlinarith
    linarith
  by_cases hχ : χ = 1
  · subst hχ
    have hzre : 1 - c2 / max 1 b < s.re := by
      have h3 : c2 / max 1 b ≥ min (min c1 c2) (1 / 2) / max ((q : ℝ) ^ ε') b := by
        have hm1 : 0 < max 1 b := lt_of_lt_of_le one_pos (le_max_left _ _)
        have hle : max 1 b ≤ max ((q : ℝ) ^ ε') b := max_le_max hqa le_rfl
        calc min (min c1 c2) (1 / 2) / max ((q : ℝ) ^ ε') b
            ≤ c2 / max ((q : ℝ) ^ ε') b := div_le_div_of_nonneg_right hcm2 hM0.le
          _ ≤ c2 / max 1 b := div_le_div_of_nonneg_left hc2.le hm1 hle
      linarith
    have hz := h2 s hs hzre
    have heq := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs
    rw [DirichletCharacter.LFunctionTrivChar] at heq
    rw [heq]
    refine mul_ne_zero ?_ hz
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    intro h0
    have hpow : (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
    have hn := congrArg norm hpow
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos),
      norm_one, Complex.neg_re] at hn
    have : (p : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    linarith
  · apply h1 q χ hχ s
    have : min (min c1 c2) (1 / 2) / max ((q : ℝ) ^ ε') b ≤ c1 / max ((q : ℝ) ^ ε') b :=
      div_le_div_of_nonneg_right hcm hM0.le
    linarith

end
end LeanLab.Perelli1996.ZeroFree1123
