/-
FALSIFY unit for `near_sup357_derivative_moment357`, burst 2026-11-17. AI wrote the Lean
code. Binary Goldbach is open.

This file does NOT prove the negation of that leaf. It proves in full, with no open step and no new
definition, the first rigorous step of the refutation recorded in
`notes/burst-20261117/Linnik1951-near_sup357_derivative_moment357.md`: the conclusion of
the leaf forces a POINTWISE bound on the differentiated series at phase zero, uniformly
in every nonprincipal character of every modulus up to N to the one seventh. The notes
explain why that pointwise bound fails for the quadratic character mod 3 lifted to level
3^k, by the classical Mellin transform argument; that part is paper mathematics, not Lean.

Standard mathematics used: a locally uniformly dominated series of continuous functions
is continuous, and the first fundamental theorem of calculus at the left end point.
-/
import LeanLab.Linnik1951.SPLIT_near_sup357_local_variation357

namespace LeanLab.Linnik1951

open Filter Topology

/-- The differentiated damped character prime series is continuous in the phase: each
term is continuous and the terms are dominated by the summable sequence
`2 pi p exp(-p/N)`, uniformly in the phase. Standard Weierstrass M test. -/
theorem near_sup357_derivative_series_continuous357 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    Continuous (fun β : ℝ => ∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : Summable (fun p : Nat.Primes =>
      2 * Real.pi * ((((p : ℕ) : ℝ)) ^ 1 * Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ)))) := by
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul 1 (r := 1 / (N : ℝ)) (by positivity)
    exact (h0.comp_injective Nat.Primes.coe_nat_injective).mul_left (2 * Real.pi)
  refine continuous_tsum (fun p => by fun_prop) hs ?_
  intro p β
  have h1 : ‖χ ((p : ℕ))‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖(Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ)‖ =
      Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    congr 1
    field_simp
  have h3 : ‖((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I : ℂ)‖ =
      2 * Real.pi * ((p : ℕ) : ℝ) := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
  have h4 : ‖Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, norm_mul, h2, h3, h4, mul_one]
  have hE : 0 ≤ Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ)) := (Real.exp_pos _).le
  have hP : 0 ≤ 2 * Real.pi * ((p : ℕ) : ℝ) := by positivity
  calc ‖χ ((p : ℕ))‖ * Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ)) * (2 * Real.pi * ((p : ℕ) : ℝ))
      ≤ 1 * Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ)) * (2 * Real.pi * ((p : ℕ) : ℝ)) := by
        gcongr
    _ = 2 * Real.pi * ((((p : ℕ) : ℝ)) ^ 1 * Real.exp (-(1 / (N : ℝ)) * ((p : ℕ) : ℝ))) := by
        ring

/-- First fundamental theorem of calculus at the left end point, in inequality form: if a
continuous real function has `∫ 0..α g ≤ K α` for every `α` in `(0, a]`, then
`g 0 ≤ K`. Standard. -/
theorem near_sup357_value_le_of_integral_le357 {g : ℝ → ℝ} (hg : Continuous g) {a K : ℝ}
    (ha : 0 < a) (h : ∀ α : ℝ, 0 ≤ α → α ≤ a → (∫ β in (0 : ℝ)..α, g β) ≤ K * α) :
    g 0 ≤ K := by
  have hd : HasDerivAt (fun u : ℝ => ∫ β in (0 : ℝ)..u, g β) (g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have ht := hd.tendsto_slope_zero_right
  refine le_of_tendsto ht ?_
  have hmem : Set.Ioc (0 : ℝ) a ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT ha
  filter_upwards [hmem] with t ht
  have h1 := h t ht.1.le ht.2
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht.1]
  linarith [mul_comm K t]

/-- The conclusion of `near_sup357_derivative_moment357` forces a pointwise bound at phase
zero. Stated with that conclusion as an explicit hypothesis `hX`, so nothing here depends
on the open leaf or on GRH: if the mean square bound held, then with the same `C` and
`N0`, for every `N > max 1 N0`, every modulus `q ≤ N^(1/7)` and every nonprincipal
character mod `q`, the squared norm of the differentiated series at phase zero would be
at most `C N^2 (N/q) log^5 N`. Proof: divide the mean square bound by the phase length
and let the length tend to zero, using continuity of the series in the phase. -/
theorem near_sup357_derivative_moment357_forces_pointwise357
    (hX : ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            (∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2) ≤
              C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * (0 : ℝ) * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2 ≤
            C * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  obtain ⟨C, hC, N0, h⟩ := hX
  refine ⟨C, hC, max 1 N0, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hcont := near_sup357_derivative_series_continuous357 χ N hN1
  have hg : Continuous (fun β : ℝ => ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2) :=
    (hcont.norm).pow 2
  have ha : (0 : ℝ) < 4 / (N : ℝ) := by positivity
  refine near_sup357_value_le_of_integral_le357 (g := fun β : ℝ => ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2) hg ha ?_
  intro α hα0 hαu
  have h1 := h N hN0 q hq hqt χ hχ α hα0 hαu
  calc (∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2)
      ≤ C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := h1
    _ = C * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) * α := by ring

end LeanLab.Linnik1951
