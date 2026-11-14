/-
Split of `oscillatory_zero_modes508`. The single retained zero mode is bounded in the two
frequency regimes `|β| X ≤ 1` and `1 ≤ |β| X`, and the zero list is counted with reciprocal
weights. Each LEAF carries one open input; the assembly
`oscillatory_zero_modes508_split` restates the sealed estimate and uses no `sorry`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp508a

namespace LeanLab.BhowmikGrimmelt2026

/-- The retained zero modes written as a sum of single-mode Abel expressions. -/
private theorem zeroTwist508_unfold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (X : ℕ) (β : ℝ) :
    zeroTwist508 χ Z X β =
      ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))) := rfl

/-- LEAF: one retained zero mode, small frequency regime. For a single `ρ` with
`0 < ρ.re ≤ Θ` and `|β| X ≤ 1` the Abel expression of that mode, which is the difference
between the endpoint term and the summed phase increments, is at most `8 X^Θ / ‖ρ‖`.
This is the summation by parts step for one mode only. OPEN. -/
theorem zero_mode_small_frequency508 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) {β : ℝ} (hβ : |β| * (X : ℝ) ≤ 1) :
    ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ := by
  have hX1' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  have hd : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hnorm_pow : ∀ n : ℕ, ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ ρ.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.cast_zero, Complex.zero_cpow hρne]
      simpa using (Real.zero_rpow (ne_of_gt hρ0)).symm
    · rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  have hstep : ∀ n : ℕ,
      ‖ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
    intro n
    rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring, ee_add150]
    rw [show ee ((n : ℝ) * β) * ee β - ee ((n : ℝ) * β) = ee ((n : ℝ) * β) * (ee β - 1) by ring,
      norm_mul, norm_ee150, one_mul]
    exact norm_ee_sub_one_le502 β
  have hterm : ∀ n ∈ Finset.range X,
      ‖(n : ℂ) ^ ρ / ρ * (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
        (X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|) := by
    intro n hn
    have hnX : (n : ℝ) ≤ (X : ℝ) := by
      have hlt : n < X := Finset.mem_range.mp hn
      exact_mod_cast le_of_lt hlt
    have hpow : (n : ℝ) ^ ρ.re ≤ (X : ℝ) ^ ρ.re :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (le_of_lt hρ0)
    have hdiv : (n : ℝ) ^ ρ.re / ‖ρ‖ ≤ (X : ℝ) ^ ρ.re / ‖ρ‖ :=
      (div_le_div_iff_of_pos_right hd).mpr hpow
    rw [norm_mul, norm_div, hnorm_pow n]
    exact mul_le_mul hdiv (hstep n) (norm_nonneg _) (by positivity)
  have hkey : (X : ℝ) ^ ρ.re / ‖ρ‖ +
      (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ := by
    have hbX : (X : ℝ) * (2 * Real.pi * |β|) ≤ 2 * Real.pi := by
      have h1 : (X : ℝ) * (2 * Real.pi * |β|) = 2 * Real.pi * (|β| * (X : ℝ)) := by ring
      rw [h1]
      nlinarith [Real.pi_pos]
    have hconst : (1 : ℝ) + 2 * Real.pi ≤ 8 := by
      have := Real.pi_lt_d2
      linarith
    have hXσΘ : (X : ℝ) ^ ρ.re ≤ (X : ℝ) ^ Θ :=
      Real.rpow_le_rpow_of_exponent_le hX1' hρΘ
    have hmul : (X : ℝ) ^ ρ.re * (1 + 2 * Real.pi) ≤ (X : ℝ) ^ Θ * 8 :=
      mul_le_mul hXσΘ hconst (by positivity) (by positivity)
    have heq : (X : ℝ) ^ ρ.re / ‖ρ‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) =
        ((X : ℝ) ^ ρ.re * (1 + (X : ℝ) * (2 * Real.pi * |β|))) / ‖ρ‖ := by
      field_simp
    rw [heq, show 8 * (X : ℝ) ^ Θ / ‖ρ‖ = ((X : ℝ) ^ Θ * 8) / ‖ρ‖ by ring]
    refine (div_le_div_iff_of_pos_right hd).mpr ?_
    calc (X : ℝ) ^ ρ.re * (1 + (X : ℝ) * (2 * Real.pi * |β|)) ≤
        (X : ℝ) ^ ρ.re * (1 + 2 * Real.pi) := by
          have hp : (0 : ℝ) ≤ (X : ℝ) ^ ρ.re := Real.rpow_nonneg (Nat.cast_nonneg X) _
          nlinarith
      _ ≤ (X : ℝ) ^ Θ * 8 := hmul
  refine (norm_sub_le _ _).trans ?_
  calc ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β)‖ +
        ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖
      ≤ ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β)‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
        have hB : ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
            (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact add_le_add (le_refl _) hB
    _ = (X : ℝ) ^ ρ.re / ‖ρ‖ +
        (X : ℝ) * ((X : ℝ) ^ ρ.re / ‖ρ‖ * (2 * Real.pi * |β|)) := by
        rw [norm_mul, norm_div, hnorm_pow X, norm_ee150, mul_one]
    _ ≤ 8 * (X : ℝ) ^ Θ / ‖ρ‖ := hkey

/-- LEAF: one retained zero mode, large frequency regime. For a single `ρ` with
`0 < ρ.re ≤ Θ` and `1 ≤ |β| X` the same Abel expression of that mode is at most
`8 X^Θ / ‖ρ‖` times the frequency factor `sqrt (|β| X)`. OPEN. -/
theorem zero_mode_large_frequency508 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) {β : ℝ} (hβ : 1 ≤ |β| * (X : ℝ)) :
    ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (|β| * (X : ℝ)) := by
  sorry

/-- LEAF: the zero list counted with multiplicity and reciprocal weight. For every `ε > 0`
the sum of `mult χ ρ / ‖ρ‖` over the zeros of `L (χ, ·)` in the open critical strip up to
height `T` is at most a constant times `X^ε`, uniformly in `X`, `q ≤ sqrt X`, `χ`, `T` and
the listed zero set. OPEN. -/
theorem zero_reciprocal_multiplicity508 (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X →
      ∀ χ : DirichletCharacter ℂ q, ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ ≤ K * (X : ℝ) ^ ε := by
  sorry

/-- The sealed sharp oscillatory zero mode estimate, assembled from the three LEAF steps. -/
theorem oscillatory_zero_modes508_split (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := zero_reciprocal_multiplicity508 ε hε
  refine ⟨8 * K, by positivity, ?_⟩
  intro X hX2 q _ hqQ χ T hT Z hZset β hβ
  have hX1 : 1 ≤ X := by omega
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hΘ1 : 1 / 2 ≤ Θ := zeroBound_lower150 hZ
  have hS1 : (1 : ℝ) ≤ Real.sqrt (1 + |β| * (X : ℝ)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
  have hKsum := hK X hX2 q hqQ χ T hT Z hZset
  have hterm : ∀ ρ ∈ Z,
      ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ ≤
      (mult χ ρ : ℝ) *
        (8 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) := by
    intro ρ hρ
    obtain ⟨hz, h0, h1, _him⟩ := (hZset ρ).mp hρ
    have hρΘ : ρ.re ≤ Θ := hZ q χ ρ hz h0 h1
    have hnn : (0 : ℝ) ≤ 8 * (X : ℝ) ^ Θ / ‖ρ‖ := by positivity
    have hmode : ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
        8 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ)) := by
      rcases le_total (|β| * (X : ℝ)) 1 with hs | hl
      · refine (zero_mode_small_frequency508 hΘ1 hX1 h0 hρΘ hs).trans ?_
        nlinarith [hnn, hS1]
      · refine (zero_mode_large_frequency508 hΘ1 hX1 h0 hρΘ hl).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by linarith)) hnn
    calc ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
        = (mult χ ρ : ℝ) * ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
            ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
              (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ (mult χ ρ : ℝ) *
            (8 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hmode (by positivity)
  rw [zeroTwist508_unfold]
  calc ‖∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖
      ≤ ∑ ρ ∈ Z, ‖(mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
          ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
            (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (mult χ ρ : ℝ) *
          (8 * (X : ℝ) ^ Θ / ‖ρ‖ * Real.sqrt (1 + |β| * (X : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 8 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) *
          ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
    _ ≤ 8 * (X : ℝ) ^ Θ * Real.sqrt (1 + |β| * (X : ℝ)) * (K * (X : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left hKsum (by positivity)
    _ = 8 * K * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * (X : ℝ)) := by
        rw [Real.rpow_add hXp]
        ring

end LeanLab.BhowmikGrimmelt2026
