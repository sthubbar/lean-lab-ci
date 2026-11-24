/-
Split of `oscillatory_zero_modes508`. The single retained zero mode is bounded in the two
frequency regimes `|β| X ≤ 1` and `1 ≤ |β| X`, and the zero list is counted with reciprocal
weights. Each LEAF carries one open input; the assembly
`oscillatory_zero_modes508_F1255` restates the sealed estimate and uses no `sorry`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp508a
import LeanLab.BhowmikGrimmelt2026.LEAF_feed1122_zero_reciprocal508

namespace LeanLab.BhowmikGrimmelt2026

/-- The retained zero modes written as a sum of single-mode Abel expressions. -/
private theorem zeroTwist508_unfold_F1255 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : Finset ℂ) (X : ℕ) (β : ℝ) :
    zeroTwist508 χ Z X β =
      ∑ ρ ∈ Z, (mult χ ρ : ℂ) * ((X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))) := rfl

/-- The phase increment of one step factors the frequency out. -/
private theorem ee_shift_F1255 (n : ℕ) (β : ℝ) :
    ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β) =
      ee ((n : ℝ) * β) * (ee β - 1) := by
  rw [show (((n + 1 : ℕ) : ℝ) * β) = (n : ℝ) * β + β by push_cast; ring, ee_add150]
  ring

/-- The Abel expression of one zero mode with the phase increment `e(β) - 1` factored out. -/
private theorem zero_mode_abel_form_F1255 {ρ : ℂ} (hρ : ρ ≠ 0) (X : ℕ) (β : ℝ) :
    (X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) =
      ((X : ℂ) ^ ρ * ee ((X : ℝ) * β) -
        (ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)) / ρ := by
  have hsum : ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
        (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β)) =
      (ee β - 1) * (∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)) / ρ := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ee_shift_F1255 n β]
    ring
  rw [hsum]
  ring

/-- The norm of a natural number raised to a complex power of positive real part. -/
private theorem norm_natCast_cpow_F1255 {ρ : ℂ} (hρ0 : 0 < ρ.re) (n : ℕ) :
    ‖(n : ℂ) ^ ρ‖ = (n : ℝ) ^ ρ.re := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.cast_zero, Complex.zero_cpow hρne]
    simpa using (Real.zero_rpow (ne_of_gt hρ0)).symm
  · rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]

/-- LEAF: one retained zero mode, small frequency regime. For a single `ρ` with
`0 < ρ.re ≤ Θ` and `|β| X ≤ 1` the Abel expression of that mode is at most
`8 X^Θ / ‖ρ‖`. This is the summation by parts step for one mode only. OPEN. -/
theorem zero_mode_small_frequency508_F1255 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρΘ : ρ.re ≤ Θ) {β : ℝ} (hβ : |β| * (X : ℝ) ≤ 1) :
    ‖(X : ℂ) ^ ρ / ρ * ee ((X : ℝ) * β) -
        ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ / ρ *
          (ee (((n + 1 : ℕ) : ℝ) * β) - ee ((n : ℝ) * β))‖ ≤
      8 * (X : ℝ) ^ Θ / ‖ρ‖ := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h] at hρ0
    simp at hρ0
  have hd : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXσ0 : 0 ≤ (X : ℝ) ^ ρ.re := Real.rpow_nonneg (by linarith) _
  have hXΘ0 : 0 ≤ (X : ℝ) ^ Θ := Real.rpow_nonneg (by linarith) _
  have hXσΘ : (X : ℝ) ^ ρ.re ≤ (X : ℝ) ^ Θ :=
    Real.rpow_le_rpow_of_exponent_le hXr hρΘ
  have hπ : (1 : ℝ) + 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_d2]
  rw [zero_mode_abel_form_F1255 hρne X β]
  have hsum : ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖
      ≤ (X : ℝ) * (X : ℝ) ^ ρ.re := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n ∈ Finset.range X,
        ‖(n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ ≤ (X : ℝ) ^ ρ.re := by
      intro n hn
      rw [norm_mul, norm_ee150, mul_one, norm_natCast_cpow_F1255 hρ0]
      exact Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast (Finset.mem_range.mp hn).le) hρ0.le
    refine (Finset.sum_le_sum hterm).trans ?_
    simp
  have hnumer : ‖(X : ℂ) ^ ρ * ee ((X : ℝ) * β) -
        (ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖
      ≤ (1 + 2 * Real.pi) * (X : ℝ) ^ ρ.re := by
    have h1 : ‖(X : ℂ) ^ ρ * ee ((X : ℝ) * β)‖ = (X : ℝ) ^ ρ.re := by
      rw [norm_mul, norm_ee150, mul_one, norm_natCast_cpow_F1255 hρ0]
    have h2 : ‖(ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖
        ≤ 2 * Real.pi * (X : ℝ) ^ ρ.re := by
      rw [norm_mul]
      calc ‖ee β - 1‖ * ‖∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖
          ≤ (2 * Real.pi * |β|) * ((X : ℝ) * (X : ℝ) ^ ρ.re) := by
            refine mul_le_mul (norm_ee_sub_one_le502 β) hsum (norm_nonneg _)
              (by positivity)
        _ = 2 * Real.pi * (|β| * (X : ℝ)) * (X : ℝ) ^ ρ.re := by ring
        _ ≤ 2 * Real.pi * 1 * (X : ℝ) ^ ρ.re := by
            refine mul_le_mul_of_nonneg_right ?_ hXσ0
            refine mul_le_mul_of_nonneg_left hβ (by positivity)
        _ = 2 * Real.pi * (X : ℝ) ^ ρ.re := by ring
    calc ‖(X : ℂ) ^ ρ * ee ((X : ℝ) * β) -
          (ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖
        ≤ ‖(X : ℂ) ^ ρ * ee ((X : ℝ) * β)‖ +
            ‖(ee β - 1) * ∑ n ∈ Finset.range X, (n : ℂ) ^ ρ * ee ((n : ℝ) * β)‖ :=
          norm_sub_le _ _
      _ ≤ (X : ℝ) ^ ρ.re + 2 * Real.pi * (X : ℝ) ^ ρ.re := by
          rw [h1]; linarith
      _ = (1 + 2 * Real.pi) * (X : ℝ) ^ ρ.re := by ring
  rw [norm_div]
  refine (div_le_div_of_nonneg_right hnumer hd.le).trans ?_
  apply div_le_div_of_nonneg_right _ hd.le
  calc (1 + 2 * Real.pi) * (X : ℝ) ^ ρ.re ≤ 8 * (X : ℝ) ^ ρ.re :=
        mul_le_mul_of_nonneg_right hπ hXσ0
    _ ≤ 8 * (X : ℝ) ^ Θ := mul_le_mul_of_nonneg_left hXσΘ (by norm_num)

/-- LEAF: one retained zero mode, large frequency regime. For a single `ρ` with
`0 < ρ.re ≤ Θ` and `1 ≤ |β| X` the same Abel expression of that mode is at most
`8 X^Θ / ‖ρ‖` times the frequency factor `sqrt (|β| X)`. OPEN. -/
theorem zero_mode_large_frequency508_F1255 {Θ : ℝ} (hΘ1 : 1 / 2 ≤ Θ) {X : ℕ} (hX : 1 ≤ X)
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
theorem zero_reciprocal_multiplicity508_F1255 (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X →
      ∀ χ : DirichletCharacter ℂ q, ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∑ ρ ∈ Z, (mult χ ρ : ℝ) / ‖ρ‖ ≤ K * (X : ℝ) ^ ε := by
  exact zero_reciprocal_multiplicity508_from_leaves ε hε

/-- The sealed sharp oscillatory zero mode estimate, assembled from the three LEAF steps. -/
theorem oscillatory_zero_modes508_F1255 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := zero_reciprocal_multiplicity508_F1255 ε hε
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
      · refine (zero_mode_small_frequency508_F1255 hΘ1 hX1 h0 hρΘ hs).trans ?_
        nlinarith [hnn, hS1]
      · refine (zero_mode_large_frequency508_F1255 hΘ1 hX1 h0 hρΘ hl).trans ?_
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
  rw [zeroTwist508_unfold_F1255]
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
