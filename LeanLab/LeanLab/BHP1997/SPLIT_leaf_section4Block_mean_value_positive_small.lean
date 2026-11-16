/-
Split of `leaf_section4Block_mean_value_positive_small` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value.
The sealed statement stays exactly as it is and this file never uses it.

That leaf fixes one sign of the height and one exponent region, and it bounds one integral
in `t`. The integral runs from the level `exp (log x ^ (1/3))` up to the level
`x ^ (0.45 - 2 ε / 3)`. This split cuts that single integral at the intermediate level
`x ^ (1/4)`, which lies between the two ends once `x` is large, into the lower piece and
the upper piece. Each piece is again an upper bound for a norm integral of the same
Dirichlet polynomial, only over a shorter range of `t`, so each piece is strictly easier
than the sealed leaf; the sealed leaf needs the whole range with one pair of constants.
The assembly adds the two constants, raises the threshold so that `x` also exceeds
`exp 16` (which puts `x ^ (1/4)` between the two ends) and uses additivity of the
integral over adjacent intervals together with the triangle inequality.

Every leaf is OPEN. A family that vanishes identically meets every hypothesis and every
conclusion of both leaves, so neither is vacuous. The hypothesis `h4` and the bound `hB`
are carried unchanged from the sealed statement, as they are there.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF 1 of 2. The mean value over the lower half of the height range: from the level
`exp (log x ^ (1/3))` only up to the intermediate level `x ^ (1/4)`. Everything else is
the sealed claim unchanged, so this is an upper bound for a norm integral over a strictly
shorter range of `t`. Non-vacuous: the vanishing family meets it. -/
theorem leaf_section4Block_mean_value_positive_small_low
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (1 / 4 : ℝ)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 2. The mean value over the upper half of the height range: from the
intermediate level `x ^ (1/4)` up to the sealed upper end `x ^ (0.45 - 2 ε / 3)`.
Everything else is the sealed claim unchanged, so this is an upper bound for a norm
integral over a strictly shorter range of `t`, and it is a separate integral from leaf 1,
not implied by it. Non-vacuous: the vanishing family meets it. -/
theorem leaf_section4Block_mean_value_positive_small_high
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (x ^ (1 / 4 : ℝ))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- The lower end of the height range stays below `x ^ (1/4)` once `x ≥ exp 16`:
the exponent `log x ^ (1/3)` is at most `log x / 4` from `log x ≥ 16`, and
`exp (log x / 4)` is `x ^ (1/4)`. -/
private lemma exp_rpow_le_quarter {x : ℝ} (hx : Real.exp 16 ≤ x) :
    Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 4 : ℝ) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 16) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have ht16 : 16 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 16) hx
    rwa [Real.log_exp] at h
  have ht1 : 1 ≤ Real.log x := by linarith
  have hsqrt : Real.log x ^ (1 / 2 : ℝ) ≤ Real.log x / 4 := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ Real.log x / 4)]
    nlinarith
  have hstep : Real.log x ^ (1 / 3 : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hkey : Real.log x ^ (1 / 3 : ℝ) ≤ Real.log x / 4 := le_trans hstep hsqrt
  rw [Real.rpow_def_of_pos hxpos,
    show Real.log x * (1 / 4 : ℝ) = Real.log x / 4 from by ring]
  exact Real.exp_le_exp.mpr hkey

/-- The intermediate level `x ^ (1/4)` stays below the upper end `x ^ (0.45 - 2 ε / 3)`
once `ε < 1/4`, because then `1/4 ≤ 0.45 - 2 ε / 3` and the base `x` is at least one. -/
private lemma rpow_quarter_le_upper {x : ℝ} {ε : ℝ} (hx1 : 1 ≤ x) (hε : ε < 1 / 4) :
    x ^ (1 / 4 : ℝ) ≤ x ^ (0.45 - 2 * ε / 3) := by
  apply Real.rpow_le_rpow_of_exponent_le hx1
  linarith

/-- The height exponent written with a real half, so that its real part is visible and
can be seen to be nonzero. That nonzero is what the continuity of the factor into the
`t` power needs. -/
private lemma half_eq (t : ℝ) : Thm4.half t = ((1 / 2 : ℝ) : ℂ) + ↑t * Complex.I := by
  simp only [Thm4.half]
  push_cast
  ring

private lemma half_ne_zero (t : ℝ) : Thm4.half t ≠ 0 := by
  rw [half_eq]
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved from
the two leaves above and never from the sealed leaf. The threshold is the smaller of the
two leaves and `1/4`, raised so that `x ≥ exp 16`; the constant is the sum of the two
constants; the integral over the whole range is the sum of the two pieces by additivity
over adjacent intervals. -/
theorem leaf_section4Block_mean_value_positive_small_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η₁, hη₁, H₁⟩ := leaf_section4Block_mean_value_positive_small_low h4 B hB
  obtain ⟨η₂, hη₂, H₂⟩ := leaf_section4Block_mean_value_positive_small_high h4 B hB
  refine ⟨min (min η₁ η₂) (1 / 4), lt_min (lt_min hη₁ hη₂) (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hmn a b ha hb A hA
  have hε₁ : ε < η₁ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε₂ : ε < η₂ := hεη.trans_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε₃ : ε < 1 / 4 := hεη.trans_le (min_le_right _ _)
  obtain ⟨C₁, X₁, h1⟩ := H₁ ε hε hε₁ m n hm0 hn0 hmn a b ha hb A hA
  obtain ⟨C₂, X₂, h2⟩ := H₂ ε hε hε₂ m n hm0 hn0 hmn a b ha hb A hA
  refine ⟨C₁ + C₂, max (max X₁ X₂) (Real.exp 16), ?_⟩
  intro x hx q hq hlog χ
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx16 : Real.exp 16 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx16
  have hlow : Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 4 : ℝ) :=
    exp_rpow_le_quarter hx16
  have hhigh : x ^ (1 / 4 : ℝ) ≤ x ^ (0.45 - 2 * ε / 3) := rpow_quarter_le_upper hx1 hε₃
  have hcont : Continuous (fun t : ℝ =>
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half t‖) := by
    refine Continuous.norm ?_
    refine continuous_finsetSum _ (fun k hk => ?_)
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le ⌊x / 2⌋₊) (Finset.mem_Ioc.mp hk).1
    have hkC : (k : ℂ) ≠ 0 := by
      have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
      exact_mod_cast hkne
    have hden : Continuous (fun t : ℝ => (k : ℂ) ^ Thm4.half t) := by
      have hfun : (fun t : ℝ => (k : ℂ) ^ Thm4.half t) =
          fun t : ℝ => (k : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + ↑t * Complex.I) := by
        funext t
        rw [half_eq]
      rw [hfun]
      exact (continuous_const_cpow' hkC).comp (by fun_prop)
    exact Continuous.div continuous_const hden
      (fun t => (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (half_ne_zero t)).mpr hkC)
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half t‖) MeasureTheory.volume
      (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (1 / 4 : ℝ)) :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half t‖) MeasureTheory.volume
      (x ^ (1 / 4 : ℝ)) (x ^ (0.45 - 2 * ε / 3)) :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  calc (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (1 / 4 : ℝ)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖) +
      (∫ t in (x ^ (1 / 4 : ℝ))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖)
      ≤ C₁ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) + C₂ * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add (h1 x hxX₁ q hq hlog χ) (h2 x hxX₂ q hq hlog χ)
    _ = (C₁ + C₂) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Decomp528a
