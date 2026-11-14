/-
Split of `bv_remainder` from `Decomp506b` into its proof steps. The three leaves are the
distribution input for squarefree moduli at level `Y ^ (1 / 9)`, the logarithmic size of
that modulus range, and the large-`X` regime of the parameters. The assembly
`bv_remainder_split` has no sorry of its own: it is bookkeeping, converting the
modulus-weighted discrepancy sum into the unweighted sum inside `remainder` and paying
one logarithmic factor for it.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp506b

namespace LeanLab.KumchevLiu2007.Task506b

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Step 1 of the split, the distribution input. Fix `A`, `B` and `ε` in the local
range. Beyond a threshold, every `n` in `H2` with `X < n ≤ X + Y ^ (1 - ε)` satisfies the
modulus-weighted discrepancy bound: the sum over squarefree moduli up to `Y ^ (1 / 9)` of
the local discrepancy of the semiprime progression count from its density times the prime
mass, weighted by `1 / (1 + log d)`, is at most a constant times the error scale at the
parameter `A + 1`. The extra weight and the smaller error are what the assembly pays back
with one logarithmic factor. -/
theorem weighted_modulus_discrepancy (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) ≤ C * errorScale X ε (A + 1) := by
  sorry

/-- LEAF: Step 2 of the split, the logarithmic size of the modulus range. With
`D = ⌊Y ^ (1 / 9)⌋` and `Y = X ^ (7 / 12 + ε / 2)`, every modulus `1 ≤ d ≤ D` has
`log d ≤ (8 / 81) log X`, so beyond a threshold `1 + log d ≤ 2 log X`. -/
theorem sieve_level_log_scale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX d hd1 hdD
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hL1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hDpos : (0 : ℝ) < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  have hdle : (d : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
    have h1 : (d : ℝ) ≤ (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hdD
    have h2 : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) := Nat.floor_le hDpos.le
    have h3 : Y X ε ^ (1 / 9 : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
      have hexp : (7 / 12 + ε / 2) * (1 / 9) ≤ 8 / 81 := by linarith
      calc Y X ε ^ (1 / 9 : ℝ) = (X ^ (7 / 12 + ε / 2)) ^ (1 / 9 : ℝ) := rfl
        _ = X ^ ((7 / 12 + ε / 2) * (1 / 9)) := (Real.rpow_mul hX0.le _ _).symm
        _ ≤ X ^ (8 / 81 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hexp
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hlogd : Real.log (d : ℝ) ≤ 8 / 81 * Real.log X := by
    have h := Real.log_le_log hdpos hdle
    rwa [Real.log_rpow hX0] at h
  nlinarith

/-- LEAF: Step 3 of the split, the large-`X` regime of the parameters. Beyond a threshold
`log X ≥ 1`, the ninth power of the window `Y` is at least one, and the error scale at the
parameter `A` is nonnegative. These are the side conditions the assembly uses at every `X`
in the range. -/
theorem sieve_regime (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hlog1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hY1 : 1 ≤ Y X ε := by
    unfold Y
    exact Real.one_le_rpow hX1 (by linarith)
  have hY0 : 0 < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  refine ⟨hlog1, Real.one_le_rpow hY1 (by norm_num), ?_⟩
  unfold errorScale
  have h1 : 0 ≤ Y X ε ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hY1)) _
  have h2 : 0 ≤ Real.log X ^ (-A) :=
    le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog1) _)
  exact mul_nonneg h1 h2

/-- Split of `bv_remainder`: the explicit squarefree remainder at level `Y ^ (1 / 9)` is at
most a constant times `Y ^ (1 / 2) * (log X) ^ (-A)`, from the three leaves above and the
definition of `remainder`. -/
theorem bv_remainder_split (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨Cw, Xw, hCw, hw⟩ := weighted_modulus_discrepancy A B ε hA hB hε hε1
  obtain ⟨Xl, hXl, hl⟩ := sieve_level_log_scale ε hε hε1
  obtain ⟨Xr, hXr, hr⟩ := sieve_regime A ε hA hε
  refine ⟨2 * Cw, max Xw (max Xl Xr), by linarith, ?_⟩
  intro X hX n hn hXn hnle
  have hXw : Xw ≤ X := (le_max_left _ _).trans hX
  have hrest : max Xl Xr ≤ X := (le_max_right _ _).trans hX
  have hXl' : Xl ≤ X := (le_max_left _ _).trans hrest
  obtain ⟨hlog1, hY1, hE0⟩ := hr X ((le_max_right _ _).trans hrest)
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlog1
  have hw' := hw X hXw n hn hXn hnle
  unfold remainder
  have hstep : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| ≤
        (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hwpos : 0 < 1 + Real.log (d : ℝ) := by
      have hnn := Real.log_nonneg hd1R
      linarith
    have hwle : 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := hl X hXl' d hd1 hdD
    have hu : 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ)) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hwpos.le
    calc (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
        = ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (1 + Real.log (d : ℝ)) :=
          (div_mul_cancel₀ _ hwpos.ne').symm
      _ ≤ ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left hwle hu
      _ = (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by rw [mul_comm]
  calc ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ))) := Finset.sum_le_sum hstep
    _ = (2 * Real.log X) * ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.log X) * (Cw * errorScale X ε (A + 1)) :=
        mul_le_mul_of_nonneg_left hw' (by linarith)
    _ = 2 * Cw * errorScale X ε A := by
        unfold errorScale
        have hkey : Real.log X * Real.log X ^ (-(A + 1)) = Real.log X ^ (-A) := by
          rw [show (-A : ℝ) = 1 + -(A + 1) by ring, Real.rpow_add hL, Real.rpow_one]
        calc (2 * Real.log X) * (Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + 1))))
            = 2 * Cw * (Real.log X * Real.log X ^ (-(A + 1))) * Y X ε ^ (1 / 2 : ℝ) := by
              ring
          _ = 2 * Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
              rw [hkey]; ring

end LeanLab.KumchevLiu2007.Task506b
