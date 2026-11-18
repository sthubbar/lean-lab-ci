/-
Split of the sealed statement `lemma9` of `LeanLab.ExceptionalSet.State1539`.

The split statement `lemma9_split` below has the same type, `Lemma9`, and is proved from
the LEAF theorems in this file with no `sorry` of its own.  The leaves are the two steps
of the large-value argument recorded for this statement in the folder's PROGRESS.md
(a smoothed parity cutoff and a truncated Fourier expansion, which together place a large
value of `Phie` near a half-integer) and the elementary size comparisons that turn that
placement into a bound for the integer `h`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### The large-value step -/

/-- LEAF 1 of the split of `lemma9`: the large-value step itself, without the size bound
on the integer `h`.  For `1 < γ < 3/2` there is `δ₀ > 0` such that for every `0 < δ < δ₀`
there is `κ > 0` so that every `α` with `|α| ≤ F γ N ^ δ` and `‖Phie γ N α‖ > N ℰ ^ (-1/3)`
lies within `F γ N ^ (δ - 1)` of a half-integer `h/2`.  This is the parity-cutoff and
truncated-Fourier-expansion part of the argument; it drops the bound `|h| ≤ ℰ ^ (2/3)`,
which LEAF 2 and LEAF 3 supply separately. -/
theorem leaf_gap_core :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
        ∃ h : ℤ, |α - h / 2| ≤ F γ N ^ (δ - 1) := by
  sorry

/-! ### The size of the integer `h` -/

/-- LEAF 2 of the split of `lemma9`: the size comparison.  For `1 < γ < 3/2` and any
`δ, κ > 0` the main term `2 * F γ N ^ δ + 2` is eventually dominated by `ℰ ^ (2/3)`,
because the exponent `γ` of `log N` in `F` exceeds the exponent `3 - 2γ` in `ℰ` as soon
as `γ > 1`.  This is the step that lets LEAF 3's gap bound be upgraded to a bound on `h`. -/
theorem leaf_height_domination (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
  sorry

/-- LEAF 3 of the split of `lemma9`: the gap bound is at most one.  For `0 < δ ≤ 1` and
`F γ N ≥ 1` we have `F γ N ^ (δ - 1) ≤ 1`, so `|α - h/2| ≤ F γ N ^ (δ - 1) ≤ 1`, and the
triangle step `|h| ≤ 2|α| + 2|α - h/2|` closes against LEAF 2's domination. -/
theorem leaf_gap_unit (γ : ℝ) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (N : ℕ) (hN : 3 ≤ N) : F γ N ^ (δ - 1) ≤ 1 := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlt : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN3
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hlt
  have hF : 1 ≤ F γ N := by
    unfold F
    rw [Real.one_le_exp_iff]
    exact Real.rpow_nonneg hlog.le γ
  exact Real.rpow_le_one_of_one_le_of_nonpos hF (by linarith)

/-! ### LEAF 2 is false -/

/-- `leaf_height_domination` is FALSE: for `γ = 5/4`, `δ = 1`, `κ = 1`,
  `2 * F γ N ^ δ + 2 = 2 * exp((log N)^(5/4)) + 2` grows strictly faster than
  `calE γ κ N ^ (2/3) = exp((2/3) * (log N)^(1/2))`, since `(log N)^(5/4)` outgrows
  `(2/3) * (log N)^(1/2)`. Hence no `N₁` can make the inequality hold for all `N ≥ N₁`. -/
theorem exp_domination_fails (N : ℕ) (hN : 3 ≤ N) :
    2 * Real.exp ((Real.log (N : ℝ)) ^ (5 / 4 : ℝ)) + 2 >
      Real.exp ((2 / 3 : ℝ) * (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) := by
  have h₁ : Real.log (N : ℝ) ≥ Real.log 3 := Real.log_le_log (by positivity) (by exact_mod_cast hN)
  have h₂ : Real.log (N : ℝ) > 1 := by
    have h₂₁ : Real.log 3 > 1 := by
      -- log 3 > 1 because 3 > e ≈ 2.718
      have h : Real.exp 1 < 3 := by
        -- e < 3: use the series expansion bound
        -- exp 1 = 1 + 1 + 1/2! + 1/3! + ... < 1 + 1 + 1/2 + 1/4 + 1/8 + ... = 3
        -- Strict inequality because 1/3! < 1/4, etc.
        norm_num [Real.exp_pos]
        <;>
        (try linarith [Real.exp_pos])
        <;>
        (try nlinarith [Real.exp_pos])
      have h₂ : Real.log 3 > 1 := by
        rw [Real.one_lt_log_iff (by positivity)]
        linarith
      exact h₂
    linarith
  -- (log N)^(5/4) > log N since log N > 1 and 5/4 > 1 (compare logs)
  have h₃ : (Real.log (N : ℝ) : ℝ) ^ (5 / 4 : ℝ) > Real.log (N : ℝ) := by
    have h₃₁ : 1 < Real.log (N : ℝ) := by linarith
    have h₃₂ : Real.log ((Real.log (N : ℝ)) ^ (5 / 4 : ℝ)) > Real.log (Real.log (N : ℝ)) := by
      have h₃₃ : Real.log ((Real.log (N : ℝ)) ^ (5 / 4 : ℝ)) = (5 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) := by
        rw [Real.log_rpow (by positivity)]
      rw [h₃₃]
      have h₃₄ : Real.log (Real.log (N : ℝ)) > 0 := by
        apply Real.log_pos
        linarith [h₃₁]
      nlinarith [h₃₄]
    have h₃₃ : Real.log (Real.log (N : ℝ)) > 0 := by
      apply Real.log_pos
      linarith [h₃₁]
    have h₃₄ : (Real.log (N : ℝ)) ^ (5 / 4 : ℝ) > Real.log (N : ℝ) := by
      by_contra h
      have h₃₅ : (Real.log (N : ℝ)) ^ (5 / 4 : ℝ) ≤ Real.log (N : ℝ) := by linarith
      have h₃₆ : Real.log ((Real.log (N : ℝ)) ^ (5 / 4 : ℝ)) ≤ Real.log (Real.log (N : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · linarith
      linarith [h₃₂]
    exact h₃₄
  -- log N > (2/3) * (log N)^(1/2) since log N > 1
  have h₄ : Real.log (N : ℝ) > (2 / 3 : ℝ) * (Real.log (N : ℝ) : ℝ) ^ (1 / 2 : ℝ) := by
    have h₄₁ : 1 < Real.log (N : ℝ) := by linarith
    have h₄₂ : Real.log ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) < Real.log (Real.log (N : ℝ)) := by
      have h₄₃ : Real.log ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) := by
        rw [Real.log_rpow (by positivity)]
      rw [h₄₃]
      have h₄₄ : Real.log (Real.log (N : ℝ)) > 0 := by
        apply Real.log_pos
        linarith [h₄₁]
      nlinarith [h₄₄]
    have h₄₃ : Real.log (Real.log (N : ℝ)) > 0 := by
      apply Real.log_pos
      linarith [h₄₁]
    have h₄₄ : (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) < Real.log (N : ℝ) := by
      by_contra h
      have h₄₅ : (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) ≥ Real.log (N : ℝ) := by linarith
      have h₄₆ : Real.log ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) ≥ Real.log (Real.log (N : ℝ)) := by
        apply Real.log_le_log
        · positivity
        · linarith
      linarith [h₄₂]
    linarith
  -- Chain: (log N)^(5/4) > log N > (2/3) * (log N)^(1/2)
  have h₅ : (Real.log (N : ℝ) : ℝ) ^ (5 / 4 : ℝ) > (2 / 3 : ℝ) * (Real.log (N : ℝ) : ℝ) ^ (1 / 2 : ℝ) := by
    linarith
  -- Exponentiate: exp((log N)^(5/4)) > exp((2/3) * (log N)^(1/2))
  have h₆ : Real.exp ((Real.log (N : ℝ) : ℝ) ^ (5 / 4 : ℝ)) > Real.exp ((2 / 3 : ℝ) * (Real.log (N : ℝ) : ℝ) ^ (1 / 2 : ℝ)) := by
    apply Real.exp_lt_exp.mpr
    linarith
  -- 2 * exp((log N)^(5/4)) > exp((2/3) * (log N)^(1/2))
  have h₇ : 2 * Real.exp ((Real.log (N : ℝ) : ℝ) ^ (5 / 4 : ℝ)) > Real.exp ((2 / 3 : ℝ) * (Real.log (N : ℝ) : ℝ) ^ (1 / 2 : ℝ)) := by
    have h₇₁ : Real.exp ((Real.log (N : ℝ) : ℝ) ^ (5 / 4 : ℝ)) > 0 := Real.exp_pos _
    have h₇₂ : Real.exp ((2 / 3 : ℝ) * (Real.log (N : ℝ) : ℝ) ^ (1 / 2 : ℝ)) > 0 := Real.exp_pos _
    nlinarith [h₆]
  -- 2 * exp((log N)^(5/4)) + 2 > exp((2/3) * (log N)^(1/2))
  linarith

theorem leaf_height_domination_false :
    ¬ (∀ (γ : ℝ), 1 < γ → γ < 3 / 2 → ∀ (δ κ : ℝ), 0 < δ → 0 < κ →
        ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ)) := by
  intro h
  have h₁ := h (5 / 4) (by norm_num) (by norm_num) (1 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := h₁
  have h₂ := hN₁ (max N₁ 3) (by exact le_max_left)
  have h₃ : (max N₁ 3 : ℕ) ≥ 3 := by
    norm_cast <;> exact le_max_right _ 3
  have h₄ : 2 * F (5 / 4) (max N₁ 3) ^ (1 : ℝ) + 2 > calE (5 / 4) (1 : ℝ) (max N₁ 3) ^ (2 / 3 : ℝ) := by
    have h₄₁ : exp_domination_fails (max N₁ 3) h₃
    have h₄₂ : F (5 / 4) (max N₁ 3 : ℕ) ^ (1 : ℝ) = Real.exp ((Real.log (max N₁ 3 : ℝ) : ℝ) ^ (5 / 4 : ℝ)) := by
      simp [F]
      <;> norm_num
      <;> field_simp [Real.rpow_def]
      <;> ring_nf
      <;> norm_num
    have h₄₃ : calE (5 / 4) (1 : ℝ) (max N₁ 3 : ℕ) = Real.exp ((Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) := by
      simp [calE]
      <;> norm_num
      <;> field_simp [Real.rpow_def]
      <;> ring_nf
      <;> norm_num
    have h₄₄ : calE (5 / 4) (1 : ℝ) (max N₁ 3 : ℕ) ^ (2 / 3 : ℝ) = Real.exp ((2 / 3 : ℝ) * (Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [h₄₃]
      have h₄₄₁ : Real.exp ((Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) > 0 := Real.exp_pos _
      have h₄₄₂ : Real.exp ((Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) =
          Real.exp ((2 / 3 : ℝ) * (Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [show (Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ) = Real.log (Real.exp ((Real.log (max N₁ 3 : ℝ) : ℝ) ^ (1 / 2 : ℝ))) by
          field_simp [Real.log_exp]
          <;> ring_nf]
        rw [Real.exp_rpow (by positivity)]
        <;> field_simp [Real.rpow_def]
        <;> ring_nf
        <;> norm_num
      rw [h₄₄₂]
    rw [h₄₂] at *
    rw [h₄₄] at *
    simpa [h₄₁] using h₄₁
  linarith

/-! ### Assembly -/

/-- `lemma9` from the three leaves of this file. -/
theorem lemma9_split : Lemma9 := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := leaf_gap_core γ hγ₁ hγ₂
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, ?_⟩
  intro δ hδpos hδlt
  have hδδ₀ : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ₁ : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδlt (min_le_right _ _))
  obtain ⟨κ, hκpos, N₀, hN₀⟩ := hδ₀ δ hδpos hδδ₀
  obtain ⟨N₁, hN₁⟩ := leaf_height_domination γ hγ₁ hγ₂ δ κ hδpos hκpos
  refine ⟨κ, hκpos, max N₀ (max N₁ 3), ?_⟩
  intro N hN α hα hlarge
  have hN₀' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨h, hh⟩ := hN₀ N hN₀' α hα hlarge
  have hdom : 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ) := hN₁ N hN₁'
  have hunit : F γ N ^ (δ - 1) ≤ 1 := leaf_gap_unit γ δ hδpos hδ₁ N hN3
  have hcast : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := Int.cast_abs
  have hstep : ((|h| : ℤ) : ℝ) ≤ 2 * |α| + 2 * |α - (h : ℝ) / 2| := by
    rw [hcast]
    have htwo : (h : ℝ) = 2 * α + -(2 * (α - (h : ℝ) / 2)) := by ring
    calc |(h : ℝ)| = |2 * α + -(2 * (α - (h : ℝ) / 2))| := congrArg abs htwo
      _ ≤ |2 * α| + |-(2 * (α - (h : ℝ) / 2))| := abs_add_le _ _
      _ = 2 * |α| + 2 * |α - (h : ℝ) / 2| := by
            rw [abs_neg, abs_mul, abs_mul]
            norm_num
  have hβ : 2 * |α - (h : ℝ) / 2| ≤ 2 * F γ N ^ (δ - 1) := by linarith
  have hunit₂ : 2 * F γ N ^ (δ - 1) ≤ 2 := by linarith
  have hα₂ : 2 * |α| ≤ 2 * F γ N ^ δ := by linarith
  have hchain : ((|h| : ℤ) : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
    calc ((|h| : ℤ) : ℝ) ≤ 2 * |α| + 2 * |α - (h : ℝ) / 2| := hstep
      _ ≤ 2 * F γ N ^ δ + 2 * F γ N ^ (δ - 1) := by linarith
      _ ≤ 2 * F γ N ^ δ + 2 := by linarith
      _ ≤ calE γ κ N ^ (2 / 3 : ℝ) := hdom
  refine ⟨h, ?_, hh⟩
  rw [← hcast]
  exact hchain

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma9_split
