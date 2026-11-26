import LeanLab.ExceptionalSet.SPLIT_leaf_inner_low_j0
import LeanLab.ExceptionalSet.DQLemma9Decisions

/-!
Split of `Decomp553a.leaf_low_j0_large_phase_localizes`, the localization of large
values of the assigned lower block phase, from `SPLIT_leaf_inner_low_j0`.

Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621, Lemma 9 page 368 and its proof in
section 7 page 370, displays 40 and 41, with Theorem 2 as the exponential sum input.

The localization is the lab form of Lemma 9 for the block `low_j0`: the lower half
`n ≤ 3N/4` of `(N/2, N]` with `⌊F(n)⌋` even. Its proof has two steps.

  * Display 40 and 41: the parity condition is removed by the trapezoid Fourier
    expansion and Lemma 4, so a large block phase forces a large unrestricted phase
    `Σ e((t - h/2) F(n))` over the same sub-block, with `|h| ≤ ℰ^2`.
  * Theorem 2 on the sub-block: away from `X^{δ-1}` and below `3 ℰ^2`, the
    unrestricted phase over the sub-block is at most `N ℰ^{-2}`.

The assembly is the closing contradiction of page 370. AI wrote the Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553a

open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-- LEAF: P0082 page 370 displays 40 and 41, proof of Lemma 9, the removal of the
parity condition on the assigned lower block. HARD. The indicator of `⌊F(n)⌋` even is
replaced by the trapezoid function `Υ(F(n)/2)` with Fourier coefficients
`c_h ≪ min(A, A^{-1} h^{-2})`; Lemma 4 with `α = 1/2` bounds the `n` of `(N/2, N]` where
the two differ, the tail `|h| > ℰ^2` is removed by the coefficient bound, and the
remaining sum over `|h| ≤ ℰ^2` has total coefficient mass `≪ A^{-1/2}`. With
`A ≍ ℰ^{-5/6}` a block phase above `N ℰ^{-5/6}` forces some unrestricted shifted phase
over the sub-block `n ≤ 3N/4` above `N ℰ^{-2}`. -/
theorem leaf_low_j0_parity_shift (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
        |t| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) →
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
            ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) t‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 : ℝ) ∧
            (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) <
              ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC ((t - (h : ℝ) / 2) * F γ n)‖ := by
  exact DQLemma9.large_value_shift_of_lemma4 (γ := γ) h1 h2

/-- LEAF: P0082 Theorem 2 page 354 with its proof in section 8 from Karacuba's
Lemma 10 page 370, applied on the sub-block `N/2 < n ≤ 3N/4` as used on page 370 after
display 41. HARD. For `X^{δ-1} < |β| ≤ 3 ℰ^2`, a range inside the range
`F(2N)^{-c} ≤ |β| ≤ F(N)^C` of Theorem 2, the unrestricted phase
`Σ e(β F(n))` over the sub-block is at most `N ℰ^{-2}` once `κ` is small. -/
theorem leaf_low_j0_subblock_theorem2 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
          F γ N ^ (δ - 1) < |β| → |β| ≤ 3 * calE γ κ N ^ (2 : ℝ) →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC (β * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) := by
  sorry

/-- `ℰ ≥ 1` for `κ ≥ 0`, since `log N ≥ 0`. Proved helper. -/
theorem feed1122_low_j0_calE_one_le (γ κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ) :
    1 ≤ calE γ κ N := by
  unfold U1539.calE
  exact Real.one_le_exp (mul_nonneg hκ (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))

/-- Assembly, page 370 closing argument of the proof of Lemma 9. Statement copied
verbatim from `leaf_low_j0_large_phase_localizes`. -/
theorem leaf_low_j0_large_phase_localizes_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  obtain ⟨κS, hκS, hS⟩ := leaf_low_j0_parity_shift γ h1 h2
  obtain ⟨δT, hδT, hT⟩ := leaf_low_j0_subblock_theorem2 γ h1 h2
  refine ⟨δT, hδT, fun δ hδ hδs => ?_⟩
  obtain ⟨κT, hκT, hT⟩ := hT δ hδ hδs
  refine ⟨min κS κT, lt_min hκS hκT, fun κ hκ hκs => ?_⟩
  obtain ⟨NS, hS⟩ := hS κ hκ (hκs.trans (min_le_left _ _))
  obtain ⟨NT, hT⟩ := hT κ hκ (hκs.trans (min_le_right _ _))
  refine ⟨max NS NT, fun N hN a ha b hb hlarge => ?_⟩
  have hNS : NS ≤ N := (le_max_left _ _).trans hN
  have hNT : NT ≤ N := (le_max_right _ _).trans hN
  have hE1 := feed1122_low_j0_calE_one_le γ κ hκ.le N
  have hba : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
    have hb1 : b ≤ calE γ κ N ^ (2 / 3 : ℝ) := hb.2.2
    have hb2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ b := hb.2.1
    have ha1 : a ≤ calE γ κ N ^ (2 / 3 : ℝ) := ha.2.2
    have ha2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ a := ha.2.1
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨h, hh, hbig⟩ := hS N hNS (b - a) hba hlarge
  refine ⟨h, ?_⟩
  by_contra hfar'
  have hfar := not_le.mp hfar'
  have h23 : calE γ κ N ^ (2 / 3 : ℝ) ≤ calE γ κ N ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hE2 : 0 ≤ calE γ κ N ^ (2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hrange : |(b - a) - (h : ℝ) / 2| ≤ 3 * calE γ κ N ^ (2 : ℝ) := by
    have hh' : |(h : ℝ) / 2| ≤ calE γ κ N ^ (2 : ℝ) / 2 := by
      rw [abs_div, abs_two]; linarith
    calc |(b - a) - (h : ℝ) / 2| ≤ |b - a| + |(h : ℝ) / 2| := abs_sub _ _
      _ ≤ 3 * calE γ κ N ^ (2 : ℝ) := by linarith
  have hsmall := hT N hNT ((b - a) - (h : ℝ) / 2) hfar hrange
  linarith

end LeanLab.ExceptionalSet.Decomp553a
