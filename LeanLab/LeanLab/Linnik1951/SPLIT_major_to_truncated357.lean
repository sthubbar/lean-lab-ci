/-
DEAD SPLIT. Unit U-1622, 2026-11-06. Do not work on major_error_remainder357.
Reason: for k at least 3 the term C N over log N is below epsilon over 2 times scale, so
major_error_remainder357 is the parent relabelled. Its two other leaves are real analysis.
The parameter tau equal to N to the 1/7 in majorArcs280 is correct: pages 165 and 166 of the
original scan print it. The translation P0093.txt misreads it as N to the 1/2.
Live route: major_expansion_remainder376 in Decomp376d, and its re-cut in SPLIT1622_major.
Statements below are unchanged. This file is not on the route of linnik1951_decomposed412.
-/
/-
Split of `major_to_truncated357` into three steps.  The target statement is
kept exactly as it stands in `Decomp357b`; `major_to_truncated357_split` below
states it character for character and derives it from the three OPEN leaves.

The shape of the split follows the one used for the neighbouring Mellin unit:
the analytic content is isolated in a single leaf that keeps the error term of
the major arc analysis but drops its logarithmic bookkeeping, and the two
remaining leaves are pure real-variable steps that turn a fixed additive error
into the demanded multiple of `scale111`.  Step 1 therefore carries an extra
nonnegative summand and is strictly weaker than the target; steps 2 and 3 are
elementary inequalities of the real line and contain no arithmetic.

Nothing here changes a statement, a definition or an import of `Decomp357b`.
-/
import LeanLab.Linnik1951.Decomp357b

namespace LeanLab.Linnik1951

/-- LEAF. Step 1 of 3: the major arc error with a crude additive tail.  For
every fixed exponent parameter at least three and every positive tolerance
there is a constant and a threshold beyond which the major arc contribution
differs from the truncated main term by at most the demanded fraction of the
scale plus the absolute tail with one factor of the logarithm only.  This is
the whole analytic content of the major arc expansion, exponent tuple counting
and geometric tail; it is weaker than the target because the tail summand is
nonnegative, and it is the step that has to be supplied by the sections on the
local prime square, the singular series and the counting of exponent tuples. -/
theorem major_error_remainder357 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε / 2 * scale111 k N + C * (N : ℝ) / Real.log N := by
  sorry

/-- LEAF. Step 2 of 3: growth of the logarithm against a constant.  For every
positive constant, every positive coefficient and every positive natural power
the logarithm of N raised to that power eventually dominates the constant.  No
arithmetic and no major arcs occur here; it is the real-variable statement that
supplies the pointwise hypothesis of step 3. -/
theorem log_power_dominates357 (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (p : ℕ) (hp : 0 < p) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → C ≤ δ * Real.log N ^ p := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ p) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by omega)
  have hmain : Filter.Tendsto (fun N : ℕ => Real.log N ^ p) Filter.atTop Filter.atTop :=
    hpow.comp hlog
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hmain.eventually_ge_atTop (C / δ))
  refine ⟨N0, fun N hN => ?_⟩
  have h1 : C / δ ≤ Real.log N ^ p := hN0 N (le_of_lt hN)
  rw [div_le_iff₀ hδ] at h1
  linarith

/-- LEAF. Step 3 of 3: the algebraic bookkeeping.  At a point N at least three,
a bound of the constant by a suitable positive multiple of the logarithm to the
power one less than the exponent parameter is exactly what is needed to turn
the crude additive tail of step 1 into the demanded multiple of the scale.
Both sides are positive here, because N is at least three forces the logarithm
of N to be positive, and the scale is the product of N with the exponent
parameter minus two power of the logarithmic ratio. -/
theorem major_absorption_algebra357 {k : ℕ} (hk : 3 ≤ k) (N : ℕ) (hN : 3 ≤ N)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h : C ≤ ε / 2 * Real.log N ^ (k - 1) / Real.log 2 ^ (k - 2)) :
    C * (N : ℝ) / Real.log N ≤ ε / 2 * scale111 k N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hL : 0 < Real.log N := Real.log_pos hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hkey : C / Real.log N ≤ ε / 2 * (Real.log N / Real.log 2) ^ (k - 2) := by
    rw [div_le_iff₀ hL]
    calc C ≤ ε / 2 * Real.log N ^ (k - 1) / Real.log 2 ^ (k - 2) := h
      _ = ε / 2 * (Real.log N / Real.log 2) ^ (k - 2) * Real.log N := by
          have hk2 : k - 1 = (k - 2) + 1 := by omega
          rw [hk2, pow_succ, div_pow]
          ring
  have hmul := mul_le_mul_of_nonneg_right hkey hNpos.le
  unfold scale111
  calc C * (N : ℝ) / Real.log N = C / Real.log N * (N : ℝ) := by ring
    _ ≤ ε / 2 * (Real.log N / Real.log 2) ^ (k - 2) * (N : ℝ) := hmul
    _ = ε / 2 * ((N : ℝ) * (Real.log N / Real.log 2) ^ (k - 2)) := by ring

/-- Assembly of `major_to_truncated357` from the three leaves above: take the
constant and the threshold of step 1, feed the constant into the growth of the
logarithm of step 2 with coefficient half of the tolerance over the logarithm
of two to the exponent parameter minus two, and absorb the additive tail into
the scale with step 3.  The triangle step is the single line
`abs_sub_le`-free comparison: the bound of step 1 is already the difference
itself, so only the addition of the two halves of the tolerance remains, and
`scale111` has to be nonnegative there.  No step uses `major_to_truncated357`
itself. -/
theorem major_to_truncated357_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280)
    (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
      |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N| ≤
        ε * scale111 k N := by
  obtain ⟨C, hC, Nc, hc⟩ := major_error_remainder357 hG hM k hk ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log 2 ^ (k - 2) := pow_pos hlog2 (k - 2)
  have hδ : 0 < ε / 2 / Real.log 2 ^ (k - 2) := by positivity
  obtain ⟨Nl, hl⟩ := log_power_dominates357 C (ε / 2 / Real.log 2 ^ (k - 2)) hC hδ
    (k - 1) (by omega)
  refine ⟨max (max Nc Nl) 3, ?_⟩
  intro N hev hN
  have hup : max Nc Nl ≤ max (max Nc Nl) 3 := le_max_left _ _
  have hNc : Nc < N := lt_of_le_of_lt (le_trans (le_max_left _ _) hup) hN
  have hNl : Nl < N := lt_of_le_of_lt (le_trans (le_max_right _ _) hup) hN
  have h3 : 3 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hbridge : C * (N : ℝ) / Real.log N ≤ ε / 2 * scale111 k N := by
    refine major_absorption_algebra357 hk N h3 hC hε ?_
    have heq : ε / 2 / Real.log 2 ^ (k - 2) * Real.log N ^ (k - 1) =
        ε / 2 * Real.log N ^ (k - 1) / Real.log 2 ^ (k - 2) := by ring
    rw [← heq]
    exact hl N hNl
  calc |arcContribution280 k N (majorArcs280 N) - truncatedMain357 k N|
      ≤ ε / 2 * scale111 k N + C * (N : ℝ) / Real.log N := hc N hev hNc
    _ ≤ ε / 2 * scale111 k N + ε / 2 * scale111 k N := by linarith
    _ = ε * scale111 k N := by ring

end LeanLab.Linnik1951
