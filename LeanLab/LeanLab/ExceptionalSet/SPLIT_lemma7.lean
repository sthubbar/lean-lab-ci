/-
Split of `lemma7` of this folder into the steps of its proof in section 6: the two
halves of the second moment of the adjacent major arc coefficient over the window
`X/2 < F(n) <= X`, the one at `R1(nu_n)` and the one at its neighbour `R1(nu_n + 1)`,
and the finite Chebyshev step that turns a second moment into an exceptional count.

`lemma7_split` below states `Lemma7` unchanged and is assembled from the three leaves,
so it carries no `sorry` of its own. The two moment leaves are the two members of the
pair `nu_n, nu_n + 1`, one even and one odd, so each carries one parity branch of the
section 6 computation, at the main term `X/2` of one member. `leaf_count_of_deviation`
is the counting step after them and has no analysis in it.

Every leaf is strictly weaker than `Lemma7`: the moment leaves are each an inequality
about one half of the pair over the whole window and bound no cardinality, the counting
leaf bounds a cardinality without any moment at a specific size and holds for every
real sequence, and no leaf restates or assumes the target.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step of the proof, the first half of the second moment of section 6: for
`1 < γ < 3/2` the squared deviation of the real part of `R1(nu_n)` from the main term
`X/2 = F(γ,N)/2` is, summed over the window `X/2 < F(n) <= X` of `n <= 2N`, eventually
at most `B N X^2 calE(γ,κ,N)^(-17/60)`, for every small enough `δ` and every `κ` below
a positive cap. This is the branch of `nu_n` itself, an inequality about a sum of
squares over the window; it bounds no cardinality and so does not imply `Lemma7`.

Non-vacuity: the range `1 < γ < 3/2` is non-empty (`γ = 5/4`); the window may be empty,
in which case the sum is `0` and the right side is positive because `B > 0`; the
summand is a square, so it is nonnegative at every `N`, including `N = 0` and `N = 1`,
where `nu_n` and `R1` are both defined. -/
theorem leaf_moment_nu (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-- LEAF. Step of the proof, the second half of the second moment of section 6: the
same squared deviation, now of the real part of the neighbour `R1(nu_n + 1)` from the
main term `X/2 = F(γ,N)/2`, summed over the same window, is eventually at most
`B N X^2 calE(γ,κ,N)^(-17/60)`. `nu_n` and `nu_n + 1` are of opposite parity, so this
is the other parity branch of the pair in display 29/30 of section 6. Again an
inequality about a sum of squares over the window, with no cardinality in it.

Non-vacuity: as for the first half; the two leaves differ only in their neighbour, so
the pair `R1(nu_n) + R1(nu_n + 1)` of the lemma is the sum of the two leaves' terms
when both deviations are measured from `X/2`. -/
theorem leaf_moment_nu_succ (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
            (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
            ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(17 / 60 : ℝ)) := by
  sorry

/-- LEAF. Step of the proof, the finite Chebyshev step after the second moment, with no
analysis in it. If the squared deviations from `X` sum to at most `A`, then the indices
whose value is below `c0 * X * E^(-1/10)`, with `c0 * E^(-1/10) <= 1/2`, are at most
`A/(X/2)^2` in number, because each of them contributes more than `(X/2)^2` to that
same sum. Stated for an arbitrary finite index set and an arbitrary real sequence.

Non-vacuity: the hypotheses are satisfiable; at `s = ∅` the conclusion reads `0 <= A`,
and the smallest interesting case `s = {0}`, `g = 0`, `X = 1`, `E = 1`, `c0 = 1/2`,
`A = 1` gives `1 * (1/2)^2 <= 1`. `0 < X` excludes the degenerate `X <= 0`, and
`1 <= E` keeps `E^(-1/10)` in `(0,1]`, so the threshold lies in `(0, X/2]` and is not
negative. -/
theorem leaf_count_of_deviation (s : Finset ℕ) (g : ℕ → ℝ) (X E c₀ A : ℝ)
    (hX : 0 < X) (hc₀ : 0 < c₀) (hE : 1 ≤ E)
    (hc₀E : c₀ * E ^ (-(1 / 10 : ℝ)) ≤ 1 / 2)
    (hmom : (∑ n ∈ s, (X - g n) ^ 2) ≤ A) :
    (((s.filter (fun n : ℕ => g n < c₀ * X * E ^ (-(1 / 10 : ℝ)))).card : ℝ) *
      (X / 2) ^ 2) ≤ A := by
  sorry

/-! ### Assembly -/

/-- The elementary step of the assembly, with no analysis in it: twice the square of
the difference to two half summands bounds the square of the difference to their sum,
because `(p + q)^2 = 2 p^2 + 2 q^2 - (p - q)^2`. -/
private theorem pair_sq_le (x u v : ℝ) :
    2 * (x / 2 - u) ^ 2 + 2 * (x / 2 - v) ^ 2 ≥ (x - (u + v)) ^ 2 := by
  nlinarith [sq_nonneg ((x / 2 - u) - (x / 2 - v))]

/-- Lemma 7 from the three leaves above: the unchanged statement of `lemma7`. The two
moment leaves are minimised in their `δ` and `κ` caps and added, so that the deviation
of the pair from `X` is bounded by two squares at `2 (B1 + B2) N X^2 calE^(-17/60)`,
and the counting leaf at the threshold `c0 = 1/2` turns that into the count
`8 (B1 + B2) N calE^(-17/60)`. Since `calE >= 1` for `N >= 1` and `-17/60 <= -1/12`,
that is at most `(8 (B1 + B2) + 1) N calE^(-1/12)`, the exceptional count of the lemma.
The window predicate of the lemma is the index set of the two moment leaves, so the
filters agree. -/
theorem lemma7_split : Lemma7 := by
  classical
  intro γ h1 h2
  obtain ⟨δa, hδa, ha⟩ := leaf_moment_nu γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_moment_nu_succ γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  have hκ : 0 < min κa κb := lt_min hκa hκb
  obtain ⟨Ba, hBa, Na, ha⟩ := ha (min κa κb) hκ (min_le_left _ _)
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb (min κa κb) hκ (min_le_right _ _)
  refine ⟨min κa κb, 1 / 2, 8 * (Ba + Bb) + 1, hκ, by norm_num, max Na Nb,
    fun N hN => ?_⟩
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  have h1a := ha N hNa
  have h1b := hb N hNb
  -- the window of the lemma is the index set of the two moment leaves
  have hset : (Finset.range (2 * N + 1)).filter (fun n : ℕ =>
        F γ N / 2 < F γ n ∧ F γ n ≤ F γ N ∧
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
          R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re
          < 1 / 2 * F γ N * calE γ (min κa κb) N ^ (-(1 / 10 : ℝ))) =
      ((Finset.range (2 * N + 1)).filter
        (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
        (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
            R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re
            < 1 / 2 * F γ N * calE γ (min κa κb) N ^ (-(1 / 10 : ℝ))) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    tauto
  rw [hset]
  have hX : 0 < F γ N := Real.exp_pos _
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have harg : 0 ≤ min κa κb * Real.log (N : ℝ) ^ (3 - 2 * γ) :=
    mul_nonneg hκ.le (Real.rpow_nonneg hlog _)
  have hE : 1 ≤ calE γ (min κa κb) N := by
    rw [calE]
    exact Real.one_le_exp harg
  have hEthr : 1 / 2 * calE γ (min κa κb) N ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := by
    have hle : calE γ (min κa κb) N ^ (-(1 / 10 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hE (by norm_num)
    nlinarith
  -- the pair sum deviates from `X` by at most two half-deviations
  have hmom : (∑ n ∈ (Finset.range (2 * N + 1)).filter
        (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
      (F γ N - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
      ≤ 2 * (Ba + Bb) * N * F γ N ^ 2 * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ)) := by
    have hstep : (∑ n ∈ (Finset.range (2 * N + 1)).filter
          (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
        (F γ N - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
          R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2)
        ≤ ∑ n ∈ (Finset.range (2 * N + 1)).filter
          (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
          (2 * (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2 +
            2 * (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2) := by
      refine Finset.sum_le_sum (fun n _ => ?_)
      exact pair_sq_le _ _ _
    have hsplit : (∑ n ∈ (Finset.range (2 * N + 1)).filter
          (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
          (2 * (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2 +
            2 * (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2))
        = 2 * (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
              (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re) ^ 2)
          + 2 * (∑ n ∈ (Finset.range (2 * N + 1)).filter
              (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N),
              (F γ N / 2 - (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [hsplit] at hstep
    nlinarith [hstep, h1a, h1b]
  have hc := leaf_count_of_deviation
    ((Finset.range (2 * N + 1)).filter
      (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N))
    (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re)
    (F γ N) (calE γ (min κa κb) N) (1 / 2)
    (2 * (Ba + Bb) * N * F γ N ^ 2 * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ)))
    hX (by norm_num) hE hEthr hmom
  -- the count is at most `8 (B1 + B2) N calE^(-17/60)`
  have hX2 : (0 : ℝ) < (F γ N / 2) ^ 2 := by positivity
  have hXne : F γ N ≠ 0 := hX.ne'
  have hcount : ((((Finset.range (2 * N + 1)).filter
        (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
        (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
            R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re
            < 1 / 2 * F γ N * calE γ (min κa κb) N ^ (-(1 / 10 : ℝ)))).card : ℝ)
      ≤ 8 * (Ba + Bb) * N * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ)) := by
    have hstep : ((((Finset.range (2 * N + 1)).filter
          (fun n : ℕ => F γ N / 2 < F γ n ∧ F γ n ≤ F γ N)).filter
          (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re
              < 1 / 2 * F γ N * calE γ (min κa κb) N ^ (-(1 / 10 : ℝ)))).card : ℝ)
        ≤ (2 * (Ba + Bb) * N * F γ N ^ 2 * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ))) /
            (F γ N / 2) ^ 2 := (le_div_iff₀ hX2).mpr hc
    refine hstep.trans (le_of_eq ?_)
    field_simp
    ring
  -- and `calE >= 1` with `-17/60 <= -1/12` sends the exponent to the lemma's `-1/12`
  have hrate : calE γ (min κa κb) N ^ (-(17 / 60 : ℝ)) ≤
      calE γ (min κa κb) N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hlast : 8 * (Ba + Bb) * N * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ)) ≤
      (8 * (Ba + Bb) + 1) * N * calE γ (min κa κb) N ^ (-(1 / 12 : ℝ)) := by
    have hmul : 8 * (Ba + Bb) * ((N : ℝ) * calE γ (min κa κb) N ^ (-(17 / 60 : ℝ))) ≤
        8 * (Ba + Bb) * ((N : ℝ) * calE γ (min κa κb) N ^ (-(1 / 12 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 8 * (Ba + Bb))
      exact mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg N)
    have hpos : (0 : ℝ) ≤ (N : ℝ) * calE γ (min κa κb) N ^ (-(1 / 12 : ℝ)) := by
      positivity
    nlinarith [hmul, hpos]
  exact hcount.trans hlast

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.lemma7_split
