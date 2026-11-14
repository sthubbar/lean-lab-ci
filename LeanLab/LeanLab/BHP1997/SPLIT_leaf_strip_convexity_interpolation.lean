/-
Split of `leaf_strip_convexity_interpolation` in
LeanLab.BHP1997.SPLIT_horizontal_convexity_input into three leaves.

The sealed statement is the uniform convexity bound for a Dirichlet L-function in the
closed strip `1 / 2 <= Re s <= 1 + 1 / log x`: given a modulus `q` with `1 <= q <= x`, a
character `chi` of modulus `q`, the two edge bounds

* `||L(1 / 2 + i u)|| <= M0 * (q * (|u| + 1)) ^ (1 / 2 + 1 / log x)`,
* `||L(1 + 1 / log x + i u)|| <= M1`,

and `0 <= sigma <= 1 / 2 + 1 / log x`, `1 / 4 <= |tau|`, the value at
`1 / 2 + sigma + i tau` is at most

`2 * (q * (|tau| + 1)) ^ (1 / 2 + 1 / log x - sigma)
   * M0 ^ (1 - sigma / (1 / 2 + 1 / log x))
   * M1 ^ (sigma / (1 / 2 + 1 / log x))`.

The steps are:

* leaf one, the analytic core: a growth weighted Phragmen-Lindelof interpolation for one
  complex function analytic on a closed strip. When the left edge carries the height
  weight `(|u| + 1) ^ alpha` and the right edge carries none, every interior point at
  height `|tau|` carries the weight `(|tau| + 1) ^ (alpha * (b - sigma) / (b - a))`, the two
  edge constants take the complementary exponents `(b - sigma) / (b - a)` and
  `(sigma - a) / (b - a)`, and the price of the height weight is the single factor `2`.
  The statement mentions no character, no modulus, no conductor and no logarithm, and it
  has no content at all until a function, its strip and its two edge bounds are supplied.
  OPEN.
* leaf two, regularity: the L-function of a character is analytic on that closed strip.
  This is the continuation step that makes applying the core possible at all, and it
  asserts no bound.
* leaf three, growth: on that closed strip the L-function grows at most like a fixed power
  of the height. The core needs a growth hypothesis, and this leaf supplies one without
  fixing the exponent.

The assembly instantiates the core at `a = 1 / 2`, `b = 1 + 1 / log x`,
`alpha = 1 / 2 + 1 / log x`, `A = M0 * q ^ (1 / 2 + 1 / log x)` and `B = M1`. The left
edge hypothesis of the sealed statement becomes `A * (|u| + 1) ^ alpha` by the power of a
product, the right edge hypothesis is already `M1`, and the conclusion is power arithmetic:
with `sigma' = 1 / 2 + sigma`,
`alpha * (b - sigma') / (b - a) = alpha - sigma`,
`(b - sigma') / (b - a) = 1 - sigma / alpha`, and
`q ^ (alpha - sigma) * (|tau| + 1) ^ (alpha - sigma) = (q * (|tau| + 1)) ^ (alpha - sigma)`.
The assembly has no sorry and does not use `leaf_strip_convexity_interpolation`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_horizontal_convexity_input

namespace LeanLab.BHP1997.DecompC165a.Contour230

open Classical Complex MeanValue132 MeasureTheory Set Filter
open scoped Topology

/-- LEAF: step 1 of 3, the analytic core. Growth weighted Phragmen-Lindelof interpolation
on a closed strip: a function analytic on `a <= Re s <= b`, of at most polynomial growth
there, bounded by `A * (|u| + 1) ^ alpha` on the left edge and by `B` on the right edge, is
bounded at every interior point of height `|tau| >= 1 / 4` by the two edge constants raised
to the complementary weights, times the height weight
`(|tau| + 1) ^ (alpha * (b - sigma) / (b - a))`, at the price of the single factor `2`.
It is a statement about one complex function and five real numbers: it mentions no
character, no modulus, no conductor and no logarithm, and it has no content at all until
a function, its strip and its two edge bounds are supplied. OPEN. -/
theorem leaf_weighted_pl_strip (F : ℂ → ℂ) (a b α A B : ℝ)
    (hab : a < b) (hα : 0 ≤ α) (hA : 0 < A) (hB : 0 < B)
    (hana : AnalyticOnNhd ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hgr : ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C * (|s.im| + 1) ^ k)
    (hleft : ∀ u : ℝ, ‖F ((a : ℂ) + u * I)‖ ≤ A * (|u| + 1) ^ α)
    (hright : ∀ u : ℝ, ‖F ((b : ℂ) + u * I)‖ ≤ B) :
    ∀ σ τ : ℝ, a ≤ σ → σ ≤ b → 1 / 4 ≤ |τ| →
      ‖F ((σ : ℂ) + τ * I)‖ ≤
        2 * (|τ| + 1) ^ (α * (b - σ) / (b - a)) * A ^ ((b - σ) / (b - a)) *
          B ^ ((σ - a) / (b - a)) := by
  -- OUT OF REACH: This is the Phragmen-Lindelof interpolation theorem with height-dependent
  -- weights. Mathlib has PhragmenLindelof.horizontal_strip and .vertical_strip, but they
  -- use exponential growth conditions, not polynomial growth with height weights.
  -- The weighted version with (|τ|+1)^(α*(b-σ)/(b-a)) requires a custom argument
  -- combining the Hadamard three-lines theorem with the specific height weight.
  --
  -- Searches performed:
  -- - Mathlib search: PhragmenLindelof.horizontal_strip, PhragmenLindelof.vertical_strip
  --   (uses exp(B*exp(c*|z.re|)) growth, not polynomial)
  -- - Mathlib search: HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip
  --   (gives a^(1-t)*b^t bound, not the weighted version)
  -- - LeanSearch: "Phragmen Lindelof polynomial growth rpow" - no results
  -- - LeanSearch: "Hadamard three lines interpolation" - no weighted results
  --
  -- The theorem requires proving that if F is analytic on a ≤ Re s ≤ b, bounded by
  -- A*(|u|+1)^α on the left edge and B on the right edge, then for interior points,
  -- |F(s)| ≤ 2 * (|Im s|+1)^(α*(b-Re s)/(b-a)) * A^((b-Re s)/(b-a)) * B^((Re s-a)/(b-a)).
  --
  -- This is a non-trivial result in complex analysis. The standard Phragmen-Lindelof
  -- theorem gives a constant bound, not a weighted one. The weighted version requires
  -- applying the theorem to F(s) * (s-a)^(-α*(b-Re s)/(b-a)) * (b-s)^(-α*(Re s-a)/(b-a))
  -- or similar transformations.
  sorry

/-- LEAF: step 2 of 3, regularity. The L-function of a character of modulus `q` is analytic
on the closed strip `1 / 2 <= Re s <= 1 + 1 / log x`: the series only converges to the
right of one, so the value in the strip is the continuation furnished by the functional
equation, and the continuation has no pole there for any character. It asserts no bound
at all, and it is what lets the analytic core of step 1 be applied to this particular
function. OPEN. -/
theorem leaf_strip_continuation (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (fun s : ℂ => χ.LFunction s)
      {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log x} := by
  intro s hs
  rcases hs with ⟨hs1, hs2⟩
  -- The L-function is analytic everywhere except at s = 1 for the trivial character χ = 1.
  -- At s = 1, ζ(s) has a pole. However, the sealed statement never evaluates at s = 1
  -- because the condition 1/4 ≤ |τ| excludes it (when Re(s) = 1, we have s = 1 + iτ,
  -- and |τ| ≥ 1/4 implies τ ≠ 0, so s ≠ 1).
  --
  -- For non-trivial characters, the L-function is entire (analytic everywhere).
  -- For the trivial character, it's analytic everywhere except at s = 1.
  --
  -- We use the Mathlib lemma DirichletCharacter.differentiableAt_LFunction
  -- which requires s ≠ 1 ∨ χ ≠ 1.
  
  by_cases hs1' : s = (1 : ℂ)
  · -- At s = 1, we have a problem for χ = 1
    -- If χ ≠ 1, then L-function is analytic at s = 1
    -- If χ = 1, then L-function has a pole at s = 1
    -- But we can still prove the result because:
    -- 1. The strip condition gives 1/2 ≤ 1 ≤ 1 + 1/log x (true since 1/log x > 0)
    -- 2. For the sealed statement, s = 1 is never reached because |τ| ≥ 1/4
    --
    -- However, to make the proof work for all s in the strip, we need to handle s = 1.
    -- Let's check: is there a way to prove analyticity at s = 1 for the trivial character?
    --
    -- Actually, looking at the definition of DirichletCharacter.LFunction:
    -- It's defined as ZMod.LFunction χ s = N^{-s} * Σ_j χ(j) * hurwitzZeta(j/N, s)
    -- At s = 1, hurwitzZeta has a pole, so LFunction has a pole.
    --
    -- The theorem as stated is technically FALSE for χ = 1 at s = 1.
    -- But since the sealed statement never evaluates there, we can still use this theorem.
    --
    -- For the proof, we note that s = 1 is in the strip, and for χ = 1, the L-function
    -- is NOT analytic at s = 1. So we need to exclude this case.
    --
    -- Let's check if we can derive a contradiction from s = 1 and the strip conditions...
    -- No, s = 1 satisfies 1/2 ≤ 1 ≤ 1 + 1/log x.
    --
    -- I think the theorem statement has an error: it should be on the OPEN strip
    -- {s | 1/2 ≤ s.re ∧ s.re ≤ 1 + 1/log x ∧ s ≠ 1} or similar.
    -- But we can't change the statement.
    --
    -- Alternative: maybe the L-function for the trivial character IS defined to be
    -- analytic at s = 1 via analytic continuation? Let me check...
    --
    -- No, DirichletCharacter.LFunction is defined via Hurwitz zeta, which has a pole at s = 1.
    --
    -- I think the only honest approach is to note that the theorem is false and leave it BLOCKED.
    sorry
  · -- s ≠ 1, use differentiability
    have hdiff : DifferentiableAt ℂ (fun s : ℂ => χ.LFunction s) s :=
      DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs1')
    exact hdiff.analyticAt

/-- LEAF: step 3 of 3, growth. On the closed strip `1 / 2 <= Re s <= 1 + 1 / log x` the
L-function of a character of modulus `q` is at most a fixed constant times a fixed power of
the height `|Im s| + 1`. Both the constant and the exponent are left free, so this is only
a polynomial growth statement, far weaker than any explicit bound on the strip: it fixes
neither the size of the constant nor the size of the exponent. OPEN. -/
theorem leaf_strip_polynomial_growth (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) (χ : DirichletCharacter ℂ q) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 + 1 / Real.log x →
        ‖χ.LFunction s‖ ≤ C * (|s.im| + 1) ^ k := by
  -- The L-function has polynomial growth on the critical strip.
  -- This follows from the functional equation and the Phragmen-Lindelof principle.
  -- For a proof, we can use the following strategy:
  --
  -- 1. For Re(s) > 1, use the LSeries representation:
  --    |L(s, χ)| = |Σ χ(n)/n^s| ≤ Σ 1/n^Re(s) = ζ(Re(s))
  --    Since Re(s) ≥ 1/2, we need a bound for ζ(σ) for σ ≥ 1/2.
  --    ζ(σ) is bounded for σ ≥ 1/2 + δ for any δ > 0, but at σ = 1/2 exactly
  --    the series diverges (conditionally convergent only).
  --
  -- 2. For Re(s) ≤ 1, use the functional equation to relate to Re(s) > 1.
  --    The functional equation expresses L(s, χ) in terms of L(1-s, χ̅).
  --
  -- 3. The result is a known theorem in analytic number theory.
  --
  -- Since we can't easily prove this from scratch, and there's no ready-made lemma
  -- in Mathlib for "L-functions have polynomial growth on the critical strip",
  -- this is OUT OF REACH for a quick proof.
  --
  -- However, we can give a trivial proof: take C = sup_{Re(s) ∈ [1/2, 1+1/log x],
  -- |Im(s)| ≤ T} |L(s, χ)| + 1 and k = 0. The supremum is finite because the strip is
  -- compact and L-functions are continuous except at poles. But this C depends on T,
  -- which is not allowed (we need a uniform C for all s).
  --
  -- Actually, we can use a simpler argument: for Re(s) ≥ 1/2, the Dirichlet series
  -- converges conditionally, and we can bound |L(s, χ)| by something like
  -- q^{1/2} * (|s|+1)^ε for any ε > 0. This is a known result but requires
  -- the functional equation and zero-free regions.
  --
  -- Given the complexity, I'll leave this as BLOCKED with the reason OUT OF REACH.
  sorry

set_option maxHeartbeats 2000000 in
/-- The sealed statement of `leaf_strip_convexity_interpolation`, assembled from the three
leaves. Leaf 3 supplies the growth hypothesis of leaf 1 and leaf 2 the analyticity, so
leaf 1 applies to `s |-> L(s, chi)` on the strip with `a = 1 / 2`, `b = 1 + 1 / log x`,
`alpha = 1 / 2 + 1 / log x`, `A = M0 * q ^ (1 / 2 + 1 / log x)` and `B = M1`; the left edge
bound of the sealed statement is `A * (|u| + 1) ^ alpha` by the power of a product, and the
right edge bound is `M1`. What is left is power arithmetic on the two exponents and on the
product `q * (|tau| + 1)`. No sorry, and `leaf_strip_convexity_interpolation` is not used. -/
theorem leaf_strip_convexity_interpolation_split :
    ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, ∀ M0 M1 : ℝ, 0 < M0 → 0 < M1 →
        (∀ u : ℝ, ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
            M0 * ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x)) →
        (∀ u : ℝ, ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * I)‖ ≤ M1) →
        ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x → 1 / 4 ≤ |τ| →
          ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
            2 * ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) *
              M0 ^ (1 - σ / (1 / 2 + 1 / Real.log x)) *
              M1 ^ (σ / (1 / 2 + 1 / Real.log x)) := by
  intro x hx q _ hq hqx χ M0 M1 hM0 hM1 hleft hright σ τ hσ0 hσc hτ0
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hinv : (0 : ℝ) < 1 / Real.log x := one_div_pos.mpr hlog
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set θ : ℝ := 1 / 2 + 1 / Real.log x with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  have hθne : θ ≠ 0 := hθpos.ne'
  have hbθ : (1 + 1 / Real.log x) - 1 / 2 = θ := by rw [hθ]; ring
  have hbs : (1 + 1 / Real.log x) - (1 / 2 + σ) = θ - σ := by rw [hθ]; ring
  have hA : 0 < M0 * (q : ℝ) ^ θ := mul_pos hM0 (Real.rpow_pos_of_pos hqpos θ)
  have hleft' : ∀ u : ℝ, ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
      M0 * (q : ℝ) ^ θ * (|u| + 1) ^ θ := by
    intro u
    have hmul : ((q : ℝ) * (|u| + 1)) ^ θ = (q : ℝ) ^ θ * (|u| + 1) ^ θ :=
      Real.mul_rpow hqpos.le (by positivity : (0 : ℝ) ≤ |u| + 1)
    calc ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖
        ≤ M0 * ((q : ℝ) * (|u| + 1)) ^ θ := hleft u
      _ = M0 * (q : ℝ) ^ θ * (|u| + 1) ^ θ := by rw [hmul]; ring
  have hσb : 1 / 2 + σ ≤ 1 + 1 / Real.log x := by
    have h := hθ ▸ hσc
    linarith
  obtain ⟨C, k, hC, hk, hgr⟩ := leaf_strip_polynomial_growth x hx q hq hqx χ
  have hana := leaf_strip_continuation x hx q hq hqx χ
  have hmain := leaf_weighted_pl_strip (fun s : ℂ => χ.LFunction s) (1 / 2)
    (1 + 1 / Real.log x) θ (M0 * (q : ℝ) ^ θ) M1 (by linarith) hθpos.le hA hM1 hana
    ⟨C, k, hC, hk, hgr⟩ hleft' hright (1 / 2 + σ) τ (by linarith) hσb hτ0
  have e1 : θ * ((1 + 1 / Real.log x) - (1 / 2 + σ)) / ((1 + 1 / Real.log x) - 1 / 2) =
      θ - σ := by
    rw [hbθ, hbs]
    field_simp
  have e2 : ((1 + 1 / Real.log x) - (1 / 2 + σ)) / ((1 + 1 / Real.log x) - 1 / 2) =
      1 - σ / θ := by
    rw [hbθ, hbs]
    field_simp
  have e3 : ((1 / 2 + σ) - 1 / 2) / ((1 + 1 / Real.log x) - 1 / 2) = σ / θ := by
    rw [hbθ]
    field_simp
    ring
  have e4 : (M0 * (q : ℝ) ^ θ) ^ (1 - σ / θ) = M0 ^ (1 - σ / θ) * (q : ℝ) ^ (θ - σ) := by
    rw [Real.mul_rpow hM0.le (Real.rpow_nonneg hqpos.le θ)]
    rw [← Real.rpow_mul hqpos.le]
    rw [show θ * (1 - σ / θ) = θ - σ by field_simp]
  have e5 : ((q : ℝ) * (|τ| + 1)) ^ (θ - σ) = (q : ℝ) ^ (θ - σ) * (|τ| + 1) ^ (θ - σ) :=
    Real.mul_rpow hqpos.le (by positivity : (0 : ℝ) ≤ |τ| + 1)
  refine hmain.trans (le_of_eq ?_)
  rw [e1, e2, e3, e4, e5]
  ring

-- Axiom audit driver for the assembly.
#print axioms leaf_strip_convexity_interpolation_split

end LeanLab.BHP1997.DecompC165a.Contour230