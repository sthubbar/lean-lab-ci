/-
Split of `leaf_strip_convexity_interpolation` in
LeanLab.BHP1997.SPLIT_horizontal_convexity_input into four leaves.

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
  height `tau` carries the weight `(|tau| + 1) ^ (alpha * (b - sigma) / (b - a))`, the two
  edge constants take the complementary exponents `(b - sigma) / (b - a)` and
  `(sigma - a) / (b - a)`, and the price of the height weight is the single factor `2`.
  The statement mentions no character, no modulus and no logarithm.
* leaf two, regularity: the L-function of a non-principal character is analytic on that
  closed strip. The series only converges to the right of one, so the value in the strip is
  the continuation, and for a non-principal character that continuation is entire. The
  leaf asserts no bound.
* leaf three, growth: on that closed strip the L-function of a non-principal character
  grows at most like a fixed power of the height.
* leaf four, the principal character. This case cannot be handled by leaves one to three:
  the L-function of the principal character is the zeta function times the finitely many
  Euler factors of the primes dividing the modulus, so it has a pole at `s = 1`, which lies
  inside the strip. Analyticity on the closed strip and a polynomial growth bound on it
  both fail there, so the core of leaf one provably cannot consume this character; the
  bound has to be produced for the heights `|tau| >= 1 / 4` that keep the point of
  evaluation at distance at least `1 / 4` from the pole. Leaf four is that bound. The
  principal and non-principal characters are different functions and are treated
  separately, exactly as the two critical line leaves of the parent file are.

The assembly instantiates the core at `a = 1 / 2`, `b = 1 + 1 / log x`,
`alpha = 1 / 2 + 1 / log x`, `A = M0 * q ^ (1 / 2 + 1 / log x)` and `B = M1`. The left
edge hypothesis of the sealed statement becomes `A * (|u| + 1) ^ alpha` by the power of a
product, the right edge hypothesis is already `M1`, and the conclusion is power
arithmetic: with `sigma' = 1 / 2 + sigma`,
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

/-- LEAF: step 1 of 4, the analytic core. Growth weighted Phragmen-Lindelof interpolation
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
  sorry

/-- LEAF: step 2 of 4, regularity for a non-principal character. The L-function of a
character whose values are not all one is entire, so in particular it is analytic on the
closed strip `1 / 2 <= Re s <= 1 + 1 / log x`. The series only converges to the right of
one, so the value in the strip is the continuation; for a non-principal character that
continuation has no pole anywhere. The leaf asserts no bound, and it is what lets the core
of step 1 be applied to this function. PROVED from the differentiability of the continued
L-function away from one. -/
theorem leaf_strip_continuation (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => χ.LFunction s)
      {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log x} := by
  intro s _
  exact (Differentiable.analyticAt (DirichletCharacter.differentiable_LFunction hχ) s)

/-- LEAF: step 3 of 4, growth. On the closed strip `1 / 2 <= Re s <= 1 + 1 / log x` the
L-function of a non-principal character of modulus `q` is at most a fixed constant times a
fixed power of the height `|Im s| + 1`. Both the constant and the exponent are left free,
so this is only a polynomial growth statement, far weaker than any explicit bound on the
strip: it fixes neither the size of the constant nor the size of the exponent. OPEN. -/
theorem leaf_strip_polynomial_growth (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 + 1 / Real.log x →
        ‖χ.LFunction s‖ ≤ C * (|s.im| + 1) ^ k := by
  sorry

/-- LEAF: step 4 of 4, the principal character. Its L-function is the zeta function times
the finitely many Euler factors of the primes dividing the modulus, so it has a simple pole
at `s = 1`, inside the strip; there is no analyticity on the closed strip and no growth
bound on it. What survives is the bound at heights `|tau| >= 1 / 4`, where the point of
evaluation is at distance at least `1 / 4` from the pole: the two edge bounds interpolate,
the pole is resolved by the shift that removes it, and the height weight
`q * (|tau| + 1)` and the two edge constants take the complementary exponents. This is one
character, the principal one, and one case; it is not the general statement of any other
line. OPEN. -/
theorem leaf_principal_strip_bound (x : ℝ) (hx : 2 ≤ x) (q : ℕ) [NeZero q] (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) (M0 M1 : ℝ) (hM0 : 0 < M0) (hM1 : 0 < M1)
    (hleft : ∀ u : ℝ, ‖(1 : DirichletCharacter ℂ q).LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
        M0 * ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x))
    (hright : ∀ u : ℝ,
      ‖(1 : DirichletCharacter ℂ q).LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * I)‖ ≤ M1) :
    ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x → 1 / 4 ≤ |τ| →
      ‖(1 : DirichletCharacter ℂ q).LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
        2 * ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) *
          M0 ^ (1 - σ / (1 / 2 + 1 / Real.log x)) *
          M1 ^ (σ / (1 / 2 + 1 / Real.log x)) := by
  sorry

set_option maxHeartbeats 2000000 in
/-- The sealed statement of `leaf_strip_convexity_interpolation`, assembled from the four
leaves. For a non-principal character, leaf 3 supplies the growth hypothesis of leaf 1 and
leaf 2 the analyticity, so leaf 1 applies to `s |-> L(s, chi)` on the strip with
`a = 1 / 2`, `b = 1 + 1 / log x`, `alpha = 1 / 2 + 1 / log x`,
`A = M0 * q ^ (1 / 2 + 1 / log x)` and `B = M1`; the left edge bound of the sealed
statement is `A * (|u| + 1) ^ alpha` by the power of a product, and the right edge bound is
`M1`. For the principal character, leaf 4 is the same bound and is used directly. What is
left is power arithmetic on the two exponents and on the product `q * (|tau| + 1)`. No
sorry, and `leaf_strip_convexity_interpolation` is not used. -/
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
  rcases eq_or_ne χ 1 with hχ | hχ
  · subst χ
    exact leaf_principal_strip_bound x hx q hq hqx M0 M1 hM0 hM1 hleft hright σ τ hσ0 hσc hτ0
  · have hlog : 0 < Real.log x := Real.log_pos (by linarith)
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
    obtain ⟨C, k, hC, hk, hgr⟩ := leaf_strip_polynomial_growth x hx q hq hqx χ hχ
    have hana := leaf_strip_continuation x hx q hq hqx χ hχ
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
    have e4 : (M0 * (q : ℝ) ^ θ) ^ (1 - σ / θ) =
        M0 ^ (1 - σ / θ) * (q : ℝ) ^ (θ - σ) := by
      rw [Real.mul_rpow hM0.le (Real.rpow_nonneg hqpos.le θ)]
      rw [← Real.rpow_mul hqpos.le]
      rw [show θ * (1 - σ / θ) = θ - σ by field_simp]
    have e5 : ((q : ℝ) * (|τ| + 1)) ^ (θ - σ) =
        (q : ℝ) ^ (θ - σ) * (|τ| + 1) ^ (θ - σ) :=
      Real.mul_rpow hqpos.le (by positivity : (0 : ℝ) ≤ |τ| + 1)
    refine hmain.trans (le_of_eq ?_)
    rw [e1, e2, e3, e4, e5]
    ring

-- Axiom audit driver for the assembly.
#print axioms leaf_strip_convexity_interpolation_split

end LeanLab.BHP1997.DecompC165a.Contour230
