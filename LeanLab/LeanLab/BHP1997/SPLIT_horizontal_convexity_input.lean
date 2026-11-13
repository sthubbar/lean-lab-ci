/-
Split of `horizontal_convexity_input` in LeanLab.BHP1997.Decomp488c into leaves.

The sealed statement is the uniform convexity bound for Dirichlet L-functions that is
used on the horizontal sides of the Perron rectangle of display 3.36: for `2 ≤ x`,
`1 ≤ q ≤ x`, a character `χ` of modulus `q` and `σ` in `[0, 1 / 2 + 1 / log x]`, the
value at `1 / 2 + σ + iτ` with `1 / 4 ≤ |τ| ≤ 2 * x` is at most
`C * log x * (((q * (|τ| + 1)) ^ (1 / 2 + 1 / log x - σ)) + 1)`.

The bound has three classical steps, and the leaves below are those steps:

* on the line `Re s = 1 / 2`, the functional equation together with Stirling's formula
  for the gamma factor gives the exponent `1 / 2 + 1 / log x` and costs the factor
  `log x`; the principal character is a separate leaf because it goes through the zeta
  function and its Euler factors rather than through a non-principal L-series;
* on the line `Re s = 1 + 1 / log x`, the Euler product gives the trivial bound
  `ζ(1 + 1 / log x) ≤ 1 + log x`, uniform in `q` and in `χ`;
* the strip `1 / 2 ≤ Re s ≤ 1 + 1 / log x` is filled in by convexity, that is, by the
  Phragmén–Lindelöf interpolation of the two endpoint bounds with the height weight
  `q * (|τ| + 1)`. That weight runs from the exponent `1 / 2 + 1 / log x` on the left
  edge to the exponent `0` on the right edge, which is exactly where the exponent
  `1 / 2 + 1 / log x - σ` of the sealed statement comes from. The hypothesis
  `1 / 4 ≤ |τ|` keeps the height away from the pole of the principal character.

The assembly below multiplies the three steps together. Both endpoint bounds are put in
the single constant `max (max C₁ C₂) C₃`, the height weight of the interpolation and the
`log x` of the two endpoints collapse to the single `log x`, and the factor `2` that the
interpolation costs is absorbed into the constant. No leaf is a restriction of the
sealed statement to some range of its parameters: each one is a strictly different
inequality, so none of them gives the sealed statement back. Every leaf is OPEN, the
assembly `horizontal_convexity_input_split` has no sorry, and the sealed theorem
`horizontal_convexity_input` is not used.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp488c

namespace LeanLab.BHP1997.DecompC165a.Contour230
open Classical Complex MeanValue132 MeasureTheory Set Filter
open scoped Topology

/-- LEAF: leaf 1 of 4. Step of the proof: the bound on the line `Re s = 1 / 2` for a
non-principal character, from the functional equation of `L(s, χ)` together with
Stirling's formula for the gamma factor. The gamma factor contributes the exponent
`1 / 2`, the loss `ε = 1 / log x` of the functional equation the rest of the exponent,
and dropping the epsilon with its cost the factor `log x`. One line, no `σ`, so not the
sealed statement. OPEN. -/
theorem leaf_critical_line_nonprincipal :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u : ℝ,
        ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
          C * Real.log x * ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x) := by
  sorry

/-- LEAF: leaf 2 of 4. Step of the proof: the bound on the line `Re s = 1 / 2` for the
principal character. Here `L(s, 1)` is the zeta function times the finitely many Euler
factors of the primes dividing the modulus, and the same functional equation and
Stirling step is applied to the zeta function; those Euler factors are absorbed into the
constant because the modulus is bounded by `x`. One line, no `σ`, so not the sealed
statement. OPEN. -/
theorem leaf_critical_line_principal :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ u : ℝ,
        ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
          C * Real.log x * ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x) := by
  sorry

set_option maxHeartbeats 4000000 in

private lemma tsum_nat_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσpos : 0 < σ := by linarith
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -σ) (by linarith)).mono
      fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht)
  have hnonneg : ∀ t ∈ Ioi (1 : ℝ), (0 : ℝ) ≤ t ^ (-σ) := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _
  have hint : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    AntitoneOn.summable_of_integrableOn_Ioi (f := fun t : ℝ => t ^ (-σ)) (N := 1)
      (by simpa using hanti) (by simpa using hint) (by simpa using hnonneg)
  have htail : ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) ≤
      ∫ x in Ioi (1 : ℝ), x ^ (-σ) := by
    simpa using (AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ => t ^ (-σ)) 1
      (by simpa using hanti) (by simpa using hint) (by simpa using hnonneg))
  have hInt : ∫ x in Ioi (1 : ℝ), x ^ (-σ) = 1 / (σ - 1) := by
    have hc : (0 : ℝ) < 1 := by norm_num
    rw [integral_Ioi_rpow_of_lt (a := -σ) (by linarith : -σ < -1) (c := 1) hc]
    norm_num
    rw [show -σ + 1 = -(σ - 1) by ring, div_neg, neg_div, neg_neg, one_div]
  rw [hInt] at htail
  have hsplit := hsummable.sum_add_tsum_nat_add 2
  have h0 : (((0 : ℕ) : ℝ)) ^ (-σ) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0)]
  have h1 : (((1 : ℕ) : ℝ)) ^ (-σ) = 1 := by
    rw [Nat.cast_one, Real.one_rpow]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1,
    zero_add] at hsplit
  linarith [hsplit]

set_option maxHeartbeats 4000000 in
private lemma LSeries_norm_le_tsum {f : ℕ → ℂ} (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
  have hσpos : 0 < s.re := by linarith
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s.re)) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -s.re) (by linarith)).mono
      fun t ht => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht)
  have hnonneg : ∀ t ∈ Ioi (1 : ℝ), (0 : ℝ) ≤ t ^ (-s.re) := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1) zero_lt_one
  have hdom : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    AntitoneOn.summable_of_integrableOn_Ioi (f := fun t : ℝ => t ^ (-s.re)) (N := 1)
      (by simpa using hanti) (by simpa using hint) (by simpa using hnonneg)
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with h0 | hn
    · subst h0
      rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [LSeries.norm_term_eq, if_neg hn]
      calc ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by
            gcongr
            exact hf n
        _ = (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg hnpos.le, one_div]
  have hsumm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hdom
  calc ‖LSeries f s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := hsumm.tsum_le_tsum hterm hdom

set_option maxHeartbeats 4000000 in
/-- LEAF: leaf 3 of 4. Step of the proof: the bound on the line `Re s = 1 + 1 / log x`,
from the Euler product. Every Euler factor has absolute value at most one, so the
L-function is at most `ζ(1 + 1 / log x)`, and that is at most `1 + 1 / (1 / log x) =
1 + log x` because the zeta function is at most `1 + 1 / (s - 1)` to the right of one.
The height does not enter and the right hand side carries no conductor, so this is far
from the sealed statement. PROVED: the two private lemmas above give the termwise bound
`‖L(s, χ)‖ ≤ ∑ n ^ (-Re s)` at `Re s > 1` and the integral-test bound
`∑ n ^ (-σ) ≤ 1 + 1 / (σ - 1)`, and `σ = 1 + 1 / log x` turns the latter into
`1 + log x ≤ 3 * log x` for `2 ≤ x`. -/
theorem leaf_right_line_euler_product :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, ∀ u : ℝ,
        ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * I)‖ ≤ C * Real.log x := by
  refine ⟨3, by norm_num, ?_⟩
  intro x hx q _ hq hqx χ u
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log x := by linarith [Real.log_two_gt_d9]
  set σ : ℝ := 1 + 1 / Real.log x with hσ
  have hσ1 : 1 < σ := by
    have hpos : 0 < 1 / Real.log x := by positivity
    rw [hσ]; linarith
  have hre : ((((1 + 1 / Real.log x : ℝ)) : ℂ) + u * I).re = σ := by
    simp [hσ]
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by rw [hre]; exact hσ1)]
  have hmain := LSeries_norm_le_tsum (f := fun n : ℕ => χ ((n : ZMod q)))
    (fun n => DirichletCharacter.norm_le_one χ ((n : ZMod q)))
    (s := ((((1 + 1 / Real.log x : ℝ)) : ℂ) + u * I)) (by rw [hre]; exact hσ1)
  rw [hre] at hmain
  have hts := tsum_nat_rpow_neg_le (σ := σ) hσ1
  have hσm : σ - 1 = 1 / Real.log x := by rw [hσ]; ring
  have hval : (1 : ℝ) + 1 / (σ - 1) = 1 + Real.log x := by rw [hσm, one_div_one_div]
  rw [hval] at hts
  linarith [hmain, hts, hlog, hlog2]

/-- LEAF: leaf 4 of 4. Step of the proof: convexity in the strip. Two bounds on the two
vertical edges, holding at every height `u` and carrying the weight `q * (|u| + 1)` with
exponent `1 / 2 + 1 / log x` on the left edge and exponent zero on the right edge,
interpolate to the exponent `1 / 2 + 1 / log x - σ` at every interior `1 / 2 + σ + iτ`.
The edge constants take the complementary weights and Phragmén-Lindelöf with that height
weight costs only the factor `2`; `1 / 4 ≤ |τ|` keeps the height away from the pole at
`s = 1`. It takes the edge bounds as hypotheses and produces no constant of its own, so
it is not the sealed statement. OPEN. -/
theorem leaf_strip_convexity_interpolation :
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
  sorry

/-- The sealed statement of `horizontal_convexity_input`, assembled from the four
leaves: leaf 1 for a non-principal character and leaf 2 for the principal one give the
left edge, leaf 3 gives the right edge, and leaf 4 interpolates between them. Both edges
are taken with the single constant `K = max (max C₁ C₂) C₃`, the two edge factors
`K * log x` raised to the complementary exponents multiply back to `K * log x`, the
height weight and the power of `q` combine into `(q * (|τ| + 1)) ^ (1 / 2 + 1 / log x -
σ)`, and the factor `2` of the interpolation is absorbed into the constant, which is
`2 * K`. No sorry, and the sealed theorem `horizontal_convexity_input` is not used. -/
theorem horizontal_convexity_input_split :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x →
        1 / 4 ≤ |τ| → |τ| ≤ 2 * x →
        ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
          C * Real.log x *
            (((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) + 1) := by
  obtain ⟨C₁, hC₁, hleaf₁⟩ := leaf_critical_line_nonprincipal
  obtain ⟨C₂, hC₂, hleaf₂⟩ := leaf_critical_line_principal
  obtain ⟨C₃, hC₃, hleaf₃⟩ := leaf_right_line_euler_product
  have hK₁ : 0 < max (max C₁ C₂) C₃ :=
    lt_of_lt_of_le (lt_of_lt_of_le hC₁ (le_max_left _ _)) (le_max_left _ _)
  have hK₂ : C₁ ≤ max (max C₁ C₂) C₃ :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₃ : C₂ ≤ max (max C₁ C₂) C₃ :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hK₄ : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ _
  refine ⟨2 * max (max C₁ C₂) C₃, ?_, ?_⟩
  · linarith
  intro x hx q _ hq hqx χ σ τ hσ0 hσc hτ0 hτ
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hKl : 0 < max (max C₁ C₂) C₃ * Real.log x := mul_pos hK₁ hlog
  have hline0 : ∀ u : ℝ, ‖χ.LFunction (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
      max (max C₁ C₂) C₃ * Real.log x *
        ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x) := by
    intro u
    have hB0 : (0 : ℝ) ≤ ((q : ℝ) * (|u| + 1)) ^ (1 / 2 + 1 / Real.log x) :=
      Real.rpow_nonneg (by positivity) _
    rcases eq_or_ne χ 1 with hχ | hχ
    · have hu := hleaf₂ x hx q hq hqx χ hχ u
      have hcl : C₂ * Real.log x ≤ max (max C₁ C₂) C₃ * Real.log x :=
        mul_le_mul_of_nonneg_right hK₃ hlog.le
      exact hu.trans (mul_le_mul_of_nonneg_right hcl hB0)
    · have hu := hleaf₁ x hx q hq hqx χ hχ u
      have hcl : C₁ * Real.log x ≤ max (max C₁ C₂) C₃ * Real.log x :=
        mul_le_mul_of_nonneg_right hK₂ hlog.le
      exact hu.trans (mul_le_mul_of_nonneg_right hcl hB0)
  have hline1 : ∀ u : ℝ, ‖χ.LFunction (((1 + 1 / Real.log x : ℝ) : ℂ) + u * I)‖ ≤
      max (max C₁ C₂) C₃ * Real.log x := by
    intro u
    have hu := hleaf₃ x hx q hq hqx χ u
    exact hu.trans (mul_le_mul_of_nonneg_right hK₄ hlog.le)
  have hconv := leaf_strip_convexity_interpolation x hx q hq hqx χ
    (max (max C₁ C₂) C₃ * Real.log x) (max (max C₁ C₂) C₃ * Real.log x)
    hKl hKl hline0 hline1 σ τ hσ0 hσc hτ0
  have hcollapse :
      (max (max C₁ C₂) C₃ * Real.log x) ^ (1 - σ / (1 / 2 + 1 / Real.log x)) *
        (max (max C₁ C₂) C₃ * Real.log x) ^ (σ / (1 / 2 + 1 / Real.log x)) =
      max (max C₁ C₂) C₃ * Real.log x := by
    rw [← Real.rpow_add hKl]
    rw [show 1 - σ / (1 / 2 + 1 / Real.log x) + σ / (1 / 2 + 1 / Real.log x) = 1 by ring]
    exact Real.rpow_one _
  have hB0 : (0 : ℝ) ≤ ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) :=
    Real.rpow_nonneg (by positivity) _
  have hc0 : (0 : ℝ) ≤ 2 * max (max C₁ C₂) C₃ * Real.log x := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact (mul_pos (mul_pos h2 hK₁) hlog).le
  have hprod : (0 : ℝ) ≤ (2 * max (max C₁ C₂) C₃ * Real.log x) *
      ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) := mul_nonneg hc0 hB0
  calc ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖
      ≤ 2 * ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) *
          (max (max C₁ C₂) C₃ * Real.log x) ^ (1 - σ / (1 / 2 + 1 / Real.log x)) *
          (max (max C₁ C₂) C₃ * Real.log x) ^ (σ / (1 / 2 + 1 / Real.log x)) := hconv
    _ = 2 * ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) *
          ((max (max C₁ C₂) C₃ * Real.log x) ^ (1 - σ / (1 / 2 + 1 / Real.log x)) *
           (max (max C₁ C₂) C₃ * Real.log x) ^ (σ / (1 / 2 + 1 / Real.log x))) := by
          ring
    _ = 2 * ((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) *
          (max (max C₁ C₂) C₃ * Real.log x) := by rw [hcollapse]
    _ ≤ (2 * max (max C₁ C₂) C₃) * Real.log x *
          (((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) + 1) := by
          nlinarith [hprod, hB0]

-- Axiom audit driver for the assembly.
#print axioms horizontal_convexity_input_split

end LeanLab.BHP1997.DecompC165a.Contour230
