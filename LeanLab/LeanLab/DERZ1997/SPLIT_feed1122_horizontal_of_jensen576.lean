import LeanLab.DERZ1997.Decomp576a

/-!
Burst S89 burst-20261122 feed1122, split of `horizontal_of_jensen576` of
`LeanLab.DERZ1997.Decomp576a`.

Source: T. S. Trudgian, An improved upper bound for the argument of the Riemann zeta-function
on the critical line II, arXiv 1206.1844v4, pages 4 to 7, read from the arXiv PDF this run.

The paper's proof of the horizontal bound has two layers.

* At one fixed power `N`, page 4 before display 2.8 counts the zeros of `Re L(σ + iT)^N` on the
  horizontal segment: `n` zeros give `|Δ arg L| ≤ (n + 1) π / N`. Lemma 2 on page 4 and 5,
  Backlund's trick, pairs each such zero with a zero left of `1/2`, so that in Jensen's formula
  on the disc of centre `1 + η` and radius `r (1/2 + η)` every zero carries weight at least
  `2 log r`, display 3.9 with the Heath-Brown refinement on page 6. Display 4.3 then reads
  `n ≤ (1/(4π log r)) J - (1/(2 log r)) log |f(1 + η)| + 1 + N E / (2π)`. With `η = 1/4` and
  `r = 12/7` the Jensen part of `(n + 1)/N` is exactly `jensenMass576 χ T N`, whose
  normalisation `2 N log (12/7)` is the doubled weight of the pairing. The Gamma reflection
  error `E/(2π)`, display 3.14, and the move of the right endpoint from `σ₁` to `2` are covered
  by the loose budget `1.5`, as in the parent, and the two `+ 1` terms give `2/N`.
* Display 4.2, Rosser's observation, chooses powers `N_k → ∞` along which
  `f(1 + η) / |L(1 + η + iT)|^N → 1`, so that `f(1 + η) ≠ 0` and Jensen's formula applies, and
  then sends `N → ∞`.

The split below keeps the first layer as one LEAF at a single power, stated with the bare
nonvanishing `Re L(5/4 + iT)^N ≠ 0` that Jensen's formula needs, and PROVES the second layer:
`horizontal_of_jensen576_split` has the exact statement of the parent and is proved from the
leaf, from the Rosser limit `hcentre`, which forces that nonvanishing eventually, and from the
eventual mass bound, by letting the slack and `2/N_k` go to zero.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576a
open Complex Filter Topology MeasureTheory Set Decomp1529a
open scoped ComplexConjugate

/-- LEAF: Trudgian arXiv 1206.1844v4 page 4 the zero count before display 2.8, pages 4 and 5
Lemma 2 Backlund's trick, page 6 display 3.9, page 7 display 4.3, at one fixed power `N`.
For a primitive nonprincipal character at a height `|T| ≥ 1` with no zero of `L` on the
horizontal segment, and a power `N ≥ 1` with `Re L(5/4 + iT)^N ≠ 0`, the horizontal argument
divided by `π` is at most the Jensen mass at that power plus the loose budget `1.5`, which
covers `E/(2π)` of display 3.14 and the right endpoint, plus `2/N` from the two `+ 1` terms.
HARD: the first passage phase count, the Backlund pairing through the functional equation and
Jensen's formula on the disc of centre `5/4` and radius `9/7`. -/
theorem leaf_horizontal_one_power576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hc : (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N).re ≠ 0) :
    |horizontal576 χ T| ≤ jensenMass576 χ T N + 1.5 + 2 / (N : ℝ) := by
  sorry

/-- Trudgian page 7 display 4.2, Rosser's observation: along the chosen powers the ratio
`Re L(5/4 + iT)^N / |L(5/4 + iT)|^N` tends to `1`, so eventually `Re L(5/4 + iT)^N ≠ 0`.
PROVED. -/
theorem rosser_eventually_ne576 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (N : ℕ → ℕ)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1)) :
    ∀ᶠ k in atTop,
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re ≠ 0 := by
  have hev := hcentre.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hev] with k hk h0
  rw [h0, zero_div] at hk
  norm_num at hk

/-- Trudgian page 7, sending `N → ∞` after display 4.7: along a strictly increasing sequence of
powers, `2/N_k ≤ ε` eventually and `N_k ≥ 1` eventually. PROVED. -/
theorem powers_eventually_large576 (N : ℕ → ℕ) (hN : StrictMono N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, 1 ≤ N k ∧ 2 / (N k : ℝ) ≤ ε := by
  have hNt : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  filter_upwards [hNt.eventually_ge_atTop (2 / ε + 1)] with k hk
  have hpos : 0 < (N k : ℝ) := lt_of_lt_of_le (by positivity) hk
  refine ⟨?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ N k := le_trans (by linarith [div_pos two_pos hε]) hk
    exact_mod_cast h1
  · rw [div_le_iff₀ hpos]
    have h2 : 2 / ε * ε = 2 := by field_simp
    nlinarith

/-- Assembly of `horizontal_of_jensen576`, the exact statement of the parent. The single power
leaf applies at every late power of the Rosser sequence, where the mass is at most `B + ε/2`
and `2/N_k ≤ ε/2`; letting `ε → 0` gives the bound. CONDITIONAL ON
`leaf_horizontal_one_power576` only. -/
theorem horizontal_of_jensen576_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1))
    {B : ℝ} (hB : ∀ ε > 0, ∀ᶠ k in atTop, jensenMass576 χ T (N k) ≤ B + ε) :
    |horizontal576 χ T| ≤ B + 1.5 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h1 := hB (ε / 2) (by linarith)
  have h2 := powers_eventually_large576 N hN (ε := ε / 2) (by linarith)
  have h3 := rosser_eventually_ne576 χ T N hcentre
  obtain ⟨k, hk1, ⟨hk2, hk3⟩, hk4⟩ := (h1.and (h2.and h3)).exists
  have hleaf := leaf_horizontal_one_power576 χ hχ hne hT hgood (N k) hk2 hk4
  linarith

/-- Twin check: the assembly has exactly the type of the parent declaration. -/
example : type_of% @horizontal_of_jensen576 := @horizontal_of_jensen576_split

end LeanLab.DERZ1997.Decomp576a
