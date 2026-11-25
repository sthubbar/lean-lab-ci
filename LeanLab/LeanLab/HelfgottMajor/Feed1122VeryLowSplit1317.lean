import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of the conductor `13` and `17` very low leaves, burst 20261122 S138

The leaves `veryLow_level_thirteen_sum_le_one` of `Feed1122VeryLowRepair` and
`veryLow_level_seventeen_sum_le_one` of `Feed1122VeryLowRepair2` say that for a primitive
character modulo `13`, resp. `17`, the strip zeros of height in `(0, 1]`, counted with
multiplicity, contribute at most one. Their source is Section 4.6 page 56 of Helfgott,
arXiv 1305.2897v4, which takes as input Platt's rigorous verification [Pla11] of GRH for
primitive characters of small conductor. Platt's method has three outputs, and the split
follows them, one LEAF each per conductor:

* GRH in the box: a zero with real part in `(0,1)` and height in `(0,1]` has real part `1/2`.
* The count on the critical line: at most one ordinate `t ∈ (0,1]` with `L(1/2 + it, χ) = 0`;
  this is the Turing method count matched against the located sign changes.
* Simplicity: each such zero is simple, since it is located by a sign change of the real
  Hardy function and the Turing count leaves no room for a double zero.

The assembly `sum_le_one_of_grh_count_simple` is PROVED here, and the two original leaves are
proved from it in their own files. Numerics, burst S138 with mpmath through the Hurwitz formula
`L(s, χ) = q^(-s) Σ χ(a) ζ(s, a/q)`: on the box `[10^(-4), 1 - 10^(-4)] × [10^(-6), 1]` the winding
number is `1` for exactly one primitive character modulo `13` and one modulo `17`, and `0` for all
the others; the two zeros lie on the critical line and have nonzero derivative. AI wrote this
Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Feed1122VeryLowSplit1317
open Complex
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- A complex number with real part `1/2` is `1/2 + (Im ρ) i`. -/
lemma eq_half_add_im_mul_I {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
  apply Complex.ext <;> simp [h]

/-- Assembly, PROVED: GRH in the box, at most one critical ordinate in `(0, 1]` and simplicity
give that the zeros of height in `(0, 1]`, with multiplicity, contribute at most one. -/
theorem sum_le_one_of_grh_count_simple (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hgrh : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      ρ.im ≤ 1 → ρ.re = 1 / 2)
    (hcount : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < t₂ → t₂ ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) = 0 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) = 0 → t₁ = t₂)
    (hsimple : ∀ t : ℝ, 0 < t → t ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 →
      mult χ ((1 / 2 : ℂ) + (t : ℂ) * I) ≤ 1) :
    (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1),
      (mult χ ρ : ℝ)) ≤ 1 := by
  set S := (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ 1) with hS
  have key : ∀ ρ ∈ S, ρ.re = 1 / 2 ∧ 0 < ρ.im ∧ ρ.im ≤ 1 ∧
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (ρ.im : ℂ) * I) = 0 := by
    intro ρ hρ
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    obtain ⟨hz, h0, h1⟩ := hρ
    have hre := hgrh ρ hz.1 hz.2.1 hz.2.2.1 h0 h1
    refine ⟨hre, h0, h1, ?_⟩
    rw [← eq_half_add_im_mul_I hre]
    exact hz.1
  have hcard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨ra, a0, a1, La⟩ := key a ha
    obtain ⟨rb, b0, b1, Lb⟩ := key b hb
    have him := hcount a.im b.im a0 a1 b0 b1 La Lb
    exact Complex.ext (by rw [ra, rb]) him
  have hterm : ∀ ρ ∈ S, (mult χ ρ : ℝ) ≤ 1 := by
    intro ρ hρ
    obtain ⟨r, h0, h1, hL⟩ := key ρ hρ
    have := hsimple ρ.im h0 h1 hL
    rw [← eq_half_add_im_mul_I r] at this
    exact_mod_cast this
  calc (∑ ρ ∈ S, (mult χ ρ : ℝ)) ≤ ∑ _ρ ∈ S, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = S.card := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11] of GRH,
conductor `13`. Class HARD. A zero of `L(s, χ)`, `χ` primitive modulo `13`, with real part in
`(0, 1)` and height in `(0, 1]` lies on the critical line. -/
theorem grh_box_level_thirteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      ρ.im ≤ 1 → ρ.re = 1 / 2 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
Turing method zero count on the critical line, conductor `13`. Class HARD. For `χ` primitive
modulo `13` there is at most one ordinate `t ∈ (0, 1]` with `L(1/2 + it, χ) = 0`; numerically
one character has `t ≈ 0.8839603095` and the other ten have none. -/
theorem critical_count_level_thirteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 13) :
    ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < t₂ → t₂ ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) = 0 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) = 0 → t₁ = t₂ := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
critical zeros of height in `(0, 1]` are simple, conductor `13`. Class HARD. -/
theorem simple_level_thirteen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 13) :
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 →
      mult χ ((1 / 2 : ℂ) + (t : ℂ) * I) ≤ 1 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11] of GRH,
conductor `17`. Class HARD. A zero of `L(s, χ)`, `χ` primitive modulo `17`, with real part in
`(0, 1)` and height in `(0, 1]` lies on the critical line. -/
theorem grh_box_level_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) :
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im →
      ρ.im ≤ 1 → ρ.re = 1 / 2 := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
Turing method zero count on the critical line, conductor `17`. Class HARD. For `χ` primitive
modulo `17` there is at most one ordinate `t ∈ (0, 1]` with `L(1/2 + it, χ) = 0`; numerically
one character has `t ≈ 0.3913146130` and the other fourteen have none. -/
theorem critical_count_level_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 17) :
    ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < t₂ → t₂ ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₁ : ℂ) * I) = 0 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t₂ : ℂ) * I) = 0 → t₁ = t₂ := by
  sorry

/-- LEAF: Helfgott arXiv 1305.2897v4 Section 4.6 page 56, Platt's verification [Pla11], the
critical zeros of height in `(0, 1]` are simple, conductor `17`. Class HARD. -/
theorem simple_level_seventeen (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 17) :
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 →
      mult χ ((1 / 2 : ℂ) + (t : ℂ) * I) ≤ 1 := by
  sorry

end LeanLab.HelfgottMajor.Feed1122VeryLowSplit1317
