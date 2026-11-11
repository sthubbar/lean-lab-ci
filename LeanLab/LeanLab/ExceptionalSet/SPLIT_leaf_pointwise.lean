import LeanLab.ExceptionalSet.Decomp465a

/-!
Split of the pointwise input `leaf_pointwise` of Decomp465a.

The statement to be split fixes `1 < γ < 3/2` and asks for one conductor `r`, at least `1` and at
most `F(γ,N)^(6δ)`, for which the real part of the major arc coefficient at every even adjacent
integer `ν_n + j`, `j ∈ {0,1}`, of the floor window exceeds `c F(γ,N) ℰ^(-1/10)` up to an explicit
multiple of the divisor error `divisorError r (F(γ,N)^(6δ)) (ν_n + j)`, and it asks for that only
when the conductor is either small, `r ≤ ℰ^(1/7)`, or has a small gcd with the even integer,
`gcd(ν_n + j, r) < r/24`.

The split separates the three things that statement says. One piece only exhibits a conductor in the
required range: `r = 1` is enough, because `F(γ,N) ≥ 1` for `N ≥ 1` and a positive power of a number
at least one is at least one. The other two pieces are the two mechanisms the lower bound has, one
for each disjunct of the conductor hypothesis, and each carries its own disjunct as a hypothesis, so
each is strictly weaker as a statement than the whole pointwise input: the small conductor piece is
the major arc lower bound at a conductor below the cap `ℰ^(1/7)`, and the large conductor piece is
the case where the conductor is beyond that cap and the explicit divisor error alone carries the
bound, the gcd of the even integer with the conductor being below `r/24`.

The assembly takes the two caps `δ₀` and `κ₀` as minima, the constant `c` as a minimum, the
coefficient `A` of the divisor error as a maximum, and the threshold `N₀` as a maximum that is also
at least one, so that the conductor piece applies. It then obtains the conductor from that piece and
splits on the disjunction of the conductor hypothesis, applying the piece belonging to the case at
hand. The only inequalities the assembly itself proves are those of a minimum in `c`, of a maximum
in `A`, and the nonnegativity of the divisor error, which is proved in the file being split.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. Conductor in range: for a positive exponent `δ` and a window start `N ≥ 1` there is a
natural number `r` with `1 ≤ r` and `r ≤ F(γ,N)^(6δ)`. This is the witness step of the pointwise
input on its own. It asserts nothing about the major arc coefficient, about the divisor error, or
about the gcd condition, and it holds with `r = 1` since `F(γ,N) ≥ 1`. -/
theorem leaf_conductor_in_range (γ δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hpow : 0 ≤ Real.log (N : ℝ) ^ γ := Real.rpow_nonneg hlog γ
  have hF : 1 ≤ F γ (N : ℝ) := Real.one_le_exp hpow
  have h6 : 0 ≤ 6 * δ := by linarith
  exact ⟨1, le_refl 1, by simpa using Real.one_le_rpow hF h6⟩

/-- LEAF. Small conductor case of the pointwise lower bound: for one conductor `r` in the allowed
range whose value is at most the cap `ℰ^(1/7)`, the real part of the major arc coefficient at every
even adjacent integer exceeds `c F(γ,N) ℰ^(-1/10)` up to the explicit divisor error term. This is
one of the two mechanisms the lower bound has, and it is asked for under the small conductor
hypothesis only, so it is strictly weaker than the pointwise input, which asks for it under a
disjunction that also covers the large conductors. It contains no count and no moment. -/
theorem leaf_pointwise_small_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- LEAF. Large conductor case of the pointwise lower bound: for one conductor `r` in the allowed
range that is beyond the cap `ℰ^(1/7)`, and for an even adjacent integer whose gcd with that
conductor is below `r/24`, the same lower bound holds, carried by the explicit divisor error term.
This is the second of the two mechanisms, and it is asked for under the large conductor hypothesis
and the gcd hypothesis only, so it is strictly weaker than the pointwise input, which asks for it
under a disjunction that also covers the small conductors. It contains no count and no moment. -/
theorem leaf_pointwise_large_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            calE γ κ N ^ (1 / 7 : ℝ) < (r : ℝ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24 →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  sorry

/-- Assembly of the pointwise input from the three pieces. The caps, the constant `c` and the
coefficient `A` are merged by minimum and maximum respectively; the threshold is the maximum of the
three thresholds and of `1`; the conductor comes from the range piece; and the disjunction of the
conductor hypothesis decides which of the two case pieces is applied. Every step is proved. -/
theorem leaf_pointwise_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  classical
  obtain ⟨δs, hδs, hs⟩ := leaf_pointwise_small_conductor γ h1 h2
  obtain ⟨δl, hδl, hl⟩ := leaf_pointwise_large_conductor γ h1 h2
  refine ⟨min δs δl, lt_min hδs hδl, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κs, hκs, hs⟩ := hs δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κl, hκl, hl⟩ := hl δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κs κl, lt_min hκs hκl, fun κ hκ hκsmall => ?_⟩
  obtain ⟨cs, As, hcs, hAs, Ns, hs⟩ := hs κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨cl, Al, hcl, hAl, Nl, hl⟩ := hl κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨min cs cl, max As Al, lt_min hcs hcl, lt_of_lt_of_le hAs (le_max_left _ _),
    max 1 (max Ns Nl), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNs : Ns ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNl : Nl ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨r, hr1, hrP⟩ := leaf_conductor_in_range γ δ hδ N hN1
  refine ⟨r, hr1, hrP, fun j hj n hnw hne hnm hdisj => ?_⟩
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hEnn : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
  have hP : 0 ≤ F γ N ^ (6 * δ) := (Real.rpow_pos_of_pos (Real.exp_pos _) _).le
  have hdv : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
    divisorError_nonneg r _ _ hP
  have hc1 : min cs cl * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      cs * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hX) hEnn
  have hc2 : min cs cl * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      cl * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hX) hEnn
  by_cases hsmall : (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ)
  · have h := hs N hNs r hr1 hrP hsmall j hj n hnw hne hnm
    have hA1 : As * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
        max As Al * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) hdv
    linarith
  · have h := hl N hNl r hr1 hrP (lt_of_not_ge hsmall) j hj n hnw hne hnm
      (hdisj.resolve_left hsmall)
    have hA2 : Al * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
        max As Al * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hX) hdv
    linarith

end LeanLab.ExceptionalSet.Supply465
