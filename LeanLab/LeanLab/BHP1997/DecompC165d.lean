/-
P0069, Section 5, pages 43 to 53. The two short weight constructions
are separate leaves. Their order comes from densities below and above 1.
The exact final statement is CONDITIONAL on both OPEN leaves.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Total
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF, OPEN. Page 51, "A computer calculation yields". The numeric `E₂` input of
`lower_density_of_e2_bound`, a floating point quadrature gives about 0.9389. -/
theorem lower_two_integral_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/10^8) :
    lowerTwoDeletedIntegral ω ε ≤ 3799/4000 := by
  have hh := lower_two_integral_grid_bound hω hz hε hε'
  rw [lower_two_grid_total] at hh
  exact hh.trans (by norm_num)

/-- LEAF, OPEN. Pages 43 to 52, the lower short weight b0, with the page 51 formula for its density:
`v₀` is 1 minus the integrals over `E₂` and `E₄`. Since `lowerFourDeletedIntegral` is the
conservative superset of `E₄`, that formula is stated as a lower bound for `v₀`.
Lemmas 29 to 35 supply the moment estimates and 5.18 to 5.23 on page 52 normalize condition iv. -/
theorem lower_short_weight_analytic (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
          1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
          RightConditions ε B v0 b0 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- Pages 43 to 52, the lower short weight b0. `0.05 < v0` is now derived from the page 51 density
formula, `lower_two_integral_bound` and the proved `lower_four_discard_small`, by
`lower_density_of_e2_bound`. CONDITIONAL on the two OPEN leaves above. U-1609 dropped the unprinted
`v0 ≤ 1`. -/
theorem lower_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ RightConditions ε B v0 b0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := lower_short_weight_analytic h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v0, b0, hv0, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v0, b0, lower_density_of_e2_bound hω hz hε.le hεsmall
    (lower_two_integral_bound hω hz hε.le hεsmall) hv0, hright, X, hsandwich⟩

/-- Pages 2 and 3. Two short weights in order on the interval have their densities in the same
order. PROVED in DensityMono1609. This replaces the unprinted `v0 ≤ 1 ≤ v1`. -/
theorem right_density_mono {ε B0 B1 v0 v1 : ℝ} {b0 b1 : ℝ → ℕ → ℝ} (hε : 0 < ε)
    (h0 : RightConditions ε B0 v0 b0) (h1 : RightConditions ε B1 v1 b1)
    (hs : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, b0 x m ≤ b1 x m) : v0 ≤ v1 :=
  DecompC165b.right_density_mono hε h0 h1 hs

/-- LEAF. Page 53, the upper short weight b1. The four-term Buchstab
identity is gm minus hm plus jm minus km. Delete only km terms where
Lemma 33 is unavailable. The printed integral formula gives v1 below 2.2.
Repeat the page 52 normalization. The analytic estimates and certified
Buchstab integral remain OPEN. U-1609 dropped the unprinted `1 ≤ v1`. -/
theorem upper_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := upper_short_weight_analytic h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v1, b1, hdensity, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v1, b1, upper_density_bound hω hz hε.le hεsmall hdensity,
    hright, X, hsandwich⟩

/-- Pages 43 to 53, combine the two short constructions at one common
divisor exponent and epsilon cutoff. This is the exact statement of
DecompC165b.section5_weights. CONDITIONAL on the OPEN leaves above. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  obtain ⟨B0, η0, hη0, h0⟩ := lower_short_weight h4 h9
  obtain ⟨B1, η1, hη1, h1⟩ := upper_short_weight h4 h9
  refine ⟨max B0 B1, min η0 η1, lt_min hη0 hη1, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hb0, X0, hs0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv1, hb1, X1, hs1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  have hsand : ∀ x : ℝ, max X0 X1 ≤ x → ∀ m ∈ rightInterval ε x,
      b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := fun x hx m hm =>
    ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
      hs1 x (le_trans (le_max_right _ _) hx) m hm⟩
  have hmono : v0 ≤ v1 := right_density_mono hε hb0 hb1
    ⟨max X0 X1, fun x hx m hm => (hsand x hx m hm).1.trans (hsand x hx m hm).2⟩
  exact ⟨v0, v1, b0, b1, hv0, hmono, hv1, hb0, hb1, max X0 X1, hsand⟩

end LeanLab.BHP1997.DecompC165d
