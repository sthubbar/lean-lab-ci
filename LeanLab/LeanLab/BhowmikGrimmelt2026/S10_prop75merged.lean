/-
S10, burst-20261124, step prop75merged. P0029 Bhowmik and Grimmelt 2026, Section 7, proof of
Proposition 7.5, pages 27 and 28.

Target: the merged estimate, the mean square over `N ≤ X` of `I - N 𝔖(N) - 𝓜 - 𝒵`, with `I`
the smoothed major arc integral at `R = X ^ ϑ`, `η = R ^ (-1/4)`, `T_q = η X q / R`. This is the
hypothesis `hmerged` of `leaf_main_iff_zero_pair_S10` and the conclusion of
`merged_of_prop75_S10` on branch claude/BhowmikGrimmelt2026-prop75main.

The paper's route from `I` to `N 𝔖(N) + 𝓜 + 𝒵`, which we split into four leaves:
* `leaf_char_expansion_S10`, display 7.10 page 27: `I` against the character expansion
  `Σ A_q(N; χ₁, χ₂) Σ_q^φ(N; χ₁, χ₂)` of display 7.11.
* `leaf_inner_lemma74_S10`, display 7.13 page 28: the first use of Lemma 7.4, on the inner
  sum over `n₂`, turning the character expansion into `innerExpS10`.
* `leaf_outer_lemma74_S10`, the pole pole, pole zero and zero zero display page 28: the second
  use of Lemma 7.4, on the outer sum over `n₁`, turning `innerExpS10` into the pole pole sum
  plus `𝓜` of display 7.15 plus `𝒵` of display 7.16.
* `leaf_pole_pole_S10`, the term `N 𝔖(N)` of display 7.17 page 28 with display 7.20 page 29 at
  `ρ₁ = ρ₂ = 1`: the pole pole sum against `N 𝔖(N)`.

Each leaf is a mean square estimate with the right hand side shape of display 7.17. The paper
states 7.10 and the two uses of 7.12 as identities up to `O_A(N ^ (-A))`; the mean square form
is what the assembly needs, and it is implied by the pointwise forms. `merged_split_S10` is
the assembly, without sorry, from the four leaves.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ## Definitions, each the display it names -/

/-- `Σ_q^φ(N; χ₁, χ₂)`, display 7.11 page 27, at `T = T_q`:
`Σ_{n₁, n₂ ≥ 1} Λ(n₁) Λ(n₂) φ(n₁/N) φ(n₂/N) χ₁(n₁) χ₂(n₂) G_T(N - n₁ - n₂)`. The sum is
finite since `φ(n/N) = 0` for `n ≥ N`; `n = 0` has `Λ(0) = 0`. -/
noncomputable def SigPhiS10 (ϕ G : ℝ → ℝ) (N : ℕ) (T : ℝ) {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) : ℂ :=
  ∑ n₁ ∈ Finset.range (N + 1), ∑ n₂ ∈ Finset.range (N + 1),
    ((vonMangoldt n₁ * vonMangoldt n₂ * ϕ (n₁ / N) * ϕ (n₂ / N) *
      GT G T ((N : ℝ) - n₁ - n₂) : ℝ) : ℂ) * χ₁ n₁ * χ₂ n₂

/-- The right hand side of display 7.10 page 27: the sum over primitive `χ₁ mod r₁`,
`χ₂ mod r₂`, `r₁, r₂ ≤ R`, and `q ≤ R` of `A_q(N; χ₁, χ₂) Σ_q^φ(N; χ₁, χ₂)`; `Aq` vanishes
unless `[r₁, r₂] | q`. Indexed as in `EM`, with `r + 1` and `q + 1` for `r, q < ⌊R⌋`. -/
noncomputable def charExpS10 (ϕ G : ℝ → ℝ) (N : ℕ) (R : ℝ) (T : ℕ → ℝ) : ℂ :=
  ∑ r₁ ∈ Finset.range ⌊R⌋₊, ∑ r₂ ∈ Finset.range ⌊R⌋₊,
    ∑ χ₁ : DirichletCharacter ℂ (r₁ + 1), ∑ χ₂ : DirichletCharacter ℂ (r₂ + 1),
      if χ₁.IsPrimitive ∧ χ₂.IsPrimitive then
        ∑ q ∈ Finset.range ⌊R⌋₊, Aq χ₁ χ₂ N (q + 1) * SigPhiS10 ϕ G N (T (q + 1)) χ₁ χ₂
      else 0

/-- `Ψ_{n₁}(t) = φ(n₁/N) φ(t/N) G_T(N - n₁ - t)`, page 28, first line of Section 7.4. -/
noncomputable def PsiS10 (ϕ G : ℝ → ℝ) (N n₁ : ℕ) (T : ℝ) (t : ℝ) : ℝ :=
  ϕ (n₁ / N) * ϕ (t / N) * GT G T ((N : ℝ) - n₁ - t)

/-- The character expansion after the first use of Lemma 7.4, display 7.13 page 28: in each
`Σ_q^φ = Σ_{n₁} Λ(n₁) χ₁(n₁) Σ_{n₂} Λ(n₂) χ₂(n₂) Ψ_{n₁}(n₂)` the inner sum is replaced by
`1_{χ₂ = χ₀^{(1)}} ∫₀^∞ Ψ_{n₁} - Σ_{ρ₂} ∫₀^∞ Ψ_{n₁}(t) t^{ρ₂ - 1} dt`, zeros of `L(s, χ₂)`
with multiplicity, as in `Lemma74`. -/
noncomputable def innerExpS10 (ϕ G : ℝ → ℝ) (N : ℕ) (R : ℝ) (T : ℕ → ℝ) : ℂ :=
  ∑ r₁ ∈ Finset.range ⌊R⌋₊, ∑ r₂ ∈ Finset.range ⌊R⌋₊,
    ∑ χ₁ : DirichletCharacter ℂ (r₁ + 1), ∑ χ₂ : DirichletCharacter ℂ (r₂ + 1),
      if χ₁.IsPrimitive ∧ χ₂.IsPrimitive then
        ∑ q ∈ Finset.range ⌊R⌋₊, Aq χ₁ χ₂ N (q + 1) *
          ∑ n₁ ∈ Finset.range (N + 1), (vonMangoldt n₁ : ℂ) * χ₁ n₁ *
            ((if χ₂ = 1 then ∫ t in Set.Ioi (0 : ℝ), (PsiS10 ϕ G N n₁ (T (q + 1)) t : ℂ)
              else 0) -
             ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ₂ ρ = 0},
               (mult χ₂ ρ : ℂ) * mellinR (PsiS10 ϕ G N n₁ (T (q + 1))) ρ)
      else 0

/-- The pole pole sum, line (pole–pole) of the display on page 28 summed against `A_q`: only
`χ₁ = χ₂ = χ₀^{(1)}` contributes, giving `Σ_{q ≤ R} A_q(N; χ₀, χ₀) I_q^φ(N; 1, 1)`. -/
noncomputable def polePoleS10 (ϕ G : ℝ → ℝ) (N : ℕ) (R : ℝ) (T : ℕ → ℝ) : ℂ :=
  ∑ q ∈ Finset.range ⌊R⌋₊, Aq chi1 chi1 N (q + 1) * Iphi ϕ G N (T (q + 1)) 1 1

/-! ## Leaves. Scales throughout: `R = X ^ ϑ`, `T_q = R ^ (-1/4) X q / R`. -/

/-- LEAF: display 7.10, page 27, the character expansion of the smoothed integral. Class
MEDIUM. The paper writes 7.10 as an identity "by the same computation as in (5.1)"; read in
mean square with the shape of 7.17, since the induced versus primitive characters differ at
prime powers dividing `q`, see the note. -/
theorem leaf_char_expansion_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) -
          charExpS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF: display 7.13, page 28, the first use of Lemma 7.4, display 7.12 page 27, on the inner
sum over `n₂` with `S = N/5`. Class MEDIUM. The `O_A(N ^ (-A))` errors, summed over `n₁ ≤ N`,
`q ≤ R` and the characters against `A_q`, are small in mean square. -/
theorem leaf_inner_lemma74_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖charExpS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          innerExpS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF: the display with lines (pole–pole), (pole–zero), (zero–zero), page 28, the second use
of Lemma 7.4 on the outer sum over `n₁`, summed against `A_q` and regrouped by the definitions
7.15 of `𝓜` and 7.16 of `𝒵`. Class HARD: the outer weight
`u ↦ φ(u/N) ∫₀^∞ φ(t/N) G_T(N - u - t) t^{ρ₂ - 1} dt` is complex valued and the zero sums must
be interchanged with the sums over `q` and the characters. -/
theorem leaf_outer_lemma74_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖innerExpS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-- LEAF: the main term `N 𝔖(N)` of display 7.17, page 28, from the pole pole sum by display
7.20 page 29 at `ρ₁ = ρ₂ = 1` with `B_φ(1, 1) = 1` by 7.1, and the tail `q > R` of the
singular series. Class MEDIUM. -/
theorem leaf_pole_pole_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖polePoleS10 ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          N * singular N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  sorry

/-! ## Mechanical steps, PROVED -/

/-- `‖a + b + c + d‖ ^ 2 ≤ 4 (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2)`. PROVED. -/
theorem norm_add4_sq_le_S10 (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
  have h0 : 0 ≤ ‖a + b + c + d‖ := norm_nonneg _
  have hsq : ‖a + b + c + d‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) ^ 2 := by
    rw [pow_two, pow_two]; exact mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- Abstract four term mean square addition: if each of `f₁, f₂, f₃, f₄` has mean square at
most `Cᵢ B X`, so does their sum with constant `4 (C₁ + C₂ + C₃ + C₄)`. PROVED. -/
theorem ms_add4_S10 (f₁ f₂ f₃ f₄ : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (h₁ : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f₁ X N‖ ^ 2 ≤ C * B X)
    (h₂ : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f₂ X N‖ ^ 2 ≤ C * B X)
    (h₃ : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f₃ X N‖ ^ 2 ≤ C * B X)
    (h₄ : ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f₄ X N‖ ^ 2 ≤ C * B X) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X, ‖f₁ X N + f₂ X N + f₃ X N + f₄ X N‖ ^ 2 ≤ C * B X := by
  obtain ⟨C₁, h₁⟩ := h₁
  obtain ⟨C₂, h₂⟩ := h₂
  obtain ⟨C₃, h₃⟩ := h₃
  obtain ⟨C₄, h₄⟩ := h₄
  refine ⟨4 * (C₁ + C₂ + C₃ + C₄), fun X hX => ?_⟩
  calc ∑ N ∈ Finset.Icc 1 X, ‖f₁ X N + f₂ X N + f₃ X N + f₄ X N‖ ^ 2
      ≤ ∑ N ∈ Finset.Icc 1 X,
          4 * (‖f₁ X N‖ ^ 2 + ‖f₂ X N‖ ^ 2 + ‖f₃ X N‖ ^ 2 + ‖f₄ X N‖ ^ 2) :=
        Finset.sum_le_sum fun N _ => norm_add4_sq_le_S10 _ _ _ _
    _ = 4 * (∑ N ∈ Finset.Icc 1 X, ‖f₁ X N‖ ^ 2 + ∑ N ∈ Finset.Icc 1 X, ‖f₂ X N‖ ^ 2 +
          ∑ N ∈ Finset.Icc 1 X, ‖f₃ X N‖ ^ 2 + ∑ N ∈ Finset.Icc 1 X, ‖f₄ X N‖ ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
    _ ≤ 4 * (C₁ * B X + C₂ * B X + C₃ * B X + C₄ * B X) := by
        linarith [h₁ X hX, h₂ X hX, h₃ X hX, h₄ X hX]
    _ = 4 * (C₁ + C₂ + C₃ + C₄) * B X := by ring

/-- Assembly, without sorry: the four leaves give the merged estimate, exactly the statement
of the hypothesis `hmerged` of `leaf_main_iff_zero_pair_S10` and of the conclusion of
`merged_of_prop75_S10`. The pointwise identity is
`I - N 𝔖 - 𝓜 - 𝒵 = (I - E) + (E - E') + (E' - P - 𝓜 - 𝒵) + (P - N 𝔖)`. -/
theorem merged_split_S10 (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) - N * singular N -
          Mterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) -
          Zterm ϕ G N ((X : ℝ) ^ ϑ)
            (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ)‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  set Tf : ℕ → ℕ → ℝ := fun X q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ
    with hTf
  set I : ℕ → ℕ → ℂ := fun X N => ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
      bRhat G ((X : ℝ) ^ ϑ) (Tf X) α * ee (-(N * α)) with hI
  set B : ℕ → ℝ := fun X => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5
    with hB
  have fix : ∀ (f : ℕ → ℕ → ℂ),
      (∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5) →
      ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∑ N ∈ Finset.Icc 1 X, ‖f X N‖ ^ 2 ≤ C * B X := by
    rintro f ⟨C, hC⟩
    exact ⟨C, fun X hX => by simp only [hB]; rw [← mul_assoc]; exact hC X hX⟩
  have key := ms_add4_S10
    (fun X N => I X N - charExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X))
    (fun X N => charExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - innerExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X))
    (fun X N => innerExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) -
      polePoleS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - Mterm ϕ G N ((X : ℝ) ^ ϑ) (Tf X) -
      Zterm ϕ G N ((X : ℝ) ^ ϑ) (Tf X))
    (fun X N => polePoleS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - N * singular N) B
    (fix _ (leaf_char_expansion_S10 ϕ G hϕ hG ϑ hϑ0 hϑ))
    (fix _ (leaf_inner_lemma74_S10 ϕ G hϕ hG ϑ hϑ0 hϑ))
    (fix _ (leaf_outer_lemma74_S10 ϕ G hϕ hG ϑ hϑ0 hϑ))
    (fix _ (leaf_pole_pole_S10 ϕ G hϕ hG ϑ hϑ0 hϑ))
  obtain ⟨C, hC⟩ := key
  refine ⟨C, fun X hX => ?_⟩
  have h := hC X hX
  rw [mul_assoc]
  calc _ = ∑ N ∈ Finset.Icc 1 X,
          ‖(I X N - charExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X)) +
            (charExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - innerExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X)) +
            (innerExpS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) -
              polePoleS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - Mterm ϕ G N ((X : ℝ) ^ ϑ) (Tf X) -
              Zterm ϕ G N ((X : ℝ) ^ ϑ) (Tf X)) +
            (polePoleS10 ϕ G N ((X : ℝ) ^ ϑ) (Tf X) - N * singular N)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun N _ => ?_
        congr 2; ring
    _ ≤ C * B X := h

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.norm_add4_sq_le_S10
#print axioms LeanLab.BhowmikGrimmelt2026.ms_add4_S10
#print axioms LeanLab.BhowmikGrimmelt2026.merged_split_S10
