/-
P0083 Perelli 1996, pages 484 and 485, equations 18 through 25.
ROUTE BURST S79 burst-20261122 split of Decomp88.leaf_character.
The density estimate 21 is the existing Decomp582a.leaf_zero_density, shared with
the Theorem 2 route, so it is named once. Display 24, the removal of the bad
characters, and display 25, the good character mean, are new LEAFs.
The combination of 24 and 25 into the leaf_character statement is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp582a

namespace LeanLab.Perelli1996.Char1122
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp582a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section

attribute [local instance] Classical.propDecidable

/-- Page 484 display 18. A character χ is good when L(s,χ) has no zeros in the
rectangle 1 - 10 (B/ε) log L / L ≤ σ ≤ 1, |t| ≤ N, with L = log N. The point s = 1
is excluded because L(s,χ₀) has a pole there, not a zero. -/
def goodCharacter (B ε N : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, s ≠ 1 → 1 - 10 * (B / ε) * Real.log (Real.log N) / Real.log N ≤ s.re →
    s.re ≤ 1 → |s.im| ≤ N → DirichletCharacter.LFunction χ s ≠ 0

/-- Page 485, the good character part of displays 23 through 25:
q/φ(q) times the sum over good χ mod q of the integral of |W(χ,η)|² over
|η| ≤ 1/(qQ), with W the existing Decomp582a.twistedRemainder. -/
def goodEnergy (B ε N : ℝ) (M q : ℕ) [NeZero q] (Q : ℝ) : ℝ :=
  (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
    if goodCharacter B ε N χ then
      ∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)), ‖twistedRemainder M χ η‖ ^ 2
    else 0

/-- The density hypothesis in exactly the form of Decomp582a.leaf_zero_density,
display 21 on page 485. -/
def DensityInput (C d : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
    ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
        σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      (∑ χ : DirichletCharacter ℂ q,
        ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
        C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) * Real.log ((q : ℝ) * T) ^ d

/-- LEAF: Page 485 display 24, from the character expansion before display 16 on
page 484, the zero free region 19 with Siegel's theorem giving 20, the bad character
count 22 from the density estimate 21, the Gauss sum bound τ(χ) ≪ q^(1/2) in 23
and Parseval for the bad characters with ε' = ε/(200 B).
Class HARD. CONDITIONAL ON display 21 through hDensity. Cited inputs:
Prachar Chapter 8 and Siegel's theorem for 19. -/
theorem leaf_bad_character_removal (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤
        C' * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := by
  sorry

/-- LEAF: Page 485 display 25, arguing as in Perelli and Pintz 1993 Section 5
equations 21 through 26: the truncated explicit formula and the short interval
smoothing for the good characters, with the density estimate 21, give
q/φ(q) ∑_{χ good} ∫_{|η| ≤ 1/(qQ)} |W(χ,η)|² ≪ N L^(-B).
The printed last step of 25 bounds this by L^(c₅) N L^(-12kB) + N L^(-B), which is
≪ N L^(-B) once B ≥ B₀ with B₀ depending on c₅ and k, so the LEAF is stated for B ≥ B₀,
as the paper uses it with B large in terms of A. Class HARD.
CONDITIONAL ON display 21 through hDensity. -/
theorem leaf_good_character_mean (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d) (hDensity : DensityInput C d)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C' N₀ : ℝ, 0 < C' ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ fareyOrder F N H B →
        goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) ≤ C' * N * Real.log N ^ (-B) := by
  sorry

/-- Pages 484 and 485 displays 16 through 25. The exact statement of
Decomp88.leaf_character, restricted to B ≥ B₀, CONDITIONAL ON Decomp582a.leaf_zero_density and the two
LEAFs above, for B at least the B₀ of leaf_good_character_mean.
The assembly itself has no sorry. -/
theorem leaf_character_of_split (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ ε B : ℝ, 0 < ε → B₀ ≤ B →
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ fareyOrder F N H B →
      ∀ a : ℤ, Nat.Coprime a.natAbs q →
      (∫ η in (-(1 / ((q : ℝ) * fareyOrder F N H B)))..
        (1 / ((q : ℝ) * fareyOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q a η‖ ^ 2) ≤ C * N * Real.log N ^ (-B) := by
  obtain ⟨CD, d, hCD, hd, hDensity⟩ := leaf_zero_density
  obtain ⟨B₀, hB₀, h25all⟩ := leaf_good_character_mean F hF CD d hCD hd hDensity c hc
  refine ⟨B₀, hB₀, ?_⟩
  intro ε B hε hBB
  have hB : 0 < B := hB₀.trans_le hBB
  obtain ⟨C1, N1, hC1, hN1, h24⟩ :=
    leaf_bad_character_removal F hF CD d hCD hd hDensity c hc ε B hε hB
  obtain ⟨C2, N2, hC2, hN2, h25⟩ := h25all ε B hε hBB
  refine ⟨C1 * (C2 + 1), max N1 N2, by positivity, hN1.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q hq hqQ a hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  have hb := h24 N H ((le_max_left _ _).trans hN) hH hHu q hqQ a hcop
  have hg := h25 N H ((le_max_right _ _).trans hN) hH hHu q hqQ
  have hN0 : 0 < N := by linarith [hN1.trans ((le_max_left N1 N2).trans hN)]
  have hP : 0 ≤ N * Real.log N ^ (-B) := by
    have : 0 < Real.log N := Real.log_pos (by linarith [hN1.trans ((le_max_left N1 N2).trans hN)])
    positivity
  calc _ ≤ C1 * (goodEnergy B ε N ⌊c * N⌋₊ q (fareyOrder F N H B) +
          N * Real.log N ^ (-B)) := hb
    _ ≤ C1 * (C2 * N * Real.log N ^ (-B) + N * Real.log N ^ (-B)) := by gcongr
    _ = C1 * (C2 + 1) * N * Real.log N ^ (-B) := by ring

end
end LeanLab.Perelli1996.Char1122
