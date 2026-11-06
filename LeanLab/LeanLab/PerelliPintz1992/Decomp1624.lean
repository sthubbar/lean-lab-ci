/-
P0070, pages 364 and 365. A re-cut of estimate 7 around display 27 for unit U-1624.
Display 27 is stated through the printed W. That W is clipped to n in [N, 2N] and uses window 2 q Q
at radius `1 / (q Q)`. The kernel of a window 2 q Q vanishes at `1 / (2 q Q)`, inside that radius.
The fixed ends N and 2 N of the clipped sum are also not averaged by the integral over x.
Here W is replaced by an averaged window quantity with window q Q / 2, a constant change of window
that lies in the printed theta range, and with the sum unclipped. The two leaves are OPEN.
The Theorem of the paper is not refuted. The assembly has no sorry of its own and is
CONDITIONAL on the two leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Decomp97

namespace LeanLab.PerelliPintz1992.Decomp1624
open Real ArithmeticFunction MeasureTheory Set Filter Topology Decomp97
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 365, the unclipped moving sum with the centering of W. -/
def movingSum {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x h : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊,
    ((Λ n : ℂ) * χ (n : ZMod (q : ℕ)) - if χ = 1 then 1 else 0)

/-- Page 365, the unclipped mean square on the printed range N / 2 to 3 N, at one window. -/
def windowMean (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (h : ℝ) : ℝ :=
  ∫ x in Ioc ((N : ℝ) / 2) (3 * N : ℝ), ‖movingSum χ x h‖ ^ 2

/-- The Gallagher window q Q / 2. Its kernel has no zero on the Farey radius `1 / (q Q)`. -/
def gallagherWindow (N : ℕ) (q : ℕ+) : ℝ := (q : ℝ) * Q N / 2

/-- The averaged W. Page 364 gives the first term with the window changed by a constant. The
second term is the average over the moving end of J, which replaces the fixed end of the clipped
sum: an end point averaged over a block of length `N L ^ (-K)` gives all windows up to q Q / 2. -/
def WA (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) : ℝ :=
  Real.sqrt ((1 / (((q : ℝ) * Q N) ^ 2 * N)) *
    (windowMean N χ (gallagherWindow N q) +
      (1 / gallagherWindow N q) *
        ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u))

/-- The character expression of 27 on p. 364, with WA in place of W. -/
def energyA (N : ℕ) (ε ξ : ℝ) (M : ℕ) : ℝ :=
  (1 / (M : ℝ) ^ 2) * ∑ q ∈ Y N ε ξ M,
    (∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA N χ) ^ 2

/-- The averaged energy is nonnegative. -/
theorem energyA_nonneg (N : ℕ) (ε ξ : ℝ) (M : ℕ) : 0 ≤ energyA N ε ξ M := by
  unfold energyA
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun q _ => sq_nonneg _

/-- Vacuity instance. The hypothesis of `reduction27A` holds for some E at every N, ε and ξ.
PROVED. Plain math: a finite family of reals is bounded above. -/
theorem energyA_bound_exists (N : ℕ) (ε ξ : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E := by
  refine ⟨∑ M ∈ Finset.range (⌊Q N⌋₊ + 1), energyA N ε ξ M,
    Finset.sum_nonneg fun M _ => energyA_nonneg N ε ξ M, ?_⟩
  intro M _ hM
  have hmem : M ∈ Finset.range (⌊Q N⌋₊ + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_floor hM)
  exact Finset.single_le_sum (f := fun M => energyA N ε ξ M)
    (fun M _ => energyA_nonneg N ε ξ M) hmem

/-- LEAF. Pages 363 and 364, displays 22 to 27, with WA in place of W. The route: replace the
range [N, 2 N] by [a, b] with a and b in end blocks of length `N L ^ (-K)`, at a cost `N L ^ (1 - K)`
by Parseval, average over a and b, then use Gallagher's lemma, P. X. Gallagher, Invent. Math. 11,
1970, pp. 329 to 339, at window q Q / 2 and radius `1 / (q Q)`. The exponent c depends on A. -/
theorem reduction27A :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  sorry

/-- LEAF. Sections 5 and 6, pp. 365 to 372, for WA. The zero sum of display 31 is monotone in
the window through `min(Θ, 1 / |ρ|)`, so all windows up to q Q / 2 are served by the printed proof.
The open sign question in ZeroFreeInputs remains separate. -/
theorem energy_decayA :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 12 → ∀ D : ℝ, 0 < D →
      ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
        ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ C * L N ^ (-D) := by
  sorry

/-- The exact existing Estimate7 Prop from the re-cut leaves.
CONDITIONAL ON reduction27A and energy_decayA. This does not prove either leaf. -/
theorem estimate7_recut : Estimate7 := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27A
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decayA ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ hξ hξ'
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have he := hbound N hN₀ ξ hξ hξ' (K * L N ^ (-(A + 1 + c)))
    (by positivity) (hdecay N hN₁ ξ hξ hξ')
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

#print axioms energyA_nonneg
#print axioms energyA_bound_exists
#print axioms estimate7_recut

end
end LeanLab.PerelliPintz1992.Decomp1624
