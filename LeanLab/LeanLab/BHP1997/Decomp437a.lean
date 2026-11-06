/-
P0069, page 13, Case 1 after displays 3.11 and 3.12.
The one-polynomial dominant square moment is supplied by Decomp437e.
The pair estimate and exact Case 1 assembly use no direct sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437e

namespace LeanLab.BHP1997.Decomp437a
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a
open scoped BigOperators

/-- LEAF. Pages 12 and 13, displays 3.11 and 3.12 and Case 1.
Sum the second moment only where its first cardinality term dominates.
The logarithmic loss includes the coefficient energy and the dyadic levels.
This concerns one polynomial and contains neither the third factor nor its
arbitrary logarithmic saving. Supplied below from the named inputs. -/
theorem dominant_square_moment (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 →
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, CoeffBound a B →
    2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
    (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      C * F * Real.log x ^ D := by
  exact Decomp437e.dominant_square_moment hmean hlarge henergy

/-- Page 13, Case 1. Cauchy Schwarz combines the two dominant square moments.
The explicit hypotheses are finite moment bounds, not cited theorems. -/
theorem pair_of_square_bounds {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {C M N L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hf : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ C * M * L)
    (hg : (∑ p ∈ S, ‖g p‖ ^ 2) ≤ C * N * L) :
    (∑ p ∈ S, ‖f p * g p‖) ≤ C * Real.sqrt M * Real.sqrt N * L := by
  simp_rw [norm_mul]
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => ‖f p‖) (fun p => ‖g p‖)
  have hs := mul_le_mul hf hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (mul_nonneg hC hM) hL)
  have he : (C * Real.sqrt M * Real.sqrt N * L) ^ 2 = (C * M * L) * (C * N * L) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hN]
    ring
  have hp : 0 ≤ C * Real.sqrt M * Real.sqrt N * L := by positivity
  nlinarith

/-- Page 13, Case 1. Extract the uniform third-factor bound from the finite sum. -/
theorem triple_of_pair_bound {ι : Type*} (S : Finset ι) (f g e : ι → ℂ)
    {H U : ℝ} (hU : 0 ≤ U)
    (hpair : (∑ p ∈ S, ‖f p * g p‖) ≤ H)
    (he : ∀ p ∈ S, ‖e p‖ ≤ U) :
    (∑ p ∈ S, ‖f p * g p * e p‖) ≤ H * U := by
  calc
    _ ≤ ∑ p ∈ S, ‖f p * g p‖ * U := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he p hp) (norm_nonneg _)
    _ = (∑ p ∈ S, ‖f p * g p‖) * U := (Finset.sum_mul ..).symm
    _ ≤ H * U := mul_le_mul_of_nonneg_right hpair hU

/-- Page 13, exact original Case 1 target from the smaller single-polynomial moment.
CONDITIONAL on the three original analytic inputs. -/
theorem both_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C, D, hC, hD, hm⟩ := dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  let A' := A + D
  have hA' : 0 < A' := by dsimp [A']; linarith
  refine ⟨C * |K A'|, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let P := casePart S
    (fun p => dominanceFlag ((q : ℝ) * T) M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag ((q : ℝ) * T) N (dirPoly b c₁ c₂ N p.2 (half p.1))) true true
  have hsub : P ⊆ S := Finset.filter_subset _ _
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hma := hm x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.1)
  have hmb := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.2)
  have hMN := pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hC.le
    (by dsimp [M]; positivity) (by dsimp [N]; positivity)
    (Real.rpow_nonneg (Real.log_nonneg (by linarith)) D) hma hmb
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hthird : ∀ p ∈ P, ‖dirPoly e c₁ c₂ L p.2 (half p.1)‖ ≤
      |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
    intro p hp
    exact (hsmall A' hA' p (hsub hp)).trans (by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have htriple := triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by positivity : 0 ≤ |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) hMN hthird
  have hXpos : 0 < X := by
    rcases hX with rfl | rfl
    · linarith
    · positivity
  have hsqrt : Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ) = X ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    dsimp [M, N, L]
    rw [← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le,
      ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    congr 1
    ring
  have hlog : Real.log x ^ D * Real.log x ^ (-A') = Real.log x ^ (-A) := by
    rw [← Real.rpow_add (Real.log_pos (by linarith : 1 < x))]
    congr 1
    dsimp [A']
    ring
  calc
    _ ≤ (C * Real.sqrt M * Real.sqrt N * Real.log x ^ D) *
        (|K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) := htriple
    _ = C * |K A'| * (Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ)) *
        (Real.log x ^ D * Real.log x ^ (-A')) := by ring
    _ = _ := by rw [hsqrt, hlog]

end LeanLab.BHP1997.Decomp437a
