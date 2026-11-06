import LeanLab.ExceptionalSet.TailSupply385

/-!
The finite Gram expansion used in P0082 page 365 displays 25 and 26.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Moment385

open MeasureTheory Set ComplexConjugate

/-- Squaring finitely many integrals gives their Gram integral on the product measure.
Source: P0082 page 365, the expansion from display 25 to display 26. -/
theorem moment_gram (s : Finset ℕ) (A : Set ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n ∈ s, IntegrableOn (f n) A) :
    (∑ n ∈ s, ‖∫ x in A, f n x‖ ^ 2) =
      (∫ z : ℝ × ℝ, ∑ n ∈ s, f n z.1 * conj (f n z.2)
        ∂(volume.restrict A).prod (volume.restrict A)).re := by
  have hfc (n : ℕ) (hn : n ∈ s) :
      Integrable (fun x => conj (f n x)) (volume.restrict A) := by
    have hi := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hf n hn)
    exact hi.congr (Filter.Eventually.of_forall (fun x => Complex.conjCLE_apply (f n x)))
  rw [integral_finsetSum s (fun n hn => (hf n hn).mul_prod (hfc n hn))]
  have hprod (n : ℕ) :
      (∫ z : ℝ × ℝ, f n z.1 * conj (f n z.2)
        ∂(volume.restrict A).prod (volume.restrict A)) =
      (∫ x in A, f n x) * conj (∫ x in A, f n x) := by
    simpa only [integral_conj] using
      integral_prod_mul (μ := volume.restrict A) (ν := volume.restrict A)
        (f n) (fun x => conj (f n x))
  simp_rw [hprod, Complex.mul_conj']
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  norm_cast

/-- The absolute Gram integral bounds the finite squared integral moment.
Source: P0082 pages 365 and 366, displays 26 and 27. -/
theorem moment_le_absolute_gram (s : Finset ℕ) (A : Set ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n ∈ s, IntegrableOn (f n) A) :
    (∑ n ∈ s, ‖∫ x in A, f n x‖ ^ 2) ≤
      ∫ z : ℝ × ℝ, ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖
        ∂(volume.restrict A).prod (volume.restrict A) := by
  rw [moment_gram s A f hf]
  exact (Complex.re_le_norm _).trans (norm_integral_le_integral_norm _)

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE majorArcs)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

/-- The exact truncated moment is bounded by its absolute finite Gram kernel.
Source: P0082 pages 365 and 366, displays 25 to 27. -/
theorem truncated_moment_le_absolute_gram (γ δ κ : ℝ) (N : ℕ)
    (hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)))
    (hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1) :
    let P := F γ N ^ (6 * δ)
    let A := (majorArcs P (F γ N))ᶜ ∩ Icc (-P) P
    (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
      ∫ z : ℝ × ℝ,
        ‖∑ n ∈ window γ N,
          PrimeTail385.integrand P (F γ N) (calE γ κ N ^ (-(1 / 8 : ℝ))) (F γ n) z.1 *
          conj (PrimeTail385.integrand P (F γ N)
            (calE γ κ N ^ (-(1 / 8 : ℝ))) (F γ n) z.2)‖
        ∂(volume.restrict A).prod (volume.restrict A) := by
  dsimp only
  let A := (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
    Icc (-(F γ N ^ (6 * δ))) (F γ N ^ (6 * δ))
  have hf (n : ℕ) (_ : n ∈ window γ N) :
      IntegrableOn (PrimeTail385.integrand (F γ N ^ (6 * δ)) (F γ N)
        (calE γ κ N ^ (-(1 / 8 : ℝ))) (F γ n)) A :=
    (PrimeKernel264.total_integrable hΔ hΔ1 _ _ _).integrableOn
  simpa only [truncatedMinor, PrimeTail385.integrand, A] using
    moment_le_absolute_gram (window γ N) A
      (fun n => PrimeTail385.integrand (F γ N ^ (6 * δ)) (F γ N)
        (calE γ κ N ^ (-(1 / 8 : ℝ))) (F γ n)) hf

end LeanLab.ExceptionalSet.Moment385
