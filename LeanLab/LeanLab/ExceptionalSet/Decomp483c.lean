import LeanLab.ExceptionalSet.Decomp483a
import LeanLab.ExceptionalSet.Moment385

/-!
P0082 page369 displays37 and38.
The shifted moment has an integrable Gram kernel with the exact parity phase sum.
The coarse existing weighted energy estimate loses all exponential saving.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483c
open Real Finset MeasureTheory ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp eC)

/-- P0082 page369 display37, derived absolute form. The shifted finite moment
is bounded by the explicit phase weighted Gram integral. Its integrability is included. -/
theorem shifted_moment_gram_bound (P X Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : Finset ℕ) (v : ℕ → ℝ) (A : Set ℝ) :
    let G := fun α : ℝ => Sp P X α ^ 2 * OddKernel467.evenKernel Δ α
    Integrable (fun z : ℝ × ℝ => ‖G z.1‖ * ‖G z.2‖ *
      ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖)
      ((volume.restrict A).prod (volume.restrict A)) ∧
    (∑ n ∈ s, ‖∫ α in A, OddTail467.integrand P X Δ (v n) α‖ ^ 2) ≤
      ∫ z : ℝ × ℝ, ‖G z.1‖ * ‖G z.2‖ *
        ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖
        ∂(volume.restrict A).prod (volume.restrict A) := by
  dsimp only
  let G := fun α : ℝ => Sp P X α ^ 2 * OddKernel467.evenKernel Δ α
  let f := fun n α => G α * eC (-(α * v n))
  have hf (n : ℕ) (_ : n ∈ s) : IntegrableOn (f n) A :=
    (OddTail467.total_integrable P X Δ (v n) hΔ hΔ1).integrableOn
  have hconj (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hpoint (α β : ℝ) :
      (∑ n ∈ s, f n α * conj (f n β)) =
        G α * conj (G β) * ∑ n ∈ s, eC ((β - α) * v n) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    dsimp only [f]
    rw [map_mul, hconj]
    rw [show G α * eC (-(α * v n)) * (conj (G β) * eC (-(-(β * v n)))) =
      (G α * conj (G β)) * (eC (-(α * v n)) * eC (-(-(β * v n)))) by ring,
      ← Fejer467.phase_add]
    congr 2
    ring
  have habs (z : ℝ × ℝ) :
      ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖ =
        ‖G z.1‖ * ‖G z.2‖ * ‖∑ n ∈ s, eC ((z.2 - z.1) * v n)‖ := by
    rw [hpoint]
    simp only [norm_mul, Complex.norm_conj]
  have hfc (n : ℕ) (hn : n ∈ s) :
      IntegrableOn (fun α => conj (f n α)) A := by
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hf n hn)
    exact hc.congr (Filter.Eventually.of_forall (fun α => Complex.conjCLE_apply (f n α)))
  have hi : Integrable (fun z : ℝ × ℝ => ∑ n ∈ s, f n z.1 * conj (f n z.2))
      ((volume.restrict A).prod (volume.restrict A)) :=
    integrable_finsetSum s (fun n hn => (hf n hn).mul_prod (hfc n hn))
  refine ⟨hi.norm.congr (Filter.Eventually.of_forall habs), ?_⟩
  calc _ ≤ ∫ z : ℝ × ℝ, ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖
      ∂(volume.restrict A).prod (volume.restrict A) :=
        Moment385.moment_le_absolute_gram s A f hf
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall habs)

/-- P0082 page369 display38, auxiliary negative result about the existing
coarse weighted energy supply. Its inverse Delta loss cancels the entire
small phase saving at the printed width. This does not refute the paper estimate. -/
theorem coarse_energy_no_saving (E : ℝ) (hE : 1 < E) :
    E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 = 1 ∧
      E ^ (-(1 / 3 : ℝ)) < E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 := by
  have hE0 : 0 < E := zero_lt_one.trans hE
  have heq : E ^ (-(2 / 3 : ℝ)) / (E ^ (-(1 / 3 : ℝ))) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast hE0.le, ← Real.rpow_sub hE0]
    norm_num
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)

end LeanLab.ExceptionalSet.Decomp483c
