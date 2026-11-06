import LeanLab.ExceptionalSet.PairSplit428

/-!
Exact finite moment expansion for P0082 pages 365 and 366 displays 25 to 27.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.MomentSplit428

open Real MeasureTheory Set Finset ComplexConjugate
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun eC calE)
open LeanLab.ExceptionalSet.Decomp404e
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

/-- Exact supply for Decomp404e.leaf_moment_split. Finite Gram expansion
and measurable strip dissection require no prime cancellation input.
Source: P0082 page 365 displays 25 and 26 and page 366 display 27. -/
theorem leaf_moment_split_supplied (γ δ κ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc (N / 2) N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
      farMoment γ δ κ N + nearMoment γ δ κ N := by
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let A := truncatedDomain P X
  let s := Finset.Ioc (N / 2) N
  let G : ℝ → ℂ := fun α => Sp P X α ^ 2 * (Kfun Δ α : ℂ)
  let f : ℕ → ℝ → ℂ := fun n α => G α * eC (-(α * F γ n))
  have hG : Continuous G := by
    apply Continuous.mul
    · unfold Sp eC
      fun_prop
    · exact KernelTransform264.Kfun_continuous Δ
  have hf (n : ℕ) (_hn : n ∈ s) : IntegrableOn (f n) A := by
    have hc : Continuous (f n) := by
      apply hG.mul
      unfold eC
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.inter_subset_right
  have hconj (t : ℝ) : conj (eC t) = eC (-t) := BG2026.conj_eC t
  have hmul (u v : ℝ) : eC u * eC v = eC (u + v) := by
    unfold eC
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpoint (α β : ℝ) :
      (∑ n ∈ s, f n α * conj (f n β)) =
        G α * conj (G β) * phaseSum γ N (β - α) := by
    rw [phaseSum, mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [f]
    rw [map_mul, hconj]
    rw [show G α * eC (-(α * F γ n)) * (conj (G β) * eC (-(-(β * F γ n)))) =
      (G α * conj (G β)) * (eC (-(α * F γ n)) * eC (-(-(β * F γ n)))) by ring, hmul]
    congr 2
    ring
  have habs (z : ℝ × ℝ) :
      ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖ =
        ‖G z.1‖ * ‖G z.2‖ * ‖phaseSum γ N (z.2 - z.1)‖ := by
    rw [hpoint]
    simp only [norm_mul, Complex.norm_conj]
  have hfc (n : ℕ) (hn : n ∈ s) : IntegrableOn (fun α => conj (f n α)) A := by
    have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hf n hn)
    exact hc.congr (Filter.Eventually.of_forall (fun α => Complex.conjCLE_apply (f n α)))
  have hi : Integrable (fun z : ℝ × ℝ => ∑ n ∈ s, f n z.1 * conj (f n z.2))
      ((volume.restrict A).prod (volume.restrict A)) :=
    integrable_finsetSum s (fun n hn => (hf n hn).mul_prod (hfc n hn))
  have habsi : Integrable (fun z : ℝ × ℝ =>
      ‖G z.1‖ * ‖G z.2‖ * ‖phaseSum γ N (z.2 - z.1)‖)
      ((volume.restrict A).prod (volume.restrict A)) :=
    hi.norm.congr (Filter.Eventually.of_forall habs)
  have hsplit := PairSplit428.integral_pair_split A
    (fun z : ℝ × ℝ => ‖G z.1‖ * ‖G z.2‖ * ‖phaseSum γ N (z.2 - z.1)‖)
    (X ^ (3 * δ - 1)) habsi
  calc
    _ = ∑ n ∈ s, ‖∫ α in A, f n α‖ ^ 2 := rfl
    _ ≤ ∫ z : ℝ × ℝ, ‖∑ n ∈ s, f n z.1 * conj (f n z.2)‖
        ∂(volume.restrict A).prod (volume.restrict A) :=
      Moment385.moment_le_absolute_gram s A f hf
    _ = ∫ z : ℝ × ℝ, ‖G z.1‖ * ‖G z.2‖ * ‖phaseSum γ N (z.2 - z.1)‖
        ∂(volume.restrict A).prod (volume.restrict A) :=
      integral_congr_ae (Filter.Eventually.of_forall habs)
    _ = _ := hsplit

end LeanLab.ExceptionalSet.MomentSplit428
