import LeanLab.Zhao2025.Estimate38WithError
import LeanLab.Zhao2025.RowError
import LeanLab.Zhao2025.UniformRowBudget
import LeanLab.Zhao2025.EpsilonBudget

/-!
The elementary proof of Lemma 3.1 with the additive row error retained.
The two analytic estimates remain explicit eventual inputs.
Their thresholds are chosen after the error budgets and then combined.
Identification of these finite kernels with Dirichlet zeros remains conditional.
Source: Zhao 2025, displays 2.14 and 3.3 to 3.11, pages 5, 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6825

/-- CONDITIONAL ON eventual 3.6 and eventual additive row estimates 2.14. -/
theorem lemma3_1_eventual {ι : Type*} (s : ℕ → Finset ι) (lam : ℕ → ι → ℝ)
    (G1 G2 : ℕ → ι → ι → ℝ) (k x y z L l0 H : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hL : 0 < L) (h0 : 0 ≤ l0) (hH : 0 < H)
    (hLam : ∀ q i, i ∈ s q → 0 < lam q i ∧ lam q i ≤ H)
    (hk : k = 2 * (1 / 3 + 3 * x + y + z) ∨ k = 2 * (2 / 3 + 3 * x + y + z))
    (hG1 : ∀ q i, i ∈ s q → ∀ j ∈ s q, 0 ≤ G1 q i j)
    (hG2 : ∀ q i, i ∈ s q → ∀ j ∈ s q, 0 ≤ G2 q i j)
    (hSym1 : ∀ q i, i ∈ s q → ∀ j ∈ s q, G1 q i j = G1 q j i)
    (hSym2 : ∀ q i, i ∈ s q → ∀ j ∈ s q, G2 q i j = G2 q j i)
    (h36 : ∀ e : ℝ, 0 < e → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      Estimate36 (s q) (lam q) (fun i j => Real.sqrt (G1 q i j * G2 q i j)) k x y z L e)
    (h14 : ∀ delta : ℝ, 0 < delta → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ i ∈ s q,
      (∑ j ∈ s q, G1 q i j) ≤ B (1 / 3 + x + y) (lam q i) l0 + delta ∧
      (∑ j ∈ s q, G2 q i j) ≤ B z (lam q i) l0 + delta) :
    ∀ e : ℝ, 0 < e → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      weightedCappedSum k (s q) (lam q) L ≤ (1 + e) * C x y z L l0 := by
  intro e he
  obtain ⟨d, hd, hbudget⟩ := epsilon_budget e he
  obtain ⟨delta, hdelta, hsmall⟩ := uniform_row_budget (1 / 3 + x + y) z H l0 d
    (by linarith) hz hH h0 hd
  obtain ⟨Q36, hQ36⟩ := h36 d hd
  obtain ⟨Q14, hQ14⟩ := h14 delta hdelta
  refine ⟨max Q36 Q14, ?_⟩
  intro q hq
  have hq36 : Q36 ≤ q := (le_max_left _ _).trans hq
  have hq14 : Q14 ≤ q := (le_max_right _ _).trans hq
  let A : ι → ι → ℝ := fun i j => Real.sqrt (G1 q i j * G2 q i j)
  have hA : ∀ i ∈ s q, ∀ j ∈ s q, 0 ≤ A i j := fun _ _ _ _ => Real.sqrt_nonneg _
  have hSym : ∀ i ∈ s q, ∀ j ∈ s q, A i j = A j i := by
    intro i hi j hj
    dsimp [A]
    rw [hSym1 q i hi j hj, hSym2 q i hi j hj]
  have hRows : ∀ i ∈ s q, (∑ j ∈ s q, A i j) ≤
      (1 + d) * Real.sqrt (B (1 / 3 + x + y) (lam q i) l0 * B z (lam q i) l0) := by
    intro i hi
    have hl := hLam q i hi
    have hb := hsmall (lam q i) hl.1 hl.2
    have hr := hQ14 q hq14 i hi
    exact row_error_bound (s q) (G1 q i) (G2 q i) _ _ delta d
      (B_nonneg_order _ _ _ _ (by linarith) hl.1 h0 le_rfl).1
      (B_nonneg_order _ _ _ _ hz.le hl.1 h0 le_rfl).1 hd.le hb.1 hb.2
      (hG1 q i hi) (hG2 q i hi) hr.1 hr.2
  have h38 := estimate38_with_error (s q) (lam q) A k x y z L l0 d e (1 + d)
    hx hy hz hd.le (by linarith) hbudget hA hSym hRows (hQ36 q hq36)
  exact lemma3_1_from38 (s q) (lam q) k x y z L l0 e hx hy hz hL h0
    (fun i hi => (hLam q i hi).1) hk h38

#print axioms lemma3_1_eventual
end LeanLab.Zhao2025.Task56
