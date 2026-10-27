/-
P0069, pages 11, 24 and 26. Positive index bookkeeping for Lemma 11.
This reuses the task78 coefficient bounds and Decomp1518 transfer congruence.
No claim resolves the normalization QUESTION for the sealed transfer predicate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.CoefficientBounds

namespace LeanLab.BakerHarmanPintz1997.Transfer90
open Finset Decomp1518
attribute [local instance] Classical.propDecidable

/-- Pages 24 and 26, equation 4.2 uses only positive coefficient indices. -/
theorem holds42_erase_zero_iff (ε : ℝ) (c : ℝ → ℕ → ℂ) :
    (Holds42 ε fun x k => if k = 0 then 0 else c x k) ↔ Holds42 ε c := by
  constructor
  · apply holds42_congr_ev
    exact ⟨0, fun x _ k hk => by simp [hk.ne']⟩
  · apply holds42_congr_ev
    exact ⟨0, fun x _ k hk => by simp [hk.ne']⟩

/-- Page 11, bound 3.1, with the irrelevant zero coefficient set to zero. -/
theorem coefficient_erase_zero {B : ℝ} {c : ℕ → ℂ}
    (h : ∀ k, 0 < k → ‖c k‖ ≤ tau k ^ B) :
    ∀ k, ‖if k = 0 then 0 else c k‖ ≤ tau k ^ B := by
  intro k
  by_cases hk : k = 0
  · simp only [hk, ite_true, norm_zero]
    exact Real.rpow_nonneg (by unfold tau; positivity) _
  · simpa [hk] using h k (Nat.pos_of_ne_zero hk)

/-- Page 26, the coefficients c prime meet 3.1 after setting the zero coefficient to zero. -/
theorem conv2T_erase_zero_bound (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B) :
    ∀ k, ‖if k = 0 then 0 else conv2T a b M N w γ k‖ ≤ tau k ^ (2 * B + 3) := by
  exact coefficient_erase_zero fun k hk => conv2T_norm_le_tau a b M N w γ B hB ha hb hk

/-- Page 26, the coefficients c double prime meet 3.1 after setting the zero coefficient to zero. -/
theorem conv2E_erase_zero_bound (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B) :
    ∀ k, ‖if k = 0 then 0 else (conv2E a b M N w γ k : ℂ)‖ ≤ tau k ^ (2 * B + 3) := by
  apply coefficient_erase_zero
  intro k hk
  rw [Complex.norm_of_nonneg (by
    unfold conv2E
    apply sum_nonneg
    intro m hm
    apply sum_nonneg
    intro n hn
    split_ifs
    · unfold psiErr; positivity
    · positivity)]
  exact conv2E_le_tau a b M N w γ B hB ha hb hk

/-- Page 24, Lemma 11 with 3.1 required only at positive indices.
CONDITIONAL ON the sealed Lemma11 and the displayed mean value hypothesis. -/
theorem lemma11_positive (h11 : Lemma11) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B : ℝ) (c : ℝ → ℕ → ℂ),
    (∀ x k, 0 < k → ‖c x k‖ ≤ tau k ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∫ t in (T0 x)..(T1 ε x),
        ‖(⟨c x, Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
        C * x ^ (1 / 2 : ℝ) / L x ^ A) → Holds42 ε c := by
  obtain ⟨ε0, hε0, h11⟩ := h11
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hεsmall B c hc hmean
  apply (holds42_erase_zero_iff ε c).mp
  apply h11 ε hε hεsmall B (fun x k => if k = 0 then 0 else c x k)
  · intro x
    exact coefficient_erase_zero (hc x)
  · intro A hA
    obtain ⟨C, X0, hC⟩ := hmean A hA
    refine ⟨C, X0, ?_⟩
    intro x hx q _ hq χ
    have heq : (⟨fun k => if k = 0 then 0 else c x k, Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ =
        (⟨c x, Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ := by
      funext s
      unfold DP.eval
      apply sum_congr rfl
      intro k hk
      have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hk).1
      simp [hkpos.ne']
    simpa only [heq] using hC x hx q hq χ

#print axioms holds42_erase_zero_iff
#print axioms coefficient_erase_zero
#print axioms conv2T_erase_zero_bound
#print axioms conv2E_erase_zero_bound
#print axioms lemma11_positive
end LeanLab.BakerHarmanPintz1997.Transfer90
