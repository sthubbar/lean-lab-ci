import LeanLab.ExceptionalSet.Decomp553a

/-! P0082 page369 displays37 to39, derived block decomposition.
AI wrote the Lean code. Goldbach is open. -/
namespace LeanLab.ExceptionalSet.Decomp553b
open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- P0082 page369 display37, the assigned high_j0 index block. -/
noncomputable def indices_high_j0 (γ : ℝ) (N : ℕ) : Finset ℕ :=
  ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4)

/-- P0082 page369 before display39, the block has at most N terms. -/
theorem indices_high_j0_card (γ : ℝ) (N : ℕ) : (indices_high_j0 γ N).card ≤ N := by
  unfold indices_high_j0
  exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans
    (by rw [Nat.card_Ioc]; omega))

/-- LEAF. P0082 page369 display39, derived high_j0 inner mass subproblem.
Only the large phase section is bounded. There is no squared moment here.
The finite Gram and small phase steps are proved separately. -/
theorem leaf_inner_high_j0 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖},
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  sorry

/-- P0082 page369 displays37 to39, exact supply for the assigned block.
CONDITIONAL ON leaf_inner_high_j0. No source leaf is changed. -/
theorem leaf_moment_high_j0_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  exact eventual_block_moment γ h1 h2 (indices_high_j0 γ)
    (fun n => F γ n - (0 : ℤ)) (indices_high_j0_card γ) (leaf_inner_high_j0 γ h1 h2)

end LeanLab.ExceptionalSet.Decomp553b
