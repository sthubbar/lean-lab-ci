import LeanLab.GoldbachAverage.State124
import LeanLab.GoldbachAverage.Decomp124b

/-!
P0098 corollary to Theorem 3, page 163.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.DecompJ202
open Classical Filter Set
open Decomp124 State124 Decomp124b

/-- LEAF. P0098 corollary to Theorem 3, page 163.
A sequence of bounds going to zero can be chosen for the exceptional counts. -/
theorem epsilon_sequence : ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (nhds 0) := by
  use fun n => 1 / ((n : ℝ) + 1)
  refine ⟨?_, ?_⟩
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- LEAF. P0098 corollary to Theorem 3, page 163.
For a given function g going to infinity, we can extract an increasing sequence of cutoffs X_k
and corresponding sets P_k from Theorem 3, such that the bounds hold. -/
theorem corollary_extraction (g : ℝ → ℝ) (hg : Tendsto g atTop atTop)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε_lim : Tendsto ε atTop (nhds 0))
    (h_th3 : GranvilleTheorem3) :
    ∃ (X : ℕ → ℝ) (P_seq : ℕ → Set ℕ),
      (∀ k, 0 < X k) ∧ (Tendsto X atTop atTop) ∧
      (∀ k, ∀ p ∈ P_seq k, Nat.Prime p) ∧
      (∀ k, ∀ᶠ x : ℝ in atTop, (count (P_seq k) x : ℝ) ≤ (g (X k) / 2) * Real.sqrt x) ∧
      (∀ k, ∀ᶠ x : ℝ in atTop, (badEven (P_seq k) x : ℝ) ≤ ε k * x) := by
  sorry

/-- LEAF. P0098 corollary to Theorem 3, page 163.
Gluing the sets P_k along the cutoffs X_k yields a single set P satisfying the prime property
and the asymptotic count bound. -/
theorem corollary_gluing (g : ℝ → ℝ) (hg : Tendsto g atTop atTop)
    (X : ℕ → ℝ) (P_seq : ℕ → Set ℕ)
    (hX : ∀ k, 0 < X k) (hX_lim : Tendsto X atTop atTop)
    (hP_prime : ∀ k, ∀ p ∈ P_seq k, Nat.Prime p)
    (hP_count : ∀ k, ∀ᶠ x : ℝ in atTop, (count (P_seq k) x : ℝ) ≤ (g (X k) / 2) * Real.sqrt x) :
    ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧
      (∀ᶠ x : ℝ in atTop, (count P x : ℝ) ≤ Real.sqrt x * g x) ∧
      (∀ k, ∀ᶠ x : ℝ in atTop, P ∩ {n : ℕ | X k ≤ (n:ℝ) ∧ (n:ℝ) < X (k+1)} =
                           P_seq k ∩ {n : ℕ | X k ≤ (n:ℝ) ∧ (n:ℝ) < X (k+1)}) := by
  sorry

/-- LEAF. P0098 corollary to Theorem 3, page 163.
The exceptional count of the glued set P eventually respects the epsilon bounds,
proving the limit of exceptions is zero. -/
theorem corollary_exceptions (ε : ℕ → ℝ) (hε_lim : Tendsto ε atTop (nhds 0))
    (X : ℕ → ℝ) (P_seq : ℕ → Set ℕ) (P : Set ℕ)
    (hX_lim : Tendsto X atTop atTop)
    (h_glue : ∀ k, ∀ᶠ x : ℝ in atTop, P ∩ {n : ℕ | X k ≤ (n:ℝ) ∧ (n:ℝ) < X (k+1)} =
                                  P_seq k ∩ {n : ℕ | X k ≤ (n:ℝ) ∧ (n:ℝ) < X (k+1)})
    (h_bad : ∀ k, ∀ᶠ x : ℝ in atTop, (badEven (P_seq k) x : ℝ) ≤ ε k * x) :
    Tendsto (fun x : ℝ => (badEven P x : ℝ) / x) atTop (nhds 0) := by
  sorry

/-- P0098 corollary to Theorem 3, page 163, assembled from GranvilleTheorem3.
CONDITIONAL ON GranvilleTheorem3 and the cited gluing lemmas. -/
theorem granville_thin_corollary_from_th3 (h_th3 : GranvilleTheorem3) : GranvilleThinCorollary := by
  intro g hg
  obtain ⟨ε, hε, hε_lim⟩ := epsilon_sequence
  obtain ⟨X, P_seq, hX, hX_lim, hP_prime, hP_count, hP_bad⟩ :=
    corollary_extraction g hg ε hε hε_lim h_th3
  obtain ⟨P, hP, hP_g, h_glue⟩ := corollary_gluing g hg X P_seq hX hX_lim hP_prime hP_count
  refine ⟨P, hP, hP_g, ?_⟩
  exact corollary_exceptions ε hε_lim X P_seq P hX_lim h_glue hP_bad

/-- P0098 corollary to Theorem 3, page 163, fully assembled.
CONDITIONAL ON rich_density, thin_rich_approximation and gluing lemmas. -/
theorem granville_thin_corollary_assembled : GranvilleThinCorollary :=
  granville_thin_corollary_from_th3 granville_theorem3_assembled

end LeanLab.GoldbachAverage.DecompJ202
