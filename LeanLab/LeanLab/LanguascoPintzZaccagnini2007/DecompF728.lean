import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
Decomposition of `leaf_singular_series_coefficients481` from `SPLIT_pintz_explicit_formula481`.
Four elementary leaves have proofs. The sealed smallness leaf is false for arbitrary families.
Its off-pole vanishing hypothesis leaves the pole coefficient unrestricted.
`DecompF728False` proves its negation. `SingSerSettle1122` refutes the parent statement.

The separate support below isolates the remaining pole bound and supplies the modulus-one case.
The artificial zero-off-pole construction does not supply the explicit formula remainder.
Every existing statement and proof is preserved.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. The singular series is nonnegative on the relevant even integers. -/
theorem LEAF_Sing_nonneg_on_evenJ131 (X : ℕ) (n : ℕ) (hn : n ∈ evenJ131 X) :
    0 ≤ Sing n := by
  rw [Sing]
  refine tprod_nonneg (fun p => ?_)
  have h2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  by_cases hp : p.1 ∣ n
  · rw [if_pos hp]
    exact div_nonneg (by linarith) (by linarith)
  · rw [if_neg hp]
    have h1 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by linarith
    have hsq : (1 : ℝ) ≤ ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((p.1 : ℝ) - 1) ^ 2 := by linarith
    have hle : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact hsq
    linarith

/-- LEAF. The supplied pole-pair equality implies itself. -/
theorem LEAF_Sg_pole_pair_condition (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) :
    (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) →
    (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) := by norm_num

/-- LEAF. The trivial `Sg` (zero off the pole pair) satisfies the uniform bound `‖Sg i j n‖ ≤ S(n)`
because `S(n) ≥ 0` and `‖0‖ = 0`. -/
theorem LEAF_Sg_uniform_bound (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSg : ∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ))
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0) :
    (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) := by
  intro i j n hn
  by_cases hij : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij
    rw [hSg n hn, Complex.norm_real,
      Real.norm_of_nonneg (LEAF_Sing_nonneg_on_evenJ131 X n hn)]
  · have hz : Sg i j n = 0 := hSgZero i j n (not_and_or.mp hij)
    rw [hz, norm_zero]
    exact LEAF_Sing_nonneg_on_evenJ131 X n hn

/-- LEAF. FALSE as written. No modulus-one condition is imposed at index zero.
The off-pole vanishing hypothesis gives no bound on the pole coefficient.
`DecompF728False` and the separate counterexample below record this lab quantifier defect. -/
theorem LEAF_Sg_smallness (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (Cε : ℝ → ℕ) (hC : ∀ ε, 0 < Cε ε) :
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
      (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by sorry

/-- LEAF. The trivial `Sg` can be explicitly constructed for any zero family `z`. -/
theorem LEAF_Sg_exists (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ) :
    ∃ (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
      (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
      (∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0) := by
  refine ⟨fun i j n => if i = 0 ∧ j = 0 then (Sing n : ℂ) else 0, ?_, ?_⟩
  · intro n _
    simp
  · intro i j n hij
    by_cases h : i = 0 ∧ j = 0
    · rcases hij with hi | hj
      · exact absurd h.1 hi
      · exact absurd h.2 hj
    · simp [h]

/-- Assembly from the sealed leaves. Its use of the false smallness leaf leaves `sorryAx`
in its axiom report. It does not establish the coefficient claim. -/
theorem leaf_singular_series_coefficients481_F728 (ε₀ : ℝ) (hε₀ : 0 < ε₀) (Cε : ℝ → ℕ)
    (hC : ∀ ε, 0 < Cε ε) :
    ∀ (X K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      ∃ Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ,
        (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
        (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) ∧
        (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
          (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  intro X K z
  obtain ⟨Sg, hSg00, hSgZero⟩ := LEAF_Sg_exists X K z
  refine' ⟨Sg, hSg00, ?_, ?_⟩
  · -- Uniform bound: ‖Sg i j n‖ ≤ Sing n
    have h₁ : ∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n :=
      LEAF_Sg_uniform_bound X K z Sg hSg00 hSgZero
    exact h₁
  · -- Smallness condition
    have h₂ : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
        (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε :=
      LEAF_Sg_smallness X K z Sg hSgZero ε₀ hε₀ Cε hC
    exact h₂

/-- Derived support for P0045 page 5, Lemma 4.1.
For coefficients zero off the pole pair, smallness reduces exactly to the pole coefficient.
The sealed smallness leaf omits this remaining obligation. -/
theorem LEAF_Sg_smallness_iff_pole_bound644 (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0)
    (ε₀ : ℝ) (Cε : ℝ → ℕ) :
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
      (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) ↔
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ n ∈ evenJ131 X,
      ¬ (z 0).1 ∣ Cε ε * n → ‖Sg 0 0 n‖ ≤ ε) := by
  constructor
  · intro h ε hε hε₀ n hn hnd
    exact h ε hε hε₀ 0 0 n hn (Or.inl hnd)
  · intro h ε hε hε₀ i j n hn hnd
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      exact h ε hε hε₀ n hn (hnd.elim id id)
    · rw [hSgZero i j n (not_and_or.mp hij), norm_zero]
      exact hε.le

/-- Derived support for P0045 page 5, Lemma 4.1.
The primitive pole modulo one makes the pole-bound obligation vacuous.
The cutoff and multiplier are arbitrary. -/
theorem LEAF_Sg_smallness_of_pole_one644 (X K : ℕ)
    (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hz : (z 0).1 = 1)
    (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ)
    (hSgZero : ∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0)
    (ε₀ : ℝ) (Cε : ℝ → ℕ) :
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
      (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  apply (LEAF_Sg_smallness_iff_pole_bound644 X K z Sg hSgZero ε₀ Cε).2
  intro ε _ _ n _ hnd
  exact (hnd (by rw [hz]; exact one_dvd _)).elim

/-- Lab quantifier audit of the split of P0045 page 5, Lemma 4.1.
For every allowed cutoff and multiplier, a two-index family refutes smallness.
The vanishing hypothesis has actual off-pole cases in this example. -/
theorem LEAF_Sg_smallness_counterexample_two_indices644
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (Cε : ℝ → ℕ) (hC : ∀ ε, 0 < Cε ε) :
    ∃ (z : Fin 2 → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
      (Sg : Fin 2 → Fin 2 → ℕ → ℂ),
      (∀ i j n, (i ≠ 0 ∨ j ≠ 0) → Sg i j n = 0) ∧
      ¬ (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 2 →
        (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) := by
  refine ⟨fun _ => ⟨Cε (ε₀ / 2) * 2 + 1, (1, 0)⟩,
    fun i j _ => if i = 0 ∧ j = 0 then (ε₀ : ℂ) else 0, ?_, ?_⟩
  · intro i j n hij
    have h : ¬ (i = 0 ∧ j = 0) := by
      intro h
      exact hij.elim (fun hi => hi h.1) (fun hj => hj h.2)
    simp [h]
  · intro h
    have hn : (2 : ℕ) ∈ evenJ131 2 := by
      unfold evenJ131
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by norm_num, le_rfl⟩, by decide, by norm_num⟩
    have hM : 0 < Cε (ε₀ / 2) * 2 := Nat.mul_pos (hC _) (by decide)
    have hnd : ¬ (Cε (ε₀ / 2) * 2 + 1) ∣ Cε (ε₀ / 2) * 2 :=
      Nat.not_dvd_of_pos_of_lt hM (Nat.lt_succ_self _)
    have key := h (ε₀ / 2) (by linarith) (by linarith) 0 0 2 hn (Or.inl hnd)
    have hk : ε₀ ≤ ε₀ / 2 := by
      simpa [Complex.norm_real, Real.norm_of_nonneg hε₀.le] using key
    linarith

end
end LeanLab.LPZ2007