/-
P0093 pages 162 and 163. Separate weighted alignment from dyadic recurrence.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Phase435
import LeanLab.Linnik1951.Alignment435

namespace LeanLab.Linnik1951

open Finset

/-- LEAF. P0093 page 162 equations 7.8 and 7.9 through page 163
7.10. A nearly maximal weighted sum of unit phases forces almost all
phases close to one common rotation. The weights lie between exp of
negative one and one. This parameter version keeps only the weighted
cosine deficit argument. There is no dyadic recurrence, near integer
conclusion or measure estimate. -/
theorem weighted_phase_alignment435 (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∀ M : ℕ,
      ∀ w θ : ℕ → ℝ,
        (∀ m ∈ range M, Real.exp (-1) ≤ w m ∧ w m ≤ 1) →
        (1 - η) * (∑ m ∈ range M, w m) <
          ‖∑ m ∈ range M, (w m : ℂ) *
            Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)‖ →
        ∃ φ : ℝ, ∃ S : Finset ℕ, S ⊆ range M ∧
          (1 - ε) * (M : ℝ) ≤ S.card ∧
          ∀ m ∈ S, ∃ z : ℤ, |θ m - φ - z| ≤ ρ := by
  exact weighted_phase_alignment_proved435 ε ρ hε hρ

/-- P0093 page 163 equation 7.11. Exact finite_phase_concentration412
statement, assembled from weighted alignment and the proved adjacent
pair rotation removal. Both components now have clean proofs. -/
theorem finite_phase_concentration_decomposed435 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (r : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, α ∈ Set.Icc (-1) 2 →
        (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖ →
          (1 - ε) * (Nat.log 2 N : ℝ) ≤
            (nearIntegerIndices412 (Nat.log 2 N) r α).card := by
  obtain ⟨η, hη, hηhalf, ha⟩ :=
    weighted_phase_alignment435 (ε / 2) ((1 / 2 : ℝ) ^ r / 4) (by positivity) (by positivity)
  refine ⟨η, hη, hηhalf, 16, ?_⟩
  intro N hN α _ hlarge
  have h1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  let w : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let θ : ℕ → ℝ := fun m => α * (2 : ℝ) ^ (m + 1)
  have hw : ∀ m ∈ range (Nat.log 2 N), Real.exp (-1) ≤ w m ∧ w m ≤ 1 := by
    intro m hm
    have hp : 2 ^ (m + 1) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hm)).trans
        (Nat.pow_log_le_self 2 (by omega))
    constructor
    · apply Real.exp_le_exp.mpr
      have hdiv : (((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤ 1 :=
        (div_le_one hNp).mpr (by exact_mod_cast hp)
      rw [neg_div]
      linarith
    · apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hNp.le
  have hzero : ‖powerTrunc412 N 0‖ = ∑ m ∈ range (Nat.log 2 N), w m := by
    simp only [powerTrunc412, mul_zero, zero_mul, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le))
  have hpoly : (∑ m ∈ range (Nat.log 2 N), (w m : ℂ) *
      Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) = powerTrunc412 N α := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [w, θ]
    congr 2
    push_cast
    ring
  rw [hzero] at hlarge
  obtain ⟨φ, S, hS, hc, hp⟩ := ha (Nat.log 2 N) w θ hw (by rwa [hpoly])
  exact cluster_to_near_indices435 (Nat.log 2 N) r hM α φ ε hε hεhalf S hS hc hp

end LeanLab.Linnik1951
