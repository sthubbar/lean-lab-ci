import LeanLab.Zhan1991.Fourier110

/-!
Decomposition of minor_reduction110.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open MeasureTheory

/-- The minor arcs, defined as the complement of major arcs in the unit interval. -/
def minorArcs110 (N : ℕ) (U d : ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ majorArcs110 N U d

/-- The real part of the minor arc integral. -/
def minorTerm110 (N : ℕ) (U d : ℝ) : ℝ :=
  (∫ α in minorArcs110 N U d,
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re

/-- LEAF. Page 269, display 3.20. Supremum bound of the exponential sum on the minor arcs.
The analytic evaluation requires Zhan Theorems 2 and 3 and the zero density theorem. -/
theorem minor_sup110 (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ, 0 ≤ K ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
      ∀ α ∈ minorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d,
        ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α‖
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) * Real.log N ^ (-4 : ℝ) := by
  sorry

/-- LEAF. Page 270, L2 integral. Parseval identity for the prime window sum.
The integral of the norm squared equals the cardinality of the window primes. -/
theorem primeSum_L2_110 (N : ℕ) (U : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) = (Win N U).card := by
  sorry

/-- LEAF. Page 269, window card bound. The cardinality of the prime window is bounded by its length. -/
theorem win_card110 (N : ℕ) (U : ℝ) :
    ((Win N U).card : ℝ) ≤ 3 * U := by
  sorry

/-- LEAF. The integral of minor arcs is bounded by sup times L2. -/
theorem minor_integral_bound110 (N : ℕ) (U d : ℝ) (K : ℝ)
    (h_sup : ∀ α ∈ minorArcs110 N U d, ‖primeSum110 N U α‖ ≤ K * U * Real.log N ^ (-4 : ℝ)) :
    |minorTerm110 N U d| ≤
      (K * U * Real.log N ^ (-4 : ℝ)) *
      (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := by
  sorry

/-- LEAF. Integration identity: The triple count minus the major term equals the minor term. -/
theorem minor_integral_identity110 (N : ℕ) (U d : ℝ) :
    |(T N U : ℝ) - majorTerm110 N U d| ≤ |minorTerm110 N U d| := by
  sorry

/-- The assembly for minor_reduction110 using the leaves.
Pages 269 and 270, displays 3.20 and 3.21. -/
theorem minor_reduction110_assembly (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ d c : ℝ, d₀ ≤ d ∧ 0 < c ∧ ∃ K N₀ : ℝ,
      ∀ N : ℕ, Odd N → N₀ ≤ N →
        |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
          - majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  obtain ⟨d, c, hd, hc, K, N₀, H_nonneg, H_sup⟩ := minor_sup110 d₀ hd₀
  refine ⟨d, c, hd, hc, 3 * K, max N₀ (Real.exp (1 : ℝ)), ?_⟩
  intro N hN hN₀
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c
  have h_id := minor_integral_identity110 N U d
  have h_sup_bound := H_sup N hN ((le_max_left _ _).trans hN₀)
  have h_bound := minor_integral_bound110 N U d K h_sup_bound
  have h_l2 := primeSum_L2_110 N U
  have h_card := win_card110 N U

  have H1 : |minorTerm110 N U d| ≤ (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ) := by
    calc
      |minorTerm110 N U d| ≤ (K * U * Real.log N ^ (-4 : ℝ)) * (∫ α in (0 : ℝ)..1, ‖primeSum110 N U α‖ ^ 2) := h_bound
      _ = (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ) := by rw [h_l2]

  have Hpos_prod : (0 : ℝ) ≤ K * U * Real.log N ^ (-4 : ℝ) := by
    have h1 : Real.exp (1 : ℝ) ≤ (N : ℝ) := (le_max_right _ _).trans hN₀
    have H1lt : (1 : ℝ) ≤ (N : ℝ) := (Real.one_le_exp (by positivity)).trans h1
    have h2 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg H1lt
    have h_u_pos : (0 : ℝ) ≤ U := by
      have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      exact mul_nonneg (Real.rpow_nonneg hNpos _) (Real.rpow_nonneg h2 _)
    exact mul_nonneg (mul_nonneg H_nonneg h_u_pos) (Real.rpow_nonneg h2 _)

  have H3 : (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ) ≤ (K * U * Real.log N ^ (-4 : ℝ)) * (3 * U) := by
    calc
      (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ)
        = ((Win N U).card : ℝ) * (K * U * Real.log N ^ (-4 : ℝ)) := mul_comm _ _
      _ ≤ (3 * U) * (K * U * Real.log N ^ (-4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right h_card Hpos_prod
      _ = (K * U * Real.log N ^ (-4 : ℝ)) * (3 * U) := mul_comm _ _

  calc
    |(T N U : ℝ) - majorTerm110 N U d| ≤ |minorTerm110 N U d| := h_id
    _ ≤ (K * U * Real.log N ^ (-4 : ℝ)) * ((Win N U).card : ℝ) := H1
    _ ≤ (K * U * Real.log N ^ (-4 : ℝ)) * (3 * U) := H3
    _ = (3 * K) * U ^ 2 * Real.log N ^ (-4 : ℝ) := by ring

end
end LeanLab.Zhan1991
