/-
Independent split of the coefficient energy step of the periodic kernel reduction.
The two polynomial energies are turned into one power of the long interval length
through orthogonality of the additive characters on one complete period and a
divisor moment on each of the two polynomial supports.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561e

namespace LeanLab.BHP1997.Decomp561e
open Classical Complex Thm2 MeasureTheory Set Decomp561d

/-- LEAF. Orthogonality on one complete period for the long block: the integral of
the squared norm of the long polynomial over the period is the sum of the squared
coefficient norms over the long support, with no analytic input. -/
theorem leaf_long_energy_parseval561 (ε x : ℝ) (a : ℕ → ℂ) :
    longEnergy561 ε x a =
      ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a k‖ ^ 2 := by
  sorry

/-- LEAF. Orthogonality on one complete period for the short block: the integral of
the squared norm of the short polynomial over the period is the sum of the squared
coefficient norms over the short support, with no analytic input. -/
theorem leaf_short_energy_parseval561 (ε x : ℝ) (b : ℕ → ℂ) :
    shortEnergy561 ε x b =
      ∑ k ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b k‖ ^ 2 := by
  sorry

/-- LEAF. Divisor moment on the window of length twice Y placed directly below x:
the squared coefficient type bound raised to the exponent B, summed over that
window, is at most a constant times Y times one fixed power of the logarithm of x.
This is the only arithmetic input of the split; Y at least one keeps the window
inside the positive integers. -/
theorem leaf_divisor_window_sum561 (B : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |B| + 4) := by
  sorry

/-- LEAF. Divisor moment on the initial segment: the short support, which runs from
Y to twice Y, carries at most a constant times Y times the same fixed power of the
logarithm of x. -/
theorem leaf_divisor_initial_sum561 (B : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ Y x : ℝ, 1 ≤ Y → 2 * Y ≤ x →
      ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 ≤
        K * Y * Real.log x ^ (2 * |B| + 4) := by
  sorry

/-- LEAF. Choice of the exponent cutoff together with the size threshold: below the
cutoff the long interval length is at least one and at most half of x. This is the
elementary step that produces the positive epsilon zero of the target. -/
theorem leaf_length_bounds561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      1 ≤ length512 ε x ∧ 2 * length512 ε x ≤ x := by
  sorry

/-- The coefficient energy step, assembled from the two orthogonality identities,
the two divisor moments and the choice of the exponent cutoff. -/
theorem leaf_coefficient_energies561_split :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ a b : ℝ → ℕ → ℂ,
        (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
          ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
        ∃ M C : ℝ, 0 ≤ M ∧ 1 ≤ C ∧ ∀ x : ℝ, C ≤ x →
          longEnergy561 ε x (a x) ≤ C * length512 ε x * Real.log x ^ M ∧
          shortEnergy561 ε x (b x) ≤ C * length512 ε x * Real.log x ^ M := by
  intro B
  obtain ⟨K₁, hK₁, hwin⟩ := leaf_divisor_window_sum561 B
  obtain ⟨K₂, hK₂, hinit⟩ := leaf_divisor_initial_sum561 B
  obtain ⟨ε₀, hε₀, hlen⟩ := leaf_length_bounds561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε' a b hcoef
  obtain ⟨C₀, hC₀⟩ := hcoef
  obtain ⟨X, hX⟩ := hlen ε hε hε'
  refine ⟨2 * |B| + 4, max (max K₁ K₂ * |C₀| ^ 2) (max X 3), ?_, ?_, ?_⟩
  · positivity
  · have h1 : (1 : ℝ) ≤ 3 := by norm_num
    have h2 : (3 : ℝ) ≤ max X 3 := le_max_right X 3
    have h3 : max X 3 ≤ max (max K₁ K₂ * |C₀| ^ 2) (max X 3) := le_max_right _ _
    exact le_trans h1 (le_trans h2 h3)
  intro x hx
  have hstep : max X 3 ≤ max (max K₁ K₂ * |C₀| ^ 2) (max X 3) := le_max_right _ _
  have hXx : X ≤ x := le_trans (le_trans (le_max_left X 3) hstep) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_right X 3) hstep) hx
  obtain ⟨hY1, hY2⟩ := hX x hXx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hY0 : (0 : ℝ) ≤ length512 ε x := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogM : (0 : ℝ) ≤ Real.log x ^ (2 * |B| + 4) := Real.rpow_nonneg hlog0 _
  have hcK1 : K₁ ≤ max K₁ K₂ := le_max_left _ _
  have hcK2 : K₂ ≤ max K₁ K₂ := le_max_right _ _
  have hKC : max K₁ K₂ * |C₀| ^ 2 ≤ max (max K₁ K₂ * |C₀| ^ 2) (max X 3) :=
    le_max_left _ _
  have hfac : ∀ k : ℕ, C₀ * (((k.divisors.card : ℕ) : ℝ) ^ B) ≤
      |C₀| * (((k.divisors.card : ℕ) : ℝ) ^ B) := fun k =>
    mul_le_mul_of_nonneg_right (le_abs_self C₀) (Real.rpow_nonneg (Nat.cast_nonneg _) B)
  have hterm : ∀ k : ℕ, ‖a x k‖ ^ 2 ≤ (|C₀| * (((k.divisors.card : ℕ) : ℝ) ^ B)) ^ 2 := by
    intro k
    exact pow_le_pow_left₀ (norm_nonneg (a x k)) (le_trans (hC₀ x k).1 (hfac k)) 2
  have hterm' : ∀ k : ℕ, ‖b x k‖ ^ 2 ≤ (|C₀| * (((k.divisors.card : ℕ) : ℝ) ^ B)) ^ 2 := by
    intro k
    exact pow_le_pow_left₀ (norm_nonneg (b x k)) (le_trans (hC₀ x k).2 (hfac k)) 2
  constructor
  · calc longEnergy561 ε x (a x)
        = ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊, ‖a x k‖ ^ 2 :=
          leaf_long_energy_parseval561 ε x (a x)
      _ ≤ ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
            (|C₀| * (((k.divisors.card : ℕ) : ℝ) ^ B)) ^ 2 :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = |C₀| ^ 2 * ∑ k ∈ Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊,
            (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ |C₀| ^ 2 * (K₁ * length512 ε x * Real.log x ^ (2 * |B| + 4)) :=
          mul_le_mul_of_nonneg_left (hwin (length512 ε x) x hY1 hY2) (sq_nonneg _)
      _ = (K₁ * |C₀| ^ 2) * length512 ε x * Real.log x ^ (2 * |B| + 4) := by ring
      _ ≤ (max K₁ K₂ * |C₀| ^ 2) * length512 ε x * Real.log x ^ (2 * |B| + 4) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcK1 (sq_nonneg _)) hY0) hlogM
      _ ≤ (max (max K₁ K₂ * |C₀| ^ 2) (max X 3)) * length512 ε x *
            Real.log x ^ (2 * |B| + 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hY0) hlogM
  · calc shortEnergy561 ε x (b x)
        = ∑ k ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x k‖ ^ 2 :=
          leaf_short_energy_parseval561 ε x (b x)
      _ ≤ ∑ k ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            (|C₀| * (((k.divisors.card : ℕ) : ℝ) ^ B)) ^ 2 :=
          Finset.sum_le_sum (fun k _ => hterm' k)
      _ = |C₀| ^ 2 * ∑ k ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊,
            (((k.divisors.card : ℕ) : ℝ) ^ B) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ |C₀| ^ 2 * (K₂ * length512 ε x * Real.log x ^ (2 * |B| + 4)) :=
          mul_le_mul_of_nonneg_left (hinit (length512 ε x) x hY1 hY2) (sq_nonneg _)
      _ = (K₂ * |C₀| ^ 2) * length512 ε x * Real.log x ^ (2 * |B| + 4) := by ring
      _ ≤ (max K₁ K₂ * |C₀| ^ 2) * length512 ε x * Real.log x ^ (2 * |B| + 4) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcK2 (sq_nonneg _)) hY0) hlogM
      _ ≤ (max (max K₁ K₂ * |C₀| ^ 2) (max X 3)) * length512 ε x *
            Real.log x ^ (2 * |B| + 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hY0) hlogM

end LeanLab.BHP1997.Decomp561e
