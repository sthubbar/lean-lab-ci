/-
P0076 Theorem 1.4, Section 11, pages 44 to 45.
Elementary reductions from prime approximations at unbounded doubling scales.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Definitions

open scoped Classical

namespace LeanLab.Teravainen2016

/-- Distance to the nearest integer is even, including half integer ties. -/
theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  apply le_antisymm
  · calc
      _ ≤ |-x - (-round x : ℤ)| := round_le (-x) (-round x)
      _ = distInt x := by
        unfold distInt
        push_cast
        rw [show -x - -(round x : ℝ) = -(x - round x) by ring, abs_neg]
  · calc
      _ ≤ |x - (-round (-x) : ℤ)| := round_le x (-round (-x))
      _ = distInt (-x) := by
        unfold distInt
        push_cast
        rw [show x - -(round (-x) : ℝ) = -(-x - round (-x)) by ring, abs_neg]

/-- The factor one half absorbs the change from scale N to a prime at most 2N. -/
theorem dyadic_rpow_lower {N p θ : ℝ} (hN : 0 < N) (hp : 0 < p)
    (hpN : p ≤ 2 * N) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    N ^ (-θ) / 2 ≤ p ^ (-θ) := by
  calc
    _ = N ^ (-θ) * (2 : ℝ) ^ (-1 : ℝ) := by norm_num; ring
    _ ≤ N ^ (-θ) * (2 : ℝ) ^ (-θ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 * N) ^ (-θ) := by rw [Real.mul_rpow (by norm_num) hN.le]; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hp hpN (by linarith)

/-- Approximations at unbounded doubling scales yield infinitely many approximating primes. -/
theorem approximation_infinite_of_dyadic {ξ κ θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
      InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2) :
    {p : ℕ | InP p ∧ distInt (ξ * p + κ) ≤ (p : ℝ) ^ (-θ)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro X
  obtain ⟨N, p, hN, hNp, hpN, hp, hd⟩ := h (X + 1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  refine ⟨p, ⟨hp, hd.trans (dyadic_rpow_lower hN0 hp0 ?_ hθ0 hθ1)⟩, by omega⟩
  exact_mod_cast hpN

/-- Increasing epsilon weakens the approximation bound for primes. -/
theorem approximation_epsilon_mono {ξ κ ε δ : ℝ} (hδε : δ ≤ ε)
    (h : {p : ℕ | InP p ∧
      distInt (ξ * p + κ) ≤ (p : ℝ) ^ (-(1 / 80 - δ))}.Infinite) :
    {p : ℕ | InP p ∧
      distInt (ξ * p + κ) ≤ (p : ℝ) ^ (-(1 / 80 - ε))}.Infinite := by
  apply h.mono
  intro p hp
  exact ⟨hp.1, hp.2.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hp.1.1.one_le) (by linarith))⟩

/-- Positive irrational frequencies suffice because nearest integer distance is even. -/
theorem theorem14_of_positive_frequency
    (h : ∀ ξ : ℝ, Irrational ξ → 0 < ξ → ∀ κ ε : ℝ, 0 < ε →
      {p : ℕ | InP p ∧ distInt (ξ * p + κ) ≤
        (p : ℝ) ^ (-(1 / 80 - ε))}.Infinite) : Theorem14 := by
  intro ξ hξ κ ε hε
  rcases lt_trichotomy ξ 0 with hneg | hzero | hpos
  · have hi := h (-ξ) hξ.neg (by linarith) (-κ) ε hε
    apply hi.mono
    intro p hp
    refine ⟨hp.1, ?_⟩
    simpa only [show -ξ * (p : ℝ) + -κ = -(ξ * p + κ) by ring, distInt_neg] using hp.2
  · exact (hξ.ne_zero hzero).elim
  · exact h ξ hξ hpos κ ε hε

/-- The Section 11 dyadic input implies the full epsilon and sign formulation. -/
theorem theorem14_of_dyadic_input
    (h : ∀ ξ : ℝ, Irrational ξ → 0 < ξ → ∀ κ θ : ℝ, 0 < θ → θ < 1 / 80 →
      ∀ X : ℕ, ∃ N p : ℕ, max 1 X ≤ N ∧ N ≤ p ∧ p ≤ 2 * N ∧
        InP p ∧ distInt (ξ * p + κ) ≤ (N : ℝ) ^ (-θ) / 2) : Theorem14 := by
  apply theorem14_of_positive_frequency
  intro ξ hξ hξ0 κ ε hε
  let δ := min (ε / 2) (1 / 160)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / 160 := min_le_right _ _
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  apply approximation_epsilon_mono hδε
  apply approximation_infinite_of_dyadic (by linarith : 0 ≤ 1 / 80 - δ)
    (by linarith : 1 / 80 - δ ≤ 1)
  exact h ξ hξ hξ0 κ (1 / 80 - δ) (by linarith) (by linarith)

example : distInt (-(1 / 2 : ℝ)) = distInt (1 / 2 : ℝ) := distInt_neg _
example : (10 : ℝ) ^ (-(1 / 160 : ℝ)) / 2 ≤ (17 : ℝ) ^ (-(1 / 160 : ℝ)) :=
  dyadic_rpow_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms theorem14_of_dyadic_input
#print axioms distInt_neg
#print axioms dyadic_rpow_lower
#print axioms approximation_infinite_of_dyadic
#print axioms approximation_epsilon_mono
#print axioms theorem14_of_positive_frequency

end LeanLab.Teravainen2016
