import LeanLab.ChenDoubleSieve.Lemma42Uk

/-!
# The elementary power saving substitution in Wu 2004 Section 4

Source: https://arxiv.org/pdf/0705.1652, pages 9, 15 and 17, Lemmas 4.1 and 4.2.
This completes the power substitution described in the existing tuple remainder bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Wu04Remainder

/-- N divided by N to eta is exactly N to one minus eta. -/
theorem div_rpow (N η : ℝ) (hN : 0 < N) : N / N ^ η = N ^ (1 - η) := by
  rw [Real.rpow_sub hN, Real.rpow_one]

/-- Bound the tuple remainder by the sum of two powers. -/
theorem remainder_two_powers {N W δ η P : ℝ} {i k : ℕ}
    (hN : 1 ≤ N) (hW : N ^ η ≤ W) (hδ : 0 ≤ δ) (hi : i ≤ k)
    (hP : 0 ≤ P) (hPQ : P ≤ N ^ (1 / 2 - δ)) :
    (i : ℝ) * (N / W + 2 ^ i * P) ≤
      k * (N ^ (1 - η) + 2 ^ k * N ^ (1 / 2 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := (Real.rpow_pos_of_pos hN0 _).trans_le hW
  have hfirst : N / W ≤ N ^ (1 - η) := by
    rw [← div_rpow N η hN0]
    exact div_le_div_of_nonneg_left hN0.le (Real.rpow_pos_of_pos hN0 _) hW
  have hhalf : P ≤ N ^ (1 / 2 : ℝ) := hPQ.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have htwo : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
  have hsecond : (2 : ℝ) ^ i * P ≤ 2 ^ k * N ^ (1 / 2 : ℝ) :=
    mul_le_mul htwo hhalf hP (by positivity)
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  exact mul_le_mul hik (add_le_add hfirst hsecond) (by positivity) (by positivity)

/-- One positive power saving absorbs both terms in the remainder. -/
theorem remainder_power_saving {N W δ η P : ℝ} {i k : ℕ}
    (hN : 1 ≤ N) (hW : N ^ η ≤ W) (hδ : 0 ≤ δ) (hi : i ≤ k)
    (hP : 0 ≤ P) (hPQ : P ≤ N ^ (1 / 2 - δ)) (hη : η ≤ 1 / 2) :
    (i : ℝ) * (N / W + 2 ^ i * P) ≤
      k * (1 + 2 ^ k) * N ^ (1 - η) := by
  have ht := remainder_two_powers hN hW hδ hi hP hPQ
  have hp : N ^ (1 / 2 : ℝ) ≤ N ^ (1 - η) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc _ ≤ (k : ℝ) * (N ^ (1 - η) + 2 ^ k * N ^ (1 / 2 : ℝ)) := ht
    _ ≤ (k : ℝ) * (N ^ (1 - η) + 2 ^ k * N ^ (1 - η)) := by gcongr
    _ = _ := by ring

/-- Wu's exponent eta is positive and at most one tenth. -/
theorem eta_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    0 < δ ^ (k + 1) / 10 ∧ δ ^ (k + 1) / 10 ≤ 1 / 10 := by
  have hp : δ ^ (k + 1) ≤ 1 := pow_le_one₀ hδ0.le hδ1
  constructor
  · positivity
  · linarith

/-- Nonempty concrete parameters for the power saving estimate. -/
theorem remainder_instance :
    (1 : ℝ) * (16 / 2 + 2 ^ (1 : ℕ) * 1) ≤
      (1 : ℝ) * (1 + 2 ^ (1 : ℕ)) * 16 ^ (1 - (1 / 4 : ℝ)) := by
  simpa only [Nat.cast_one] using
    (remainder_power_saving (N := 16) (W := 2) (δ := 1 / 4)
      (η := 1 / 4) (P := 1) (i := 1) (k := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Real.one_le_rpow (by norm_num) (by norm_num)) (by norm_num))

end LeanLab.ChenDoubleSieve.Wu04Remainder

#print axioms LeanLab.ChenDoubleSieve.Wu04Remainder.div_rpow
#print axioms LeanLab.ChenDoubleSieve.Wu04Remainder.remainder_two_powers
#print axioms LeanLab.ChenDoubleSieve.Wu04Remainder.remainder_power_saving
#print axioms LeanLab.ChenDoubleSieve.Wu04Remainder.eta_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Remainder.remainder_instance
